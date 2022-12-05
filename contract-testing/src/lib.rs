use anyhow::anyhow;
use concordium_base::base::{Energy, ExchangeRate};
use concordium_contracts_common::*;
use sha2::{Digest, Sha256};
use std::{
    collections::{
        btree_map::Entry::{Occupied, Vacant},
        BTreeMap,
    },
    path::Path,
};
use wasm_chain_integration::{
    v0,
    v1::{self, ConcordiumAllowedImports, InvokeResponse, ReturnValue},
    ExecResult, InterpreterEnergy,
};
use wasm_transform::artifact;

pub struct Chain {
    /// The slot time viewable inside the smart contracts.
    /// An error is thrown if this is `None` and the contract tries to
    /// access it.
    slot_time:            Option<SlotTime>,
    /// MicroCCD per Energy.
    micro_ccd_per_energy: ExchangeRate,
    /// Accounts and info about them.
    accounts:             BTreeMap<AccountAddress, AccountInfo>,
    /// Smart contract modules.
    modules: BTreeMap<
        ModuleReference,
        artifact::Artifact<v1::ProcessedImports, artifact::CompiledFunction>,
    >,
    /// Smart contract instances.
    // TODO: Value should also hold module ref, name etc.
    contracts:            BTreeMap<ContractAddress, ContractInstance>,
    /// Next contract index to use when creating a new instance.
    next_contract_index:  u64,
}

pub struct ContractInstance {
    module_reference: ModuleReference,
    contract_name:    OwnedContractName,
    state:            v1::trie::PersistentState,
    owner:            AccountAddress,
    self_balance:     Amount,
}

impl Chain {
    pub fn new_with_time(slot_time: SlotTime, energy_per_micro_ccd: ExchangeRate) -> Self {
        Self {
            slot_time: Some(slot_time),
            ..Self::new(energy_per_micro_ccd)
        }
    }

    pub fn new(energy_per_micro_ccd: ExchangeRate) -> Self {
        Self {
            slot_time:            None,
            micro_ccd_per_energy: energy_per_micro_ccd,
            accounts:             BTreeMap::new(),
            modules:              BTreeMap::new(),
            contracts:            BTreeMap::new(),
            next_contract_index:  0,
        }
    }

    pub fn module_deploy<P: AsRef<Path>>(
        &mut self,
        sender: AccountAddress,
        module_path: P,
    ) -> Result<SuccessfulModuleDeployment, DeployModuleError> {
        // Load file
        let module = std::fs::read(module_path)?;

        // Deserialize as wasm module (artifact)
        let artifact = wasm_transform::utils::instantiate_with_metering::<v1::ProcessedImports, _>(
            &ConcordiumAllowedImports {
                support_upgrade: true,
            },
            &module[8..], // skip the 4 version bytes and 4 len bytes
        )
        .map_err(|e| DeployModuleError::InvalidModule(e.to_string()))?;

        // Calculate transaction fee of deployment
        let energy = Energy::from(module.len() as u64 / 10); // From: Concordium/Const/deployModuleCost.hs
        let transaction_fee = self.calculate_energy_cost(energy);

        // Try to subtract cost for account
        match self.accounts.entry(sender) {
            Vacant(_) => return Err(DeployModuleError::AccountDoesNotExist),
            Occupied(mut acc) => {
                let acc = acc.get_mut();
                if acc.balance < transaction_fee {
                    return Err(DeployModuleError::InsufficientFunds);
                }
                acc.balance -= transaction_fee;
            }
        }

        // Save the module
        let module_reference = {
            let mut hasher = Sha256::new();
            hasher.update(module);
            let hash: [u8; 32] = hasher.finalize().into();
            ModuleReference::from(hash)
        };
        self.modules.insert(module_reference, artifact);
        Ok(SuccessfulModuleDeployment {
            module_reference,
            energy,
            transaction_fee,
        })
    }

    pub fn contract_init(
        &mut self,
        sender: AccountAddress,
        module_reference: ModuleReference,
        contract_name: ContractName,
        parameter: ContractParameter,
        amount: Amount,
        energy_reserved: Energy,
    ) -> Result<SuccessfulContractInit, ContractInitError> {
        // Lookup artifact
        let artifact = self.get_artifact(module_reference)?;
        // Get the account and check that it has sufficient balance to pay for the
        // energy.
        let account_info = self.get_account(sender)?;
        if account_info.balance < self.calculate_energy_cost(energy_reserved) {
            return Err(ContractInitError::InsufficientFunds);
        }
        // Construct the context.
        let init_ctx = InitContextOpt {
            metadata:        ChainMetadataOpt {
                slot_time: self.slot_time,
            },
            init_origin:     sender,
            sender_policies: account_info.policies.clone(),
        };
        // Initialize contract
        let mut loader = v1::trie::Loader::new(&[][..]);
        let res = v1::invoke_init(
            artifact,
            init_ctx,
            v1::InitInvocation {
                amount,
                init_name: contract_name.get_chain_name(),
                parameter: &parameter.0,
                energy: InterpreterEnergy {
                    // TODO: Why do we have two separate energy types?
                    energy: energy_reserved.energy,
                },
            },
            false,
            loader,
        )
        .map_err(|e| ContractInitError::StringError(e.to_string()))?;
        // Charge account for cost
        let (res, transaction_fee) = match res {
            v1::InitResult::Success {
                logs,
                return_value: _, /* Ignore return value for now, since our tools do not support
                                  * it for inits, currently. */
                remaining_energy,
                mut state,
            } => {
                let contract_address = self.create_contract_address();
                let energy_used = Energy::from(energy_reserved.energy - remaining_energy);
                let transaction_fee = self.calculate_energy_cost(energy_used);

                let mut collector = v1::trie::SizeCollector::default();

                let contract_instance = ContractInstance {
                    module_reference,
                    contract_name: contract_name.to_owned(),
                    state: state.freeze(&mut loader, &mut collector), /* TODO: Do we need to
                                                                       * charge to storage? */
                    owner: sender,
                    self_balance: amount,
                };

                // Save the contract instance
                self.contracts.insert(contract_address, contract_instance);

                (
                    Ok(SuccessfulContractInit {
                        contract_address,
                        logs,
                        energy_used,
                        transaction_fee,
                    }),
                    transaction_fee,
                )
            }
            v1::InitResult::Reject {
                reason,
                return_value,
                remaining_energy,
            } => {
                let energy_used = Energy::from(energy_reserved.energy - remaining_energy);
                let transaction_fee = self.calculate_energy_cost(energy_used);
                (
                    Err(ContractInitError::ValidChainError(
                        FailedContractInteraction::Reject {
                            reason,
                            return_value,
                            energy_used,
                            transaction_fee,
                            logs: v0::Logs::default(), // TODO: Get Logs on failures.
                        },
                    )),
                    transaction_fee,
                )
            }
            v1::InitResult::Trap {
                error,
                remaining_energy,
            } => {
                let energy_used = Energy::from(energy_reserved.energy - remaining_energy);
                let transaction_fee = self.calculate_energy_cost(energy_used);
                (
                    Err(ContractInitError::ValidChainError(
                        FailedContractInteraction::Trap {
                            error,
                            energy_used,
                            transaction_fee,
                            logs: v0::Logs::default(), // TODO: Get Logs on failures.
                        },
                    )),
                    transaction_fee,
                )
            }
            v1::InitResult::OutOfEnergy => {
                let transaction_fee = self.calculate_energy_cost(energy_reserved);
                (
                    Err(ContractInitError::ValidChainError(
                        FailedContractInteraction::OutOFEnergy {
                            energy_used: energy_reserved,
                            transaction_fee,
                            logs: v0::Logs::default(), // TODO: Get Logs on failures.
                        },
                    )),
                    transaction_fee,
                )
            }
        };
        // Charge the account.
        // We have to get the account info again because of the borrow checker.
        self.get_account_mut(sender)?.balance -= transaction_fee;
        res
    }

    /// Can we get the return value here?
    pub fn contract_update(
        &mut self,
        invoker: AccountAddress, // TODO: Should we add a sender field and allow contract senders?
        address: ContractAddress,
        entrypoint: EntrypointName,
        parameter: ContractParameter,
        amount: Amount,
        energy_reserved: Energy,
    ) -> Result<SuccessfulContractUpdate, ContractUpdateError> {
        // Find contract instance and artifact
        let instance = self.get_instance(address)?;
        // TODO: Charge energy for module lookup.
        let artifact = self.get_artifact(instance.module_reference)?;

        // Ensure account exists and can pay for the reserved energy
        let account_info = self.get_account(invoker)?;
        if account_info.balance < self.calculate_energy_cost(energy_reserved) {
            return Err(ContractUpdateError::InsufficientFunds);
        }
        // Construct the context
        let receive_ctx = ReceiveContextOpt {
            metadata: ChainMetadataOpt {
                slot_time: self.slot_time,
            },
            invoker,
            self_address: address,
            self_balance: instance.self_balance + amount,
            sender: Address::Account(invoker),
            owner: instance.owner,
            sender_policies: account_info.policies.clone(),
            entrypoint: entrypoint.to_owned(),
        };
        let receive_name = OwnedReceiveName::new_unchecked(format!(
            "{}.{}",
            instance.contract_name.as_contract_name().contract_name(),
            entrypoint
        ));

        let mut loader = v1::trie::Loader::new(&[][..]);
        let mut mutable_state = instance.state.thaw();
        let inner = mutable_state.get_inner(&mut loader);
        let instance_state = v1::InstanceState::new(loader, inner);

        // Update the contract
        let res = v1::invoke_receive::<_, _, _, _, ReceiveContextOpt, ReceiveContextOpt>(
            std::sync::Arc::new(artifact.clone()), /* TODO: I made ProcessedImports cloneable
                                                    * for this to work. */
            receive_ctx,
            v1::ReceiveInvocation {
                amount,
                receive_name: receive_name.as_receive_name(),
                parameter: &parameter.0,
                energy: InterpreterEnergy {
                    energy: energy_reserved.energy,
                },
            },
            instance_state,
            v1::ReceiveParams {
                max_parameter_size:           65535,
                limit_logs_and_return_values: false,
                support_queries:              true,
            },
        )
        .map_err(|e| ContractUpdateError::StringError(e.to_string()))?;

        let (res, transaction_fee) = match res {
            v1::ReceiveResult::Success {
                logs,
                state_changed,
                return_value,
                remaining_energy,
            } => {
                let energy_used = Energy::from(energy_reserved.energy - remaining_energy);
                let transaction_fee = self.calculate_energy_cost(energy_used);
                if state_changed {
                    let instance = self.get_instance_mut(address)?;
                    let mut collector = v1::trie::SizeCollector::default();
                    instance.state = mutable_state.freeze(&mut loader, &mut collector);
                    // TODO: Do we need to charge for storage?
                }
                (
                    Ok(SuccessfulContractUpdate {
                        host_events: Vec::new(), // TODO: add host events
                        transfers: Vec::new(),   /* TODO: add transfers (or add fn to compute
                                                  * based on host events) */
                        energy_used,
                        transaction_fee,
                        return_value: ContractReturnValue(return_value),
                        state_changed,
                        logs,
                    }),
                    transaction_fee,
                )
            }
            v1::ReceiveResult::Interrupt {
                remaining_energy,
                state_changed,
                logs,
                config,
                interrupt,
            } => {
                if let v1::Interrupt::Transfer { to, amount } = interrupt {
                    let energy_used = Energy::from(energy_reserved.energy - remaining_energy);
                    let transaction_fee = self.calculate_energy_cost(energy_used);

                    let response = {
                        // Check if receiver account exists
                        if !self.accounts.contains_key(&to) {
                            InvokeResponse::Failure {
                                kind: v1::InvokeFailure::NonExistentAccount,
                            }
                        } else if self.get_instance(address)?.self_balance < amount {
                            InvokeResponse::Failure {
                                kind: v1::InvokeFailure::InsufficientAmount,
                            }
                        } else {
                            // Move the CCD
                            self.get_account_mut(to)?.balance += amount;
                            let instance = self.get_instance_mut(address)?;
                            instance.self_balance -= amount;

                            InvokeResponse::Success {
                                new_balance: instance.self_balance,
                                data:        None,
                            }
                        }
                    };

                    // Resume execution
                    let resume_res = v1::resume_receive(
                        config, // TODO: Need to change some things so it can use the ReceiveCtxOpt
                        response,
                        InterpreterEnergy::from(remaining_energy),
                        &mut mutable_state,
                        state_changed,
                        loader,
                    );
                    // TODO: Do we need to check energy here?
                } else {
                    todo!("Handle other interrupts")
                }
                todo!()
            }
            v1::ReceiveResult::Reject {
                reason,
                return_value,
                remaining_energy,
            } => {
                let energy_used = Energy::from(energy_reserved.energy - remaining_energy);
                let transaction_fee = self.calculate_energy_cost(energy_used);
                (
                    Err(ContractUpdateError::ValidChainError(
                        FailedContractInteraction::Reject {
                            reason,
                            return_value,
                            energy_used,
                            transaction_fee,
                            logs: v0::Logs::default(), // TODO: Get logs on failures.
                        },
                    )),
                    transaction_fee,
                )
            }
            v1::ReceiveResult::Trap {
                error,
                remaining_energy,
            } => {
                let energy_used = Energy::from(energy_reserved.energy - remaining_energy);
                let transaction_fee = self.calculate_energy_cost(energy_used);
                (
                    Err(ContractUpdateError::ValidChainError(
                        FailedContractInteraction::Trap {
                            error,
                            energy_used,
                            transaction_fee,
                            logs: v0::Logs::default(), // TODO: Get logs on failures.
                        },
                    )),
                    transaction_fee,
                )
            }
            v1::ReceiveResult::OutOfEnergy => {
                let transaction_fee = self.calculate_energy_cost(energy_reserved);
                (
                    Err(ContractUpdateError::ValidChainError(
                        FailedContractInteraction::OutOFEnergy {
                            energy_used: energy_reserved,
                            transaction_fee,
                            logs: v0::Logs::default(), // TODO: Get logs on failures.
                        },
                    )),
                    transaction_fee,
                )
            }
        };
        // Charge the transaction fee
        self.get_account_mut(invoker)?.balance -= transaction_fee;
        res
    }

    /// TODO: Should we make invoker and energy optional?
    pub fn contract_invoke(
        &mut self,
        invoker: AccountAddress,
        address: ContractAddress,
        entrypoint: EntrypointName,
        parameter: ContractParameter,
        amount: Amount,
        energy_reserved: Energy,
    ) -> Result<SuccessfulContractUpdate, ContractUpdateError> {
        // Find contract instance and artifact
        let instance = self.get_instance(address)?;
        let artifact = self.get_artifact(instance.module_reference)?;

        // Ensure account exists and can pay for the reserved energy
        let account_info = self.get_account(invoker)?;
        if account_info.balance < self.calculate_energy_cost(energy_reserved) {
            return Err(ContractUpdateError::InsufficientFunds);
        }
        // Construct the context
        let receive_ctx = ReceiveContextOpt {
            metadata: ChainMetadataOpt {
                slot_time: self.slot_time,
            },
            invoker,
            self_address: address,
            self_balance: instance.self_balance + amount,
            sender: Address::Account(invoker),
            owner: instance.owner,
            sender_policies: account_info.policies.clone(),
            entrypoint: entrypoint.to_owned(),
        };
        let receive_name = OwnedReceiveName::new_unchecked(format!(
            "{}.{}",
            instance.contract_name.as_contract_name().contract_name(),
            entrypoint
        ));

        let mut loader = v1::trie::Loader::new(&[][..]);
        let mut mutable_state = instance.state.thaw();
        let inner = mutable_state.get_inner(&mut loader);
        let instance_state = v1::InstanceState::new(loader, inner);

        // Update the contract
        let res = v1::invoke_receive::<_, _, _, _, ReceiveContextOpt, ReceiveContextOpt>(
            std::sync::Arc::new(artifact.clone()), /* TODO: I made ProcessedImports cloneable
                                                    * for this to work. */
            receive_ctx,
            v1::ReceiveInvocation {
                amount,
                receive_name: receive_name.as_receive_name(),
                parameter: &parameter.0,
                energy: InterpreterEnergy {
                    energy: energy_reserved.energy,
                },
            },
            instance_state,
            v1::ReceiveParams {
                max_parameter_size:           65535,
                limit_logs_and_return_values: false,
                support_queries:              true,
            },
        )
        .map_err(|e| ContractUpdateError::StringError(e.to_string()))?;

        match res {
            v1::ReceiveResult::Success {
                logs,
                state_changed,
                return_value,
                remaining_energy,
            } => {
                let energy_used = Energy::from(energy_reserved.energy - remaining_energy);
                let transaction_fee = self.calculate_energy_cost(energy_used);
                Ok(SuccessfulContractUpdate {
                    host_events: Vec::new(), // TODO: add host events
                    transfers: Vec::new(),   /* TODO: add transfers (or add fn to compute
                                              * based on host events) */
                    energy_used,
                    transaction_fee,
                    return_value: ContractReturnValue(return_value),
                    state_changed, // TODO: Should we always set this to false?
                    logs,
                })
            }
            v1::ReceiveResult::Interrupt { .. } => todo!("Handle interrupts"),
            v1::ReceiveResult::Reject {
                reason,
                return_value,
                remaining_energy,
            } => {
                let energy_used = Energy::from(energy_reserved.energy - remaining_energy);
                let transaction_fee = self.calculate_energy_cost(energy_used);
                Err(ContractUpdateError::ValidChainError(
                    FailedContractInteraction::Reject {
                        reason,
                        return_value,
                        energy_used,
                        transaction_fee,
                        logs: v0::Logs::default(), // TODO: Get logs on failures.
                    },
                ))
            }
            v1::ReceiveResult::Trap {
                error,
                remaining_energy,
            } => {
                let energy_used = Energy::from(energy_reserved.energy - remaining_energy);
                let transaction_fee = self.calculate_energy_cost(energy_used);
                Err(ContractUpdateError::ValidChainError(
                    FailedContractInteraction::Trap {
                        error,
                        energy_used,
                        transaction_fee,
                        logs: v0::Logs::default(), // TODO: Get logs on failures.
                    },
                ))
            }
            v1::ReceiveResult::OutOfEnergy => {
                let transaction_fee = self.calculate_energy_cost(energy_reserved);
                Err(ContractUpdateError::ValidChainError(
                    FailedContractInteraction::OutOFEnergy {
                        energy_used: energy_reserved,
                        transaction_fee,
                        logs: v0::Logs::default(), // TODO: Get logs on failures.
                    },
                ))
            }
        }
    }

    /// Create an account. Will override existing account if already present.
    pub fn create_account(&mut self, account: AccountAddress, account_info: AccountInfo) {
        self.accounts.insert(account, account_info);
    }

    /// Creates a contract address with an index one above the highest
    /// currently used. Next call to `contract_init` will skip this
    /// address.
    pub fn create_contract_address(&mut self) -> ContractAddress {
        let index = self.next_contract_index;
        let subindex = 0;
        self.next_contract_index += 1;
        ContractAddress::new(index, subindex)
    }

    pub fn set_slot_time(&mut self, slot_time: SlotTime) { self.slot_time = Some(slot_time); }

    pub fn set_energy_per_micro_ccd(&mut self, energy_per_micro_ccd: ExchangeRate) {
        self.micro_ccd_per_energy = energy_per_micro_ccd;
    }

    /// Returns the balance of an account if it exists.
    pub fn account_balance(&self, address: AccountAddress) -> Option<Amount> {
        self.accounts.get(&address).and_then(|ai| Some(ai.balance))
    }

    pub fn calculate_energy_cost(&self, energy: Energy) -> Amount {
        Amount::from_micro_ccd(
            energy.energy * self.micro_ccd_per_energy.numerator()
                / self.micro_ccd_per_energy.denominator(),
        )
    }

    fn get_artifact(
        &self,
        module_ref: ModuleReference,
    ) -> Result<&artifact::Artifact<v1::ProcessedImports, artifact::CompiledFunction>, ModuleMissing>
    {
        self.modules.get(&module_ref).ok_or(ModuleMissing)
    }

    fn get_instance(
        &self,
        address: ContractAddress,
    ) -> Result<&ContractInstance, ContractInstanceMissing> {
        self.contracts.get(&address).ok_or(ContractInstanceMissing)
    }

    fn get_instance_mut(
        &mut self,
        address: ContractAddress,
    ) -> Result<&mut ContractInstance, ContractInstanceMissing> {
        self.contracts
            .get_mut(&address)
            .ok_or(ContractInstanceMissing)
    }

    fn get_account(&self, address: AccountAddress) -> Result<&AccountInfo, AccountMissing> {
        self.accounts.get(&address).ok_or(AccountMissing)
    }

    fn get_account_mut(
        &mut self,
        address: AccountAddress,
    ) -> Result<&mut AccountInfo, AccountMissing> {
        self.accounts.get_mut(&address).ok_or(AccountMissing)
    }
}

#[derive(Debug)]
struct ModuleMissing;

impl From<ModuleMissing> for ContractInitError {
    fn from(_: ModuleMissing) -> Self { Self::ModuleDoesNotExist }
}

impl From<ModuleMissing> for ContractUpdateError {
    fn from(_: ModuleMissing) -> Self { Self::ModuleDoesNotExist }
}

#[derive(Debug)]
struct ContractInstanceMissing;

impl From<ContractInstanceMissing> for ContractUpdateError {
    fn from(_: ContractInstanceMissing) -> Self { Self::InstanceDoesNotExist }
}

#[derive(Debug)]
struct AccountMissing;

impl From<AccountMissing> for ContractInitError {
    fn from(_: AccountMissing) -> Self { Self::AccountDoesNotExist }
}

impl From<AccountMissing> for ContractUpdateError {
    fn from(_: AccountMissing) -> Self { Self::AccountDoesNotExist }
}

/// A chain metadata with an optional field.
/// Used when simulating contracts to allow the user to only specify the
/// necessary context fields.
/// The default value is `None` for all `Option` fields.
pub(crate) struct ChainMetadataOpt {
    slot_time: Option<SlotTime>,
}

impl v0::HasChainMetadata for ChainMetadataOpt {
    fn slot_time(&self) -> ExecResult<SlotTime> {
        unwrap_ctx_field(self.slot_time, "metadata.slotTime")
    }
}

/// An init context with optional fields.
/// Used when simulating contracts to allow the user to only specify the
/// context fields used by the contract.
/// The default value is `None` for all `Option` fields and the default of
/// `ChainMetadataOpt` for `metadata`.
pub(crate) struct InitContextOpt {
    metadata:        ChainMetadataOpt,
    init_origin:     AccountAddress,
    sender_policies: Option<v0::OwnedPolicyBytes>,
}

impl v0::HasInitContext for InitContextOpt {
    type MetadataType = ChainMetadataOpt;

    fn metadata(&self) -> &Self::MetadataType { &self.metadata }

    fn init_origin(&self) -> ExecResult<&AccountAddress> { Ok(&self.init_origin) }

    fn sender_policies(&self) -> ExecResult<&[u8]> {
        unwrap_ctx_field(
            self.sender_policies.as_ref().map(Vec::as_ref),
            "senderPolicies",
        )
    }
}

/// A receive context with optional fields.
/// Used when simulating contracts to allow the user to only specify the
/// context fields used by the contract.
/// The default value is `None` for all `Option` fields and the default of
/// `ChainMetadataOpt` for `metadata`.
pub(crate) struct ReceiveContextOpt {
    metadata:        ChainMetadataOpt,
    invoker:         AccountAddress,
    self_address:    ContractAddress,
    self_balance:    Amount,
    sender:          Address,
    owner:           AccountAddress,
    sender_policies: Option<v0::OwnedPolicyBytes>,
    /// The entrypoint name invoked. Only relevant for fallback receive
    /// functions.
    entrypoint:      OwnedEntrypointName,
}

impl v0::HasReceiveContext for ReceiveContextOpt {
    type MetadataType = ChainMetadataOpt;

    fn metadata(&self) -> &Self::MetadataType { &self.metadata }

    fn invoker(&self) -> ExecResult<&AccountAddress> { Ok(&self.invoker) }

    fn self_address(&self) -> ExecResult<&ContractAddress> { Ok(&self.self_address) }

    fn self_balance(&self) -> ExecResult<Amount> { Ok(self.self_balance) }

    fn sender(&self) -> ExecResult<&Address> { Ok(&self.sender) }

    fn owner(&self) -> ExecResult<&AccountAddress> { Ok(&self.owner) }

    fn sender_policies(&self) -> ExecResult<&[u8]> {
        unwrap_ctx_field(
            self.sender_policies.as_ref().map(Vec::as_ref),
            "senderPolicies",
        )
    }
}

impl v1::HasReceiveContext for ReceiveContextOpt {
    fn entrypoint(&self) -> ExecResult<EntrypointName> { Ok(self.entrypoint.as_entrypoint_name()) }
}

// Error handling when unwrapping.
fn unwrap_ctx_field<A>(opt: Option<A>, name: &str) -> ExecResult<A> {
    match opt {
        Some(v) => Ok(v),
        None => Err(anyhow!(
            "Missing field '{}' in the context. Make sure to provide all the fields that the \
             contract uses.",
            name,
        )),
    }
}

pub struct AccountInfo {
    /// The account balance. TODO: Do we need the three types of balances?
    pub balance: Amount,
    /// Optional test policies.
    policies:    Option<v0::OwnedPolicyBytes>,
}

impl AccountInfo {
    pub fn new(balance: Amount) -> Self {
        Self {
            balance,
            policies: None,
        }
    }
}

#[derive(Debug)]
pub enum ContractInitError {
    /// Initialization failed for a reason that also exists on the chain.
    ValidChainError(FailedContractInteraction),
    /// TODO: Can we get a better error than the anyhow?
    StringError(String),
    /// Module has not been deployed in test environment.
    ModuleDoesNotExist,
    /// Account has not been created in test environment.
    AccountDoesNotExist,
    /// The account does not have enough funds to pay for the energy.
    InsufficientFunds,
}

#[derive(Debug)]
pub enum ContractUpdateError {
    /// Update failed for a reason that also exists on the chain.
    ValidChainError(FailedContractInteraction),
    /// TODO: Can we get a better error than the anyhow?
    StringError(String),
    /// Module has not been deployed in test environment.
    ModuleDoesNotExist,
    /// Contract instance has not been initialized in test environment.
    InstanceDoesNotExist,
    /// Account has not been created in test environment.
    AccountDoesNotExist,
    /// The account does not have enough funds to pay for the energy.
    InsufficientFunds,
}

#[derive(Debug)]
pub enum FailedContractInteraction {
    Reject {
        reason:          i32,
        return_value:    ReturnValue,
        energy_used:     Energy,
        transaction_fee: Amount,
        /// Logs emitted before the interaction failed. Logs from failed
        /// updates are not stored on the chain, but can be useful for
        /// debugging.
        logs:            v0::Logs,
    },
    Trap {
        error:           anyhow::Error,
        energy_used:     Energy,
        transaction_fee: Amount,
        /// Logs emitted before the interaction failed. Logs from failed
        /// updates are not stored on the chain, but can be useful for
        /// debugging.
        logs:            v0::Logs,
    },
    OutOFEnergy {
        energy_used:     Energy,
        transaction_fee: Amount,
        /// Logs emitted before the interaction failed. Logs from failed
        /// updates are not stored on the chain, but can be useful for
        /// debugging.
        logs:            v0::Logs,
    },
}

impl FailedContractInteraction {
    pub fn transaction_fee(&self) -> Amount {
        match self {
            FailedContractInteraction::Reject {
                transaction_fee, ..
            } => *transaction_fee,
            FailedContractInteraction::Trap {
                transaction_fee, ..
            } => *transaction_fee,
            FailedContractInteraction::OutOFEnergy {
                transaction_fee, ..
            } => *transaction_fee,
        }
    }

    pub fn logs(&self) -> &v0::Logs {
        match self {
            FailedContractInteraction::Reject { logs, .. } => logs,
            FailedContractInteraction::Trap { logs, .. } => logs,
            FailedContractInteraction::OutOFEnergy { logs, .. } => logs,
        }
    }
}

#[derive(Debug)]
pub struct ContractError(Vec<u8>);

// TODO: Can we get Eq for this when using io::Error?
// TODO: Should this also have the energy used?
#[derive(Debug)]
pub enum DeployModuleError {
    ReadFileError(std::io::Error),
    InvalidModule(String),
    InsufficientFunds,
    AccountDoesNotExist,
}

impl From<std::io::Error> for DeployModuleError {
    fn from(e: std::io::Error) -> Self { DeployModuleError::ReadFileError(e) }
}

impl ContractError {
    pub fn deserial<T: Deserial>(&self) -> Result<T, ParsingError> { todo!() }
}

#[derive(Debug)]
pub enum ChainEvent {
    Interrupted {
        address: ContractAddress,
        logs:    v0::Logs,
    },
    Resumed {
        address: ContractAddress,
        success: bool,
    },
    Upgraded {
        address: ContractAddress,
        from:    ModuleReference,
        to:      ModuleReference,
    },
    Updated {
        address:    ContractAddress,
        contract:   OwnedContractName,
        entrypoing: OwnedEntrypointName,
        amount:     Amount,
    },
}

// TODO: Consider adding function to aggregate all logs from the host_events.
pub struct SuccessfulContractUpdate {
    /// Host events that occured. This includes interrupts, resumes, and
    /// upgrades.
    pub host_events:     Vec<ChainEvent>,
    pub transfers:       Vec<(AccountAddress, Amount)>,
    /// Energy used.
    pub energy_used:     Energy,
    /// Cost of transaction.
    pub transaction_fee: Amount,
    /// The returned value.
    pub return_value:    ContractReturnValue,
    /// Whether the state was changed.
    pub state_changed:   bool,
    /// The logs produced before?/after? the last interrupt if any.
    pub logs:            v0::Logs,
}

#[derive(Debug, PartialEq, Eq)]
pub struct SuccessfulModuleDeployment {
    pub module_reference: ModuleReference,
    pub energy:           Energy,
    /// Cost of transaction.
    pub transaction_fee:  Amount,
}

#[derive(Debug)]
pub struct SuccessfulContractInit {
    /// The address of the new instance.
    pub contract_address: ContractAddress,
    /// Logs produced during initialization.
    pub logs:             v0::Logs,
    /// Energy used.
    pub energy_used:      Energy,
    /// Cost of transaction.
    pub transaction_fee:  Amount,
}

pub struct ContractReturnValue(Vec<u8>);

#[derive(Debug, PartialEq, Eq)]
pub enum ParsingError {
    /// Thrown by `deserial` on failure.
    ParsingFailed,
}

impl ContractReturnValue {
    pub fn deserial<T: Deserial>(&self) -> Result<T, ParsingError> { todo!() }
}

pub struct ContractParameter(pub Vec<u8>);

impl ContractParameter {
    pub fn empty() -> Self { Self(Vec::new()) }

    pub fn from_bytes(bytes: Vec<u8>) -> Self { Self(bytes) }

    // TODO: add version with serde json
    pub fn from_typed<T: Serial>(parameter: &T) -> Self { Self(to_bytes(parameter)) }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ACC_0: AccountAddress = AccountAddress([0; 32]);
    const ACC_1: AccountAddress = AccountAddress([1; 32]);

    #[test]
    fn creating_accounts_work() {
        let mut chain = Chain::new(ExchangeRate::new_unchecked(2404, 1));
        chain.create_account(ACC_0, AccountInfo::new(Amount::from_ccd(1)));
        chain.create_account(ACC_1, AccountInfo::new(Amount::from_ccd(2)));

        assert_eq!(chain.accounts.len(), 2);
        assert_eq!(chain.account_balance(ACC_0), Some(Amount::from_ccd(1)));
        assert_eq!(chain.account_balance(ACC_1), Some(Amount::from_ccd(2)));
    }

    #[test]
    fn deploying_valid_module_works() {
        let mut chain = Chain::new(ExchangeRate::new_unchecked(2404, 1));
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res = chain
            .module_deploy(ACC_0, "icecream/icecream.wasm.v1") // TODO: Add wasm files to the repo for tests.
            .expect("Deploying valid module should work");

        assert_eq!(chain.modules.len(), 1);
        assert_eq!(
            chain.account_balance(ACC_0),
            Some(initial_balance - res.transaction_fee)
        );
    }

    #[test]
    fn initializing_valid_contract_works() {
        let mut chain = Chain::new(ExchangeRate::new_unchecked(2404, 1));
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy(ACC_0, "icecream/icecream.wasm.v1") // TODO: Add wasm files to the repo for tests.
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_weather"),
                ContractParameter::from_bytes(vec![0u8]),
                Amount::zero(),
                Energy::from(10000u64),
            )
            .expect("Initializing valid contract should work");
        assert_eq!(
            chain.account_balance(ACC_0),
            Some(initial_balance - res_deploy.transaction_fee - res_init.transaction_fee)
        );
        assert_eq!(chain.contracts.len(), 1);
    }

    #[test]
    fn initializing_with_invalid_parameter_fails() {
        let mut chain = Chain::new(ExchangeRate::new_unchecked(2404, 1));
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy(ACC_0, "icecream/icecream.wasm.v1") // TODO: Add wasm files to the repo for tests.
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_weather"),
                ContractParameter::from_bytes(vec![99u8]), // Invalid param
                Amount::zero(),
                Energy::from(10000u64),
            )
            .expect_err("Initializing with invalid params should fail");

        assert!(matches!(res_init, ContractInitError::ValidChainError(_)));
        match res_init {
            // Failed in the right way and account is still charged.
            ContractInitError::ValidChainError(FailedContractInteraction::Reject {
                transaction_fee,
                ..
            }) => assert_eq!(
                chain.account_balance(ACC_0),
                Some(initial_balance - res_deploy.transaction_fee - transaction_fee)
            ),
            _ => panic!("Expected valid chain error."),
        };
    }

    #[test]
    fn updating_valid_contract_works() {
        let mut chain = Chain::new(ExchangeRate::new_unchecked(2404, 1));
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy(ACC_0, "icecream/icecream.wasm.v1") // TODO: Add wasm files to the repo for tests.
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_weather"),
                ContractParameter::from_bytes(vec![0u8]), // Starts as 0
                Amount::zero(),
                Energy::from(10000u64),
            )
            .expect("Initializing valid contract should work");

        let res_update = chain
            .contract_update(
                ACC_0,
                res_init.contract_address,
                EntrypointName::new_unchecked("set"),
                ContractParameter::from_bytes(vec![1u8]), // Updated to 1
                Amount::zero(),
                Energy::from(10000u64),
            )
            .expect("Updating valid contract should work");

        let res_invoke_get = chain
            .contract_invoke(
                ACC_0,
                res_init.contract_address,
                EntrypointName::new_unchecked("get"),
                ContractParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Invoking get should work");

        // This also asserts that the account wasn't charged for the invoke.
        assert_eq!(
            chain.account_balance(ACC_0),
            Some(
                initial_balance
                    - res_deploy.transaction_fee
                    - res_init.transaction_fee
                    - res_update.transaction_fee
            )
        );
        assert_eq!(chain.contracts.len(), 1);
        assert!(res_update.state_changed);
        // Assert that the updated state is persisted.
        assert_eq!(res_invoke_get.return_value.0, [1u8]);
    }

    #[test]
    fn update_with_account_transfer_works() {
        let mut chain = Chain::new(ExchangeRate::new_unchecked(2404, 1));
        let initial_balance = Amount::from_ccd(10000);
        let transfer_amount = Amount::from_ccd(123);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));
        chain.create_account(ACC_1, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy(ACC_0, "integrate/a.wasm.v1") // TODO: Add wasm files to the repo for tests.
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_integrate"),
                ContractParameter::empty(),
                Amount::zero(),
                Energy::from(10000u64),
            )
            .expect("Initializing valid contract should work");

        let res_update = chain
            .contract_update(
                ACC_0,
                res_init.contract_address,
                EntrypointName::new_unchecked("receive"),
                ContractParameter::from_typed(&ACC_1),
                transfer_amount,
                Energy::from(10000u64),
            )
            .expect("Updating valid contract should work");

        let res_view = chain
            .contract_invoke(
                ACC_0,
                res_init.contract_address,
                EntrypointName::new_unchecked("view"),
                ContractParameter::empty(),
                Amount::zero(),
                Energy::from(10000u64),
            )
            .expect("Invoking get should work");

        // This also asserts that the account wasn't charged for the invoke.
        assert_eq!(
            chain.account_balance(ACC_0),
            Some(
                initial_balance
                    - res_deploy.transaction_fee
                    - res_init.transaction_fee
                    - res_update.transaction_fee
                    - transfer_amount
            )
        );
        assert_eq!(
            chain.account_balance(ACC_1),
            Some(initial_balance + transfer_amount)
        );
        assert_eq!(chain.contracts.len(), 1);
        assert!(res_update.state_changed);
        assert_eq!(res_update.return_value.0, [2u8]);
        // Assert that the updated state is persisted.
        assert_eq!(res_view.return_value.0, [2u8]);
    }
}
