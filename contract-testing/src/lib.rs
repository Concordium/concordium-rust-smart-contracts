use anyhow::bail;
use concordium_base::{
    base::{Energy, ExchangeRate},
    transactions::{self, cost},
};
use concordium_contracts_common::*;
use sha2::{Digest, Sha256};
use std::{
    collections::{
        btree_map::Entry::{Occupied, Vacant},
        BTreeMap,
    },
    path::Path,
};
use thiserror::Error;
use wasm_chain_integration::{
    v0,
    v1::{
        self,
        trie::{MutableState, SizeCollector},
        ConcordiumAllowedImports, InvokeResponse, ReturnValue,
    },
    ExecResult, InterpreterEnergy,
};
use wasm_transform::artifact;

/// A V1 artifact, with concrete types for the generic parameters.
type ArtifactV1 = artifact::Artifact<v1::ProcessedImports, artifact::CompiledFunction>;

// Energy constants from Cost.hs in concordium-base.
const QUERY_ACCOUNT_BALANCE_COST: u64 = 200;
const QUERY_CONTRACT_BALANCE_COST: u64 = 200;
const QUERY_EXCHANGE_RATE_COST: u64 = 100;

pub struct Chain {
    /// The slot time viewable inside the smart contracts.
    /// Defaults to `0`.
    slot_time:           SlotTime,
    /// MicroCCD per Euro ratio.
    micro_ccd_per_euro:  ExchangeRate,
    /// Euro per Energy ratio.
    euro_per_energy:     ExchangeRate,
    /// Accounts and info about them.
    accounts:            BTreeMap<AccountAddress, AccountInfo>,
    /// Smart contract modules.
    modules:             BTreeMap<ModuleReference, ArtifactV1>,
    /// Smart contract instances.
    contracts:           BTreeMap<ContractAddress, ContractInstance>,
    /// Next contract index to use when creating a new instance.
    next_contract_index: u64,
}

#[derive(Clone)]
pub struct ContractInstance {
    module_reference: ModuleReference,
    contract_name:    OwnedContractName,
    state:            v1::trie::PersistentState,
    owner:            AccountAddress,
    self_balance:     Amount,
}

impl Chain {
    pub fn new_with_time_and_rates(
        slot_time: SlotTime,
        micro_ccd_per_euro: ExchangeRate,
        euro_per_energy: ExchangeRate,
    ) -> Self {
        Self {
            slot_time,
            micro_ccd_per_euro,
            euro_per_energy,
            accounts: BTreeMap::new(),
            modules: BTreeMap::new(),
            contracts: BTreeMap::new(),
            next_contract_index: 0,
        }
    }

    pub fn new_with_time(slot_time: SlotTime) -> Self {
        Self {
            slot_time,
            ..Self::new()
        }
    }

    /// Create a new [`Self`] where
    ///  - `slot_time` defaults to `0`,
    ///  - `micro_ccd_per_euro` defaults to `16036807715944130560 /
    ///    108919627567`,
    ///  - `euro_per_energy` defaults to `1 / 50000`.
    pub fn new() -> Self {
        Self::new_with_time_and_rates(
            Timestamp::from_timestamp_millis(0),
            ExchangeRate::new_unchecked(147235241, 1),
            ExchangeRate::new_unchecked(1, 50000),
        )
    }

    /// Helper function that handles the actual logic of deploying the module
    /// bytes.
    ///
    /// Parameters:
    ///  - `sender`: the sender account.
    ///  - `module_bytes`: the module **without** the contract version and
    ///    module length bytes (8 bytes total).
    fn module_deploy_aux(
        &mut self,
        sender: AccountAddress,
        module: &[u8],
    ) -> Result<SuccessfulModuleDeployment, DeployModuleError> {
        // Deserialize as wasm module (artifact)
        let artifact = wasm_transform::utils::instantiate_with_metering::<v1::ProcessedImports, _>(
            &ConcordiumAllowedImports {
                support_upgrade: true,
            },
            &module,
        )
        .map_err(|e| DeployModuleError::InvalidModule(e.to_string()))?;

        // Calculate transaction fee of deployment
        // TODO: This is still slightly off.
        // For the fib module
        //   - This results in 18259 NRG
        //   - Concordium-client says 18262 NRG
        //   - The node charges for 18261 NRG
        let energy = {
            let payload_size =
                1 + module.len() as u64 + transactions::construct::TRANSACTION_HEADER_SIZE; // +1 for the tag
            let number_of_sigs = 1; // Accounts always have one signature here. TODO: Should we allow changing that?
            let base_cost = cost::base_cost(payload_size, number_of_sigs);
            let deploy_module_cost = cost::deploy_module(payload_size);
            let total = base_cost + deploy_module_cost;
            println!(
                "Deploying module \
                 cost:\n\tmodule_size:{}\n\tbase_cost:{}\n\tdeploy_module_cost:{}\n\ttotal:{}",
                payload_size, base_cost, deploy_module_cost, total
            );
            total
        };
        let transaction_fee = self.calculate_energy_cost(energy);
        println!(
            "Deploying module with size {}, resulting in {} NRG.",
            module.len(),
            energy
        );

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

    /// Deploy a raw wasm module, i.e. one **without** the prefix of 4 version
    /// bytes and 4 module length bytes.
    pub fn module_deploy_raw<P: AsRef<Path>>(
        &mut self,
        sender: AccountAddress,
        module_path: P,
    ) -> Result<SuccessfulModuleDeployment, DeployModuleError> {
        // Load file
        let module = std::fs::read(module_path)?;
        self.module_deploy_aux(sender, &module)
    }

    /// Deploy a wasm module as it is output from `cargo concordium build`, i.e.
    /// **including** the prefix of 4 version bytes and 4 module length bytes.
    pub fn module_deploy<P: AsRef<Path>>(
        &mut self,
        sender: AccountAddress,
        module_path: P,
    ) -> Result<SuccessfulModuleDeployment, DeployModuleError> {
        // Load file
        let module = std::fs::read(module_path)?;
        // Here, we skip the 8 bytes that encode the smart contract version and module
        // length
        self.module_deploy_aux(sender, &module[8..])
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
        let mut transaction_fee = self.calculate_energy_cost(self.lookup_module_cost(&artifact));
        // Get the account and check that it has sufficient balance to pay for the
        // reserved_energy and amount.
        let account_info = self.get_account(sender)?;
        if account_info.balance < self.calculate_energy_cost(energy_reserved) + amount {
            return Err(ContractInitError::InsufficientFunds);
        }
        // Construct the context.
        let init_ctx = v0::InitContext {
            metadata:        ChainMetadata {
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
        // Handle the result and update the transaction fee.
        let res = match res {
            v1::InitResult::Success {
                logs,
                return_value: _, /* Ignore return value for now, since our tools do not support
                                  * it for inits, currently. */
                remaining_energy,
                mut state,
            } => {
                let contract_address = self.create_contract_address();
                let energy_used = Energy::from(energy_reserved.energy - remaining_energy);
                transaction_fee += self.calculate_energy_cost(energy_used);

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
                // Subtract the from the invoker.
                self.get_account_mut(sender)?.balance -= amount;

                Ok(SuccessfulContractInit {
                    contract_address,
                    logs,
                    energy_used,
                    transaction_fee,
                })
            }
            v1::InitResult::Reject {
                reason,
                return_value,
                remaining_energy,
            } => {
                let energy_used = Energy::from(energy_reserved.energy - remaining_energy);
                transaction_fee += self.calculate_energy_cost(energy_used);
                Err(ContractInitError::ValidChainError(
                    FailedContractInteraction::Reject {
                        reason,
                        return_value,
                        energy_used,
                        transaction_fee,
                        logs: v0::Logs::default(), // TODO: Get Logs on failures.
                    },
                ))
            }
            v1::InitResult::Trap {
                error,
                remaining_energy,
            } => {
                let energy_used = Energy::from(energy_reserved.energy - remaining_energy);
                transaction_fee += self.calculate_energy_cost(energy_used);
                Err(ContractInitError::ValidChainError(
                    FailedContractInteraction::Trap {
                        error,
                        energy_used,
                        transaction_fee,
                        logs: v0::Logs::default(), // TODO: Get Logs on failures.
                    },
                ))
            }
            v1::InitResult::OutOfEnergy => {
                transaction_fee += self.calculate_energy_cost(energy_reserved);
                Err(ContractInitError::ValidChainError(
                    FailedContractInteraction::OutOFEnergy {
                        energy_used: energy_reserved,
                        transaction_fee,
                        logs: v0::Logs::default(), // TODO: Get Logs on failures.
                    },
                ))
            }
        };
        // Charge the account.
        // We have to get the account info again because of the borrow checker.
        self.get_account_mut(sender)?.balance -= transaction_fee;
        res
    }

    /// Used for handling contract invokes internally.
    ///
    /// Preconditions:
    ///  - `invoker` exists
    ///  - `invoker` has sufficient balance to pay for `remaining_energy`
    ///
    /// Returns:
    ///  - Everything the types can encode apart from
    ///    `Ok(v1::ReceiveResult::Interrupt)`
    ///  TODO: Use proper error types instead of anyhow.
    fn contract_update_aux(
        &mut self,
        invoker: AccountAddress,
        sender: Address,
        address: ContractAddress,
        entrypoint: OwnedEntrypointName,
        parameter: Vec<u8>,
        amount: Amount,
        // The CCD amount reserved from the invoker account. While the amount
        // is reserved, it is not subtracted in the chain.accounts map.
        // Used to handle account balance queries for the invoker account.
        invoker_amount_reserved_for_nrg: Amount,
        mut remaining_energy: Energy,
        chain_events: &mut Vec<ChainEvent>,
    ) -> ExecResult<v1::ReceiveResult<artifact::CompiledFunction>> {
        // Move the amount from the sender to the contract.
        match sender {
            Address::Account(addr) => {
                self.get_account_mut(addr)?.balance -= amount;
            }
            Address::Contract(addr) => {
                self.get_instance_mut(addr)?.self_balance -= amount;
            }
        }
        self.get_instance_mut(address)?.self_balance += amount;

        // Get the instance and artifact. To be used in several places.
        let instance = self.get_instance(address)?;
        let artifact = self.get_artifact(instance.module_reference)?;
        // Subtract the cost of looking up the module
        remaining_energy =
            Energy::from(remaining_energy.energy - self.lookup_module_cost(&artifact).energy);

        // Construct the receive name (or fallback receive name) and ensure its presence
        // in the contract.
        let receive_name = {
            let contract_name = instance.contract_name.as_contract_name().contract_name();
            let receive_name = format!("{}.{}", contract_name, entrypoint);
            let fallback_receive_name = format!("{}.", contract_name);
            if artifact.has_entrypoint(receive_name.as_str()) {
                OwnedReceiveName::new_unchecked(receive_name)
            } else if artifact.has_entrypoint(fallback_receive_name.as_str()) {
                OwnedReceiveName::new_unchecked(fallback_receive_name)
            } else {
                bail!("Entrypoint does not exist.");
            }
        };

        // Construct the receive context
        let receive_ctx = v1::ReceiveContext {
            entrypoint: entrypoint.to_owned(),
            common:     v0::ReceiveContext {
                metadata: ChainMetadata {
                    slot_time: self.slot_time,
                },
                invoker,
                self_address: address,
                self_balance: instance.self_balance,
                sender,
                owner: instance.owner,
                sender_policies: self.get_account(invoker)?.policies.clone(),
            },
        };

        // Construct the instance state
        let mut loader = v1::trie::Loader::new(&[][..]);
        let mut mutable_state = instance.state.thaw();
        let inner = mutable_state.get_inner(&mut loader);
        let instance_state = v1::InstanceState::new(loader, inner);

        // Get the initial result from invoking receive
        let res = v1::invoke_receive(
            std::sync::Arc::new(artifact.clone()),
            receive_ctx,
            v1::ReceiveInvocation {
                amount,
                receive_name: receive_name.as_receive_name(),
                parameter: &parameter,
                energy: InterpreterEnergy {
                    energy: remaining_energy.energy,
                },
            },
            instance_state,
            v1::ReceiveParams {
                max_parameter_size:           65535,
                limit_logs_and_return_values: false,
                support_queries:              true,
            },
        );

        // Set up some data needed for recursively processing the receive until the end,
        // i.e. beyond interrupts.
        let mut data = ProcessReceiveData {
            invoker,
            address,
            contract_name: instance.contract_name.clone(),
            amount,
            invoker_amount_reserved_for_nrg,
            entrypoint: entrypoint.to_owned(),
            chain: self,
            chain_events: Vec::new(),
            mutable_state,
            loader,
        };

        // Process the receive invocation to the end.
        let res = data.process(res);
        // Append the new chain events if the invocation succeeded.
        if matches!(res, Ok(v1::ReceiveResult::Success { .. })) {
            chain_events.append(&mut data.chain_events);
        }
        res
    }

    pub fn contract_update(
        &mut self,
        invoker: AccountAddress, // TODO: Should we add a sender field and allow contract senders?
        address: ContractAddress,
        entrypoint: EntrypointName,
        parameter: ContractParameter,
        amount: Amount,
        energy_reserved: Energy,
    ) -> Result<SuccessfulContractUpdate, ContractUpdateError> {
        // Save backups of accounts and contracts in case of rollbacks.
        let accounts_backup = self.accounts.clone();
        let contracts_backup = self.contracts.clone();

        println!(
            "Updating contract {}, with parameter: {:?}",
            address, parameter.0
        );

        // Ensure account exists and can pay for the reserved energy and amount
        let account_info = self.get_account(invoker)?;
        let invoker_amount_reserved_for_nrg = self.calculate_energy_cost(energy_reserved);
        if account_info.balance < invoker_amount_reserved_for_nrg + amount {
            return Err(ContractUpdateError::InsufficientFunds);
        }

        let mut chain_events = Vec::new();
        let res = self.contract_update_aux(
            invoker,
            Address::Account(invoker),
            address,
            entrypoint.to_owned(),
            parameter.0,
            amount,
            invoker_amount_reserved_for_nrg,
            energy_reserved,
            &mut chain_events,
        );

        let mut transaction_fee = Amount::zero();

        // Convert the wasm_chain_integration result to the one used here and
        // update the transaction fee.
        let res = match res {
            Ok(r) => match r {
                v1::ReceiveResult::Success {
                    logs,
                    state_changed,
                    return_value,
                    remaining_energy,
                } => {
                    let energy_used = Energy::from(energy_reserved.energy - remaining_energy);
                    transaction_fee += self.calculate_energy_cost(energy_used);
                    Ok(SuccessfulContractUpdate {
                        chain_events,
                        energy_used,
                        transaction_fee,
                        return_value: ContractReturnValue(return_value),
                        state_changed,
                        logs,
                    })
                }
                v1::ReceiveResult::Interrupt { .. } => panic!("Should never happen"),
                v1::ReceiveResult::Reject {
                    reason,
                    return_value,
                    remaining_energy,
                } => {
                    let energy_used = Energy::from(energy_reserved.energy - remaining_energy);
                    transaction_fee += self.calculate_energy_cost(energy_used);
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
                    transaction_fee += self.calculate_energy_cost(energy_used);
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
                    transaction_fee += self.calculate_energy_cost(energy_reserved);
                    Err(ContractUpdateError::ValidChainError(
                        FailedContractInteraction::OutOFEnergy {
                            energy_used: energy_reserved,
                            transaction_fee,
                            logs: v0::Logs::default(), // TODO: Get logs on failures.
                        },
                    ))
                }
            },
            Err(e) => {
                // TODO: what is the correct cost here?
                transaction_fee += self.calculate_energy_cost(energy_reserved);
                Err(ContractUpdateError::StringError(e.to_string()))
            }
        };

        // Handle rollback
        if res.is_err() {
            self.accounts = accounts_backup;
            self.contracts = contracts_backup;
        }

        // Charge the transaction fee irrespective of the result
        self.get_account_mut(invoker)?.balance -= transaction_fee;
        res
    }

    /// TODO: Should we make invoker and energy optional?
    /// TODO: Only works with basic update functions. Rewrite to use
    /// `contract_update_aux`.
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

        println!(
            "Invoking contract {} with parameter: {:?}",
            address, parameter.0
        );

        // Ensure account exists and can pay for the reserved energy
        let account_info = self.get_account(invoker)?;
        if account_info.balance < self.calculate_energy_cost(energy_reserved) {
            return Err(ContractUpdateError::InsufficientFunds);
        }
        // Construct the context
        let receive_ctx = v1::ReceiveContext {
            entrypoint: entrypoint.to_owned(),
            common:     v0::ReceiveContext {
                metadata: ChainMetadata {
                    slot_time: self.slot_time,
                },
                invoker,
                self_address: address,
                self_balance: instance.self_balance + amount,
                sender: Address::Account(invoker),
                owner: instance.owner,
                sender_policies: account_info.policies.clone(),
            },
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
        let res = v1::invoke_receive::<
            _,
            _,
            _,
            _,
            v1::ReceiveContext<v0::OwnedPolicyBytes>,
            v1::ReceiveContext<v0::OwnedPolicyBytes>,
        >(
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
                    chain_events: Vec::new(), // TODO: add host events
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

    pub fn set_slot_time(&mut self, slot_time: SlotTime) { self.slot_time = slot_time; }

    pub fn set_euro_per_energy(&mut self, euro_per_energy: ExchangeRate) {
        self.euro_per_energy = euro_per_energy;
    }

    pub fn set_micro_ccd_per_euro(&mut self, micro_ccd_per_euro: ExchangeRate) {
        self.micro_ccd_per_euro = micro_ccd_per_euro;
    }

    /// Returns the balance of an account if it exists.
    pub fn account_balance(&self, address: AccountAddress) -> Option<Amount> {
        self.accounts.get(&address).and_then(|ai| Some(ai.balance))
    }

    /// Returns the balance of an contract if it exists.
    pub fn contract_balance(&self, address: ContractAddress) -> Option<Amount> {
        self.contracts
            .get(&address)
            .and_then(|ci| Some(ci.self_balance))
    }

    // Calculate the microCCD(mCCD) cost of energy(NRG) using the two exchange rates
    // available:
    //
    // To find the mCCD/NRG exchange rate:
    //
    //  euro     mCCD   euro * mCCD   mCCD
    //  ----  *  ---- = ----------- = ----
    //  NRG      euro   NRG * euro    NRG
    //
    // To convert the `energy` parameter to mCCD:
    //
    //        mCCD   NRG * mCCD
    //  NRG * ---- = ---------- = mCCD
    //        NRG       NRG
    //
    //  TODO: If using a mCCD/euro exchange rate with large numbers, then this can
    // overflow.
    pub fn calculate_energy_cost(&self, energy: Energy) -> Amount {
        let micro_ccd_per_energy_numerator =
            self.euro_per_energy.numerator() * self.micro_ccd_per_euro.numerator();
        let micro_ccd_per_energy_denominator =
            self.euro_per_energy.denominator() * self.micro_ccd_per_euro.denominator();
        Amount::from_micro_ccd(
            energy.energy * micro_ccd_per_energy_numerator / micro_ccd_per_energy_denominator,
        )
    }

    pub fn lookup_module_cost(&self, artifact: &ArtifactV1) -> Energy {
        // TODO: Is it just the `.code`?
        // Comes from Concordium/Cost.hs::lookupModule
        Energy::from(artifact.code.len() as u64 / 50)
    }

    fn get_artifact(&self, module_ref: ModuleReference) -> Result<&ArtifactV1, ModuleMissing> {
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

struct ProcessReceiveData<'a, 'b> {
    invoker: AccountAddress,
    address: ContractAddress,
    contract_name: OwnedContractName,
    amount: Amount,
    /// The CCD amount reserved from the invoker account for the energy. While
    /// the amount is reserved, it is not subtracted in the chain.accounts
    /// map. Used to handle account balance queries for the invoker account.
    invoker_amount_reserved_for_nrg: Amount,
    entrypoint: OwnedEntrypointName,
    chain: &'a mut Chain,
    chain_events: Vec<ChainEvent>,
    mutable_state: MutableState,
    loader: v1::trie::Loader<&'b [u8]>,
}

impl<'a, 'b> ProcessReceiveData<'a, 'b> {
    /// Process a receive function until completion.
    ///
    /// *Preconditions*:
    /// - Contract instance exists in `chain.contracts`.
    /// - Account exists in `chain.accounts`.
    fn process(
        &mut self,
        res: ExecResult<v1::ReceiveResult<artifact::CompiledFunction>>,
    ) -> ExecResult<v1::ReceiveResult<artifact::CompiledFunction>> {
        match res {
            Ok(r) => match r {
                v1::ReceiveResult::Success {
                    logs,
                    state_changed,
                    return_value,
                    remaining_energy,
                } => {
                    println!("\tSuccessful contract update {}", self.address);
                    let update_event = ChainEvent::Updated {
                        address:    self.address,
                        contract:   self.contract_name.clone(),
                        entrypoint: self.entrypoint.clone(),
                        amount:     self.amount,
                    };
                    if state_changed {
                        let instance = self
                            .chain
                            .get_instance_mut(self.address)
                            .expect("Instance known to exist");
                        let mut collector = v1::trie::SizeCollector::default();
                        instance.state =
                            self.mutable_state.freeze(&mut self.loader, &mut collector);
                        // TODO: Charge energy for this
                    }
                    // Add update event
                    self.chain_events.push(update_event);
                    Ok(v1::ReceiveResult::Success {
                        logs,
                        state_changed,
                        return_value,
                        remaining_energy,
                    })
                }
                v1::ReceiveResult::Interrupt {
                    remaining_energy,
                    state_changed,
                    logs,
                    config,
                    interrupt,
                } => {
                    println!("\tInterrupting contract {}", self.address);

                    // Create the interrupt event, which will be included for transfers and calls,
                    // but not for the remaining interrupts.
                    // TODO: Or is it included in upgrades as well?
                    let interrupt_event = ChainEvent::Interrupted {
                        address: self.address,
                        logs,
                    };
                    match interrupt {
                        v1::Interrupt::Transfer { to, amount } => {
                            // Add the interrupt event
                            self.chain_events.push(interrupt_event);

                            println!("Transferring {} CCD to {}", amount, to);

                            let response = {
                                // Check if receiver account exists
                                if !self.chain.accounts.contains_key(&to) {
                                    InvokeResponse::Failure {
                                        kind: v1::InvokeFailure::NonExistentAccount,
                                    }
                                } else if self
                                    .chain
                                    .get_instance(self.address)
                                    .expect("Contract is known to exist")
                                    .self_balance
                                    < amount
                                {
                                    InvokeResponse::Failure {
                                        kind: v1::InvokeFailure::InsufficientAmount,
                                    }
                                } else {
                                    // Move the CCD
                                    self.chain
                                        .get_account_mut(to)
                                        .expect("Account is known to exist")
                                        .balance += amount;
                                    let instance = self
                                        .chain
                                        .get_instance_mut(self.address)
                                        .expect("Contract is known to exist");
                                    instance.self_balance -= amount;

                                    // Add transfer event
                                    self.chain_events.push(ChainEvent::Transferred {
                                        from: self.address,
                                        amount,
                                        to,
                                    });

                                    InvokeResponse::Success {
                                        new_balance: instance.self_balance,
                                        data:        None,
                                    }
                                }
                            };
                            let success = matches!(response, InvokeResponse::Success { .. });
                            // Add resume event
                            self.chain_events.push(ChainEvent::Resumed {
                                address: self.address,
                                success,
                            });

                            let resume_res = v1::resume_receive(
                                config,
                                response,
                                InterpreterEnergy::from(remaining_energy),
                                &mut self.mutable_state,
                                false, // never changes on transfers
                                self.loader,
                            );

                            // Resume
                            self.process(resume_res)
                        }
                        v1::Interrupt::Call {
                            address,
                            parameter,
                            name,
                            amount,
                        } => {
                            // Add the interrupt event
                            self.chain_events.push(interrupt_event);

                            if state_changed {
                                println!("\t\tState was changed. Saving prior to another call.");
                                let mut collector = SizeCollector::default();
                                let persistent_state =
                                    self.mutable_state.freeze(&mut self.loader, &mut collector);
                                // TODO: Charge for size of new state.
                                self.chain.get_instance_mut(address)?.state = persistent_state;
                            }

                            println!(
                                "\t\tCalling contract {}\n\t\t\twith parameter: {:?}",
                                address, parameter
                            );

                            let res = self.chain.contract_update_aux(
                                self.invoker,
                                Address::Contract(self.address),
                                address,
                                name,
                                parameter,
                                amount,
                                self.invoker_amount_reserved_for_nrg,
                                Energy::from(remaining_energy),
                                &mut self.chain_events,
                            );

                            let (success, response, energy_after_invoke, state_changed) = match res
                            {
                                Ok(r) => match r {
                                    v1::ReceiveResult::Success {
                                        return_value,
                                        remaining_energy,
                                        state_changed,
                                        ..
                                    } => {
                                        println!(
                                            "\t\tInvoke returned with value: {:?}",
                                            return_value
                                        );
                                        (
                                            true,
                                            InvokeResponse::Success {
                                                new_balance: self
                                                    .chain
                                                    .get_instance(self.address)?
                                                    .self_balance,
                                                data:        Some(return_value),
                                            },
                                            remaining_energy,
                                            state_changed,
                                        )
                                    }
                                    v1::ReceiveResult::Interrupt { .. } => {
                                        panic!("Internal error: Should never return on interrupts.")
                                    }
                                    v1::ReceiveResult::Reject {
                                        reason,
                                        return_value,
                                        remaining_energy,
                                    } => (
                                        false,
                                        InvokeResponse::Failure {
                                            kind: v1::InvokeFailure::ContractReject {
                                                code: reason,
                                                data: return_value,
                                            },
                                        },
                                        remaining_energy,
                                        false,
                                    ),
                                    v1::ReceiveResult::Trap {
                                        remaining_energy, ..
                                    } => (
                                        false,
                                        InvokeResponse::Failure {
                                            kind: v1::InvokeFailure::RuntimeError,
                                        },
                                        remaining_energy,
                                        false,
                                    ),
                                    v1::ReceiveResult::OutOfEnergy => (
                                        false,
                                        InvokeResponse::Failure {
                                            kind: v1::InvokeFailure::RuntimeError,
                                        },
                                        0,
                                        false,
                                    ), // TODO: What is the correct error here?
                                },
                                Err(_e) => (
                                    false,
                                    InvokeResponse::Failure {
                                        kind: v1::InvokeFailure::RuntimeError,
                                    },
                                    0,
                                    false,
                                ), // TODO: Correct energy here?
                            };

                            // Add resume event
                            let resume_event = ChainEvent::Resumed {
                                address: self.address,
                                success,
                            };

                            println!(
                                "\tResuming contract {}\n\t\tafter {}",
                                self.address,
                                if success {
                                    "succesful invocation"
                                } else {
                                    "failed invocation"
                                }
                            );
                            self.chain_events.push(resume_event);

                            // Update the mutable state, since it might have been changed on
                            // reentry.
                            self.mutable_state =
                                self.chain.get_instance(self.address)?.state.thaw();

                            let resume_res = v1::resume_receive(
                                config,
                                response,
                                InterpreterEnergy::from(energy_after_invoke),
                                &mut self.mutable_state,
                                state_changed,
                                self.loader,
                            );

                            self.process(resume_res)
                        }
                        v1::Interrupt::Upgrade { module_ref } => todo!(),
                        v1::Interrupt::QueryAccountBalance { address } => {
                            println!("Querying account balance of {}", address);
                            // When querying an account, the amounts from any `invoke_transfer`s
                            // should be included. That is handled by
                            // the `chain` struct already. transaction.
                            // However, that is hand
                            let response = match self.chain.account_balance(address) {
                                Some(acc_bal) => {
                                    // If you query the invoker account, it should also
                                    // take into account the send-amount and the amount reserved for
                                    // the reserved max energy. The former is handled in
                                    // `contract_update_aux`, but the latter is represented in
                                    // `self.invoker_amount_reserved_for_nrg`.
                                    let acc_bal = if address == self.invoker {
                                        acc_bal - self.invoker_amount_reserved_for_nrg
                                    } else {
                                        acc_bal
                                    };

                                    // TODO: Do we need non-zero staked and shielded balances?
                                    let balances =
                                        to_bytes(&(acc_bal, Amount::zero(), Amount::zero()));
                                    InvokeResponse::Success {
                                        new_balance: self
                                            .chain
                                            .get_instance(self.address)?
                                            .self_balance,
                                        data:        Some(balances),
                                    }
                                }
                                None => InvokeResponse::Failure {
                                    kind: v1::InvokeFailure::NonExistentAccount,
                                },
                            };

                            let energy_after_invoke = remaining_energy - QUERY_ACCOUNT_BALANCE_COST;

                            let resume_res = v1::resume_receive(
                                config,
                                response,
                                InterpreterEnergy::from(energy_after_invoke),
                                &mut self.mutable_state,
                                false, // State never changes on queries.
                                self.loader,
                            );

                            self.process(resume_res)
                        }
                        v1::Interrupt::QueryContractBalance { address } => {
                            println!("Querying contract balance of {}", address);

                            let response = match self.chain.contract_balance(address) {
                                Some(balance) => InvokeResponse::Success {
                                    new_balance: self
                                        .chain
                                        .get_instance(self.address)?
                                        .self_balance,
                                    data:        Some(to_bytes(&balance)),
                                },
                                None => InvokeResponse::Failure {
                                    kind: v1::InvokeFailure::NonExistentContract,
                                },
                            };

                            let energy_after_invoke =
                                remaining_energy - QUERY_CONTRACT_BALANCE_COST;

                            let resume_res = v1::resume_receive(
                                config,
                                response,
                                InterpreterEnergy::from(energy_after_invoke),
                                &mut self.mutable_state,
                                false, // State never changes on queries.
                                self.loader,
                            );

                            self.process(resume_res)
                        }
                        v1::Interrupt::QueryExchangeRates => {
                            println!("Querying exchange rates");

                            let exchange_rates =
                                (self.chain.euro_per_energy, self.chain.micro_ccd_per_euro);

                            let response = InvokeResponse::Success {
                                new_balance: self.chain.get_instance(self.address)?.self_balance,
                                data:        Some(to_bytes(&exchange_rates)),
                            };

                            let energy_after_invoke = remaining_energy - QUERY_EXCHANGE_RATE_COST;

                            let resume_res = v1::resume_receive(
                                config,
                                response,
                                InterpreterEnergy::from(energy_after_invoke),
                                &mut self.mutable_state,
                                false, // State never changes on queries.
                                self.loader,
                            );

                            self.process(resume_res)
                        }
                    }
                }
                x => Ok(x),
            },
            Err(e) => Err(e),
        }
    }
}

#[derive(Debug, Error)]
#[error("Module has not been deployed.")]
struct ModuleMissing;

impl From<ModuleMissing> for ContractInitError {
    fn from(_: ModuleMissing) -> Self { Self::ModuleDoesNotExist }
}

impl From<ModuleMissing> for ContractUpdateError {
    fn from(_: ModuleMissing) -> Self { Self::ModuleDoesNotExist }
}

#[derive(Debug, Error)]
#[error("Contract instance has not been instantiated.")]
struct ContractInstanceMissing;

impl From<ContractInstanceMissing> for ContractUpdateError {
    fn from(_: ContractInstanceMissing) -> Self { Self::InstanceDoesNotExist }
}

#[derive(Debug, Error)]
#[error("Account has not been created.")]
struct AccountMissing;

impl From<AccountMissing> for ContractInitError {
    fn from(_: AccountMissing) -> Self { Self::AccountDoesNotExist }
}

impl From<AccountMissing> for ContractUpdateError {
    fn from(_: AccountMissing) -> Self { Self::AccountDoesNotExist }
}

#[derive(Clone)]
pub struct AccountInfo {
    /// The account balance. TODO: Do we need the three types of balances?
    pub balance: Amount,
    /// Account policies.
    policies:    v0::OwnedPolicyBytes,
}

pub struct TestPolicies(v0::OwnedPolicyBytes);

impl TestPolicies {
    // TODO: Make correctly structured policies ~= Vec<Tuple<Credential,
    // PolicyBytes>>.
    pub fn empty() -> Self { Self(v0::OwnedPolicyBytes::new()) }

    // TODO: Add helper functions for creating arbitrary valid policies.
}

impl AccountInfo {
    pub fn new_with_policy(balance: Amount, policies: TestPolicies) -> Self {
        Self {
            balance,
            policies: policies.0,
        }
    }

    /// Create new account info with empty account policies.
    pub fn new(balance: Amount) -> Self { Self::new_with_policy(balance, TestPolicies::empty()) }
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
    /// Entrypoint does not exist and neither does the fallback entrypoint.
    EntrypointDoesNotExist,
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
        entrypoint: OwnedEntrypointName,
        amount:     Amount,
    },
    Transferred {
        from:   ContractAddress,
        amount: Amount,
        to:     AccountAddress,
    },
}

// TODO: Consider adding function to aggregate all logs from the host_events.
#[derive(Debug)]
pub struct SuccessfulContractUpdate {
    /// Host events that occured. This includes interrupts, resumes, and
    /// upgrades.
    pub chain_events:    Vec<ChainEvent>,
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
pub struct Transfer {
    pub from:   ContractAddress,
    pub amount: Amount,
    pub to:     AccountAddress,
}

impl SuccessfulContractUpdate {
    pub fn transfers(&self) -> Vec<Transfer> {
        self.chain_events
            .iter()
            .filter_map(|e| {
                if let ChainEvent::Transferred { from, amount, to } = e {
                    Some(Transfer {
                        from:   *from,
                        amount: *amount,
                        to:     *to,
                    })
                } else {
                    None
                }
            })
            .collect()
    }
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

#[derive(Debug)]
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

    const NRG_PER_MICRO_CCD: u64 = 2404;
    const ACC_0: AccountAddress = AccountAddress([0; 32]);
    const ACC_1: AccountAddress = AccountAddress([1; 32]);
    const WASM_TEST_FOLDER: &str =
        "../../concordium-node/concordium-consensus/testdata/contracts/v1";

    #[test]
    fn creating_accounts_work() {
        let mut chain = Chain::new();
        chain.create_account(ACC_0, AccountInfo::new(Amount::from_ccd(1)));
        chain.create_account(ACC_1, AccountInfo::new(Amount::from_ccd(2)));

        assert_eq!(chain.accounts.len(), 2);
        assert_eq!(chain.account_balance(ACC_0), Some(Amount::from_ccd(1)));
        assert_eq!(chain.account_balance(ACC_1), Some(Amount::from_ccd(2)));
    }

    #[test]
    fn deploying_valid_module_works() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res = chain
            .module_deploy(ACC_0, "examples/icecream/icecream.wasm.v1")
            .expect("Deploying valid module should work");

        assert_eq!(chain.modules.len(), 1);
        assert_eq!(
            chain.account_balance(ACC_0),
            Some(initial_balance - res.transaction_fee)
        );
    }

    #[test]
    fn initializing_valid_contract_works() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy(ACC_0, "examples/icecream/icecream.wasm.v1")
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
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy(ACC_0, "examples/icecream/icecream.wasm.v1")
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
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy(ACC_0, "examples/icecream/icecream.wasm.v1")
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
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        let transfer_amount = Amount::from_ccd(1);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));
        chain.create_account(ACC_1, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy(ACC_0, "examples/integrate/a.wasm.v1")
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
        assert_eq!(res_update.transfers(), [Transfer {
            from:   res_init.contract_address,
            amount: transfer_amount,
            to:     ACC_1,
        }]);
        assert_eq!(chain.contracts.len(), 1);
        assert!(res_update.state_changed);
        assert_eq!(res_update.return_value.0, [2, 0, 0, 0]);
        // Assert that the updated state is persisted.
        assert_eq!(res_view.return_value.0, [2, 0, 0, 0]);
    }

    #[test]
    fn update_with_account_transfer_to_missing_account_fails() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        let transfer_amount = Amount::from_ccd(1);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy(ACC_0, "examples/integrate/a.wasm.v1")
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

        let res_update = chain.contract_update(
            ACC_0,
            res_init.contract_address,
            EntrypointName::new_unchecked("receive"),
            ContractParameter::from_typed(&ACC_1), // We haven't created ACC_1.
            transfer_amount,
            Energy::from(100000u64),
        );

        match res_update {
            Err(ContractUpdateError::ValidChainError(FailedContractInteraction::Reject {
                reason,
                transaction_fee,
                ..
            })) => {
                assert_eq!(reason, -3); // Corresponds to contract error TransactionErrorAccountMissing
                assert_eq!(
                    chain.account_balance(ACC_0),
                    Some(
                        initial_balance
                            - res_deploy.transaction_fee
                            - res_init.transaction_fee
                            - transaction_fee
                    )
                );
            }
            _ => panic!("Expected contract update to fail"),
        }
    }

    // TODO: Add tests that check:
    // - Correct account balances after init / update failures (when Amount > 0)
    //
    #[test]
    fn update_with_fib_reentry_works() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(1000000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy(ACC_0, "examples/fib/a.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_fib"),
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
                ContractParameter::from_typed(&6u64),
                Amount::zero(),
                Energy::from(4000000u64),
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
            )
        );
        assert_eq!(chain.contracts.len(), 1);
        assert!(res_update.state_changed);
        let expected_res = u64::to_le_bytes(13);
        assert_eq!(res_update.return_value.0, expected_res);
        // Assert that the updated state is persisted.
        assert_eq!(res_view.return_value.0, expected_res);
    }

    #[test]
    fn update_with_integrate_reentry_works() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy(ACC_0, "examples/integrate/a.wasm.v1")
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
                EntrypointName::new_unchecked("recurse"),
                ContractParameter::from_typed(&10u32),
                Amount::zero(),
                Energy::from(1000000u64),
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
            )
        );
        assert_eq!(chain.contracts.len(), 1);
        assert!(res_update.state_changed);
        let expected_res = 10 + 7 + 11 + 3 + 7 + 11;
        assert_eq!(res_update.return_value.0, u32::to_le_bytes(expected_res));
        // Assert that the updated state is persisted.
        assert_eq!(res_view.return_value.0, u32::to_le_bytes(expected_res));
    }

    #[test]
    fn update_with_rollback_and_reentry_works() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(1000000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy(ACC_0, "examples/integrate/a.wasm.v1")
            .expect("Deploying valid module should work");

        let input_param: u32 = 8;

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
                EntrypointName::new_unchecked("inc-fail-on-zero"),
                ContractParameter::from_typed(&input_param),
                Amount::zero(),
                Energy::from(100000000u64),
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

        assert_eq!(
            chain.account_balance(ACC_0),
            Some(
                initial_balance
                    - res_deploy.transaction_fee
                    - res_init.transaction_fee
                    - res_update.transaction_fee
            )
        );
        assert!(res_update.state_changed);
        let expected_res = 2u32.pow(input_param) - 1;
        assert_eq!(res_update.return_value.0, u32::to_le_bytes(expected_res));
        // Assert that the updated state is persisted.
        assert_eq!(res_view.return_value.0, u32::to_le_bytes(expected_res));
    }

    mod query_account_balance {
        use super::*;

        /// Queries the balance of another account and asserts that it is as
        /// expected.
        #[test]
        fn test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));
            chain.create_account(ACC_1, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_raw(
                    ACC_0,
                    format!("{}/queries-account-balance.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000u64),
                )
                .expect("Initializing valid contract should work");

            // TODO: Implement serial for four-tuples in contracts-common. Nesting tuples to
            // get around it here.
            // The contract will query the balance of ACC_1 and assert that the three
            // balances match this input.
            let input_param = (ACC_1, (initial_balance, Amount::zero(), Amount::zero()));

            let res_update = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    ContractParameter::from_typed(&input_param),
                    Amount::zero(),
                    Energy::from(100000u64),
                )
                .expect("Updating valid contract should work");

            assert_eq!(
                chain.account_balance(ACC_0),
                Some(
                    initial_balance
                        - res_deploy.transaction_fee
                        - res_init.transaction_fee
                        - res_update.transaction_fee
                )
            );
            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }

        /// Queries the balance of the invoker account, which will have have the
        /// expected balance of:
        /// prior_balance - amount_sent - amount_to_cover_reserved_NRG.
        #[test]
        fn invoker_test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));
            chain.create_account(ACC_1, AccountInfo::new(initial_balance));

            let res_deploy = chain
            .module_deploy_raw(ACC_0, format!("{}/queries-account-balance.wasm", WASM_TEST_FOLDER)) // TODO: Add wasm files to the repo for tests.
            .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000u64),
                )
                .expect("Initializing valid contract should work");

            let update_amount = Amount::from_ccd(123);
            let energy_limit = Energy::from(100000u64);
            let invoker_reserved_amount = update_amount + chain.calculate_energy_cost(energy_limit);

            // The contract will query the balance of ACC_1, which is also the invoker, and
            // assert that the three balances match this input.
            let expected_balance = initial_balance - invoker_reserved_amount;
            let input_param = (ACC_1, (expected_balance, Amount::zero(), Amount::zero()));

            let res_update = chain
                .contract_update(
                    ACC_1,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    ContractParameter::from_typed(&input_param),
                    update_amount,
                    energy_limit,
                )
                .expect("Updating valid contract should work");

            assert_eq!(
                chain.account_balance(ACC_0),
                Some(initial_balance - res_deploy.transaction_fee - res_init.transaction_fee)
            );
            assert_eq!(
                chain.account_balance(ACC_1),
                // Differs from `expected_balance` as it only includes the actual amount charged
                // for the NRG use. Not the reserved amount.
                Some(initial_balance - res_update.transaction_fee - update_amount)
            );
            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }

        /// Makes a transfer to an account, then queries its balance and asserts
        /// that it is as expected.
        #[test]
        fn transfer_test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));
            chain.create_account(ACC_1, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_raw(
                    ACC_0,
                    format!("{}/queries-account-balance-transfer.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let amount_to_send = Amount::from_ccd(123);

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    amount_to_send, // Make sure the contract has CCD to transfer.
                    Energy::from(10000u64),
                )
                .expect("Initializing valid contract should work");

            let amount_to_send = Amount::from_ccd(123);
            let expected_balance = initial_balance + amount_to_send;
            let input_param = (
                ACC_1,
                amount_to_send,
                (expected_balance, Amount::zero(), Amount::zero()),
            );

            let res_update = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    ContractParameter::from_typed(&input_param),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Updating valid contract should work");

            assert_eq!(
                chain.account_balance(ACC_0),
                Some(
                    initial_balance
                        - res_deploy.transaction_fee
                        - res_init.transaction_fee
                        - res_update.transaction_fee
                        - amount_to_send
                )
            );
            assert_eq!(
                chain.account_balance(ACC_1),
                Some(initial_balance + amount_to_send)
            );
            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Interrupted { .. },
                ChainEvent::Transferred { .. },
                ChainEvent::Resumed { .. },
                ChainEvent::Updated { .. }
            ]));
        }

        #[test]
        fn balance_test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));
            chain.create_account(ACC_1, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_raw(
                    ACC_0,
                    format!("{}/queries-account-balance.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000u64),
                )
                .expect("Initializing valid contract should work");

            // TODO: Implement serial for four-tuples in contracts-common. Nesting tuples to
            // get around it here.
            // The contract will query the balance of ACC_1 and assert that the three
            // balances match this input.
            let input_param = (ACC_1, (initial_balance, Amount::zero(), Amount::zero()));

            let res_update = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    ContractParameter::from_typed(&input_param),
                    Amount::zero(),
                    Energy::from(100000u64),
                )
                .expect("Updating valid contract should work");

            assert_eq!(
                chain.account_balance(ACC_0),
                Some(
                    initial_balance
                        - res_deploy.transaction_fee
                        - res_init.transaction_fee
                        - res_update.transaction_fee
                )
            );
            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }

        /// Queries the balance of a missing account and asserts that it returns
        /// the correct error.
        #[test]
        fn missing_account_test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_raw(
                    ACC_0,
                    format!(
                        "{}/queries-account-balance-missing-account.wasm",
                        WASM_TEST_FOLDER
                    ),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000u64),
                )
                .expect("Initializing valid contract should work");

            // The account to query, which doesn't exist in this test case.
            let input_param = ACC_1;

            let res_update = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    ContractParameter::from_typed(&input_param),
                    Amount::zero(),
                    Energy::from(100000u64),
                )
                .expect("Updating valid contract should work");

            assert_eq!(
                chain.account_balance(ACC_0),
                Some(
                    initial_balance
                        - res_deploy.transaction_fee
                        - res_init.transaction_fee
                        - res_update.transaction_fee
                )
            );
            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }
    }

    mod query_contract_balance {
        use super::*;

        /// Test querying the balance of another contract, which exists. Asserts
        /// that the balance is as expected.
        #[test]
        fn test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let init_amount = Amount::from_ccd(123);

            let res_deploy = chain
                .module_deploy_raw(
                    ACC_0,
                    format!("{}/queries-contract-balance.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000u64),
                )
                .expect("Initializing valid contract should work");

            let res_init_other = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    init_amount, // Set up another contract with `init_amount` balance
                    Energy::from(10000u64),
                )
                .expect("Initializing valid contract should work");

            // check that the other contract has `self_balance == init_amount`.
            let input_param = (res_init_other.contract_address, init_amount);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    ContractParameter::from_typed(&input_param),
                    Amount::zero(),
                    Energy::from(100000u64),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }

        /// Test querying the balance of the contract instance itself. This
        /// should include the amount sent to it in the update transaction.
        #[test]
        fn query_self_test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let init_amount = Amount::from_ccd(123);
            let update_amount = Amount::from_ccd(456);

            let res_deploy = chain
                .module_deploy_raw(
                    ACC_0,
                    format!("{}/queries-contract-balance.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    init_amount,
                    Energy::from(10000u64),
                )
                .expect("Initializing valid contract should work");

            // check that the other contract has `self_balance == init_amount`.
            let input_param = (res_init.contract_address, init_amount + update_amount);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    ContractParameter::from_typed(&input_param),
                    update_amount,
                    Energy::from(100000u64),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }

        /// Test querying the balance after a transfer of CCD.
        #[test]
        fn query_self_after_transfer_test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let init_amount = Amount::from_ccd(123);
            let update_amount = Amount::from_ccd(456);
            let transfer_amount = Amount::from_ccd(78);

            let res_deploy = chain
                .module_deploy_raw(
                    ACC_0,
                    format!(
                        "{}/queries-contract-balance-transfer.wasm",
                        WASM_TEST_FOLDER
                    ),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    init_amount,
                    Energy::from(10000u64),
                )
                .expect("Initializing valid contract should work");

            let input_param = (
                ACC_0,
                transfer_amount,
                (
                    res_init.contract_address,
                    init_amount + update_amount - transfer_amount,
                ),
            );

            let res_update = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    ContractParameter::from_typed(&input_param),
                    update_amount,
                    Energy::from(100000u64),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Interrupted { .. },
                ChainEvent::Transferred { .. },
                ChainEvent::Resumed { .. },
                ChainEvent::Updated { .. }
            ]));
        }

        /// Test querying the balance of a contract that doesn't exist.
        #[test]
        fn missing_contract_test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_raw(
                    ACC_0,
                    format!(
                        "{}/queries-contract-balance-missing-contract.wasm",
                        WASM_TEST_FOLDER
                    ),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000u64),
                )
                .expect("Initializing valid contract should work");

            // Non-existent contract address.
            let input_param = ContractAddress::new(123, 456);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    ContractParameter::from_typed(&input_param),
                    Amount::zero(),
                    Energy::from(100000u64),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }
    }

    mod query_exchange_rates {

        use super::*;

        /// Test querying the exchange rates.
        #[test]
        fn test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_raw(
                    ACC_0,
                    format!("{}/queries-exchange-rates.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000u64),
                )
                .expect("Initializing valid contract should work");

            // Non-existent contract address.
            let input_param = (chain.euro_per_energy, chain.micro_ccd_per_euro);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    ContractParameter::from_typed(&input_param),
                    Amount::zero(),
                    Energy::from(100000u64),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }
    }
}
