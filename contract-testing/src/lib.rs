use anyhow::bail;
use concordium_base::{
    base::{Energy, ExchangeRate},
    common,
    contracts_common::*,
    smart_contracts::{ModuleSource, WasmModule, WasmVersion},
    transactions::{self, cost},
};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::Path, sync::Arc};
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

/// Cost of querying the account balance from a within smart contract instance.
const CONTRACT_INSTANCE_QUERY_ACCOUNT_BALANCE_COST: Energy = Energy { energy: 200 };
/// Cost of querying the contract balance from a within smart contract instance.
const CONTRACT_INSTANCE_QUERY_CONTRACT_BALANCE_COST: Energy = Energy { energy: 200 };
/// Cost of querying the current exchange rates from a within smart contract
/// instance.
const CONTRACT_INSTANCE_QUERY_EXCHANGE_RATE_COST: Energy = Energy { energy: 100 };
/// The base cost of initializing a contract instance to cover administrative
/// costs. Even if no code is run and no instance created.
const INITIALIZE_CONTRACT_INSTANCE_BASE_COST: Energy = Energy { energy: 300 };
/// Cost of creating an empty smart contract instance.
const INITIALIZE_CONTRACT_INSTANCE_CREATE_COST: Energy = Energy { energy: 200 };

pub struct Chain {
    /// The slot time viewable inside the smart contracts.
    /// Defaults to `0`.
    pub slot_time:           SlotTime,
    /// MicroCCD per Euro ratio.
    pub micro_ccd_per_euro:  ExchangeRate,
    /// Euro per Energy ratio.
    pub euro_per_energy:     ExchangeRate,
    /// Accounts and info about them.
    pub accounts:            BTreeMap<AccountAddress, AccountInfo>,
    /// Smart contract modules.
    pub modules:             BTreeMap<ModuleReference, Arc<ArtifactV1>>,
    /// Smart contract instances.
    pub contracts:           BTreeMap<ContractAddress, ContractInstance>,
    /// Next contract index to use when creating a new instance.
    pub next_contract_index: u64,
    pub instance_changesets: BTreeMap<ContractAddress, InstanceChangeSet>,
}

#[derive(Clone)]
pub struct ContractInstance {
    pub module_reference: ModuleReference,
    pub contract_name:    OwnedContractName,
    pub state:            v1::trie::PersistentState,
    pub owner:            AccountAddress,
    pub self_balance:     Amount,
}

#[derive(Clone, Copy)]
pub enum AmountDelta {
    Positive(Amount),
    Negative(Amount),
}
impl AmountDelta {
    pub fn new() -> Self { Self::Positive(Amount::zero()) }
}

/// Data held for a contract instance during the execution of a transaction.
#[derive(Clone)]
pub struct InstanceChangeSet {
    // modification_index ?
    amount_changed: AmountDelta,
    state:          MutableState,
}

impl InstanceChangeSet {
    fn from_state(state: MutableState) -> Self {
        Self {
            amount_changed: AmountDelta::new(),
            state,
        }
    }
}

impl Chain {
    /// Create a new [`Self`] where all the configurable parameters are
    /// provided.
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
            instance_changesets: BTreeMap::new(),
        }
    }

    /// Create a new [`Self`] with a specified `slot_time` where
    ///  - `micro_ccd_per_euro` defaults to `147235241 / 1`
    ///  - `euro_per_energy` defaults to `1 / 50000`.
    pub fn new_with_time(slot_time: SlotTime) -> Self {
        Self {
            slot_time,
            ..Self::new()
        }
    }

    /// Create a new [`Self`] where
    ///  - `slot_time` defaults to `0`,
    ///  - `micro_ccd_per_euro` defaults to `147235241 / 1`
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
    ///  - `module`: the raw wasm module (i.e. **without** the contract version
    ///    and module length bytes (8 bytes total)).
    fn module_deploy_aux(
        &mut self,
        sender: AccountAddress,
        wasm_module: WasmModule,
    ) -> Result<SuccessfulModuleDeployment, DeployModuleError> {
        // Deserialize as wasm module (artifact)
        let artifact = wasm_transform::utils::instantiate_with_metering::<v1::ProcessedImports, _>(
            &ConcordiumAllowedImports {
                support_upgrade: true,
            },
            wasm_module.source.as_ref(),
        )?;

        // Calculate transaction fee of deployment
        let energy = {
            // +1 for the tag, +8 for size and version
            let payload_size = 1
                + 8
                + wasm_module.source.size() as u64
                + transactions::construct::TRANSACTION_HEADER_SIZE;
            let number_of_sigs = self.get_account(sender)?.signature_count;
            let base_cost = cost::base_cost(payload_size, number_of_sigs);
            let deploy_module_cost = cost::deploy_module(wasm_module.source.size());
            base_cost + deploy_module_cost
        };
        let transaction_fee = self.calculate_energy_cost(energy);
        println!(
            "Deploying module with size {}, resulting in {} NRG.",
            wasm_module.source.size(),
            energy
        );

        // Try to subtract cost for account
        let account = self.get_account_mut(sender)?;
        if account.balance < transaction_fee {
            return Err(DeployModuleError::InsufficientFunds);
        };
        account.balance -= transaction_fee;

        // Save the module TODO: Use wasm_module.get_module_ref() and find a proper way
        // to convert ModuleRef to ModuleReference.
        let module_reference = {
            let mut hasher = Sha256::new();
            hasher.update(wasm_module.source.as_ref());
            let hash: [u8; 32] = hasher.finalize().into();
            ModuleReference::from(hash)
        };
        // Ensure module hasn't been deployed before.
        if self.modules.contains_key(&module_reference) {
            return Err(DeployModuleError::DuplicateModule(module_reference));
        }
        self.modules.insert(module_reference, Arc::new(artifact));
        Ok(SuccessfulModuleDeployment {
            module_reference,
            energy,
            transaction_fee,
        })
    }

    /// Deploy a raw wasm module, i.e. one **without** the prefix of 4 version
    /// bytes and 4 module length bytes.
    /// The module still has to a valid V1 smart contract module.
    ///
    /// - `sender`: The account paying for the transaction.
    /// - `module_path`: Path to a module file.
    pub fn module_deploy_wasm_v1<P: AsRef<Path>>(
        &mut self,
        sender: AccountAddress,
        module_path: P,
    ) -> Result<SuccessfulModuleDeployment, DeployModuleError> {
        // Load file
        let file_contents = std::fs::read(module_path)?;
        let wasm_module = WasmModule {
            version: WasmVersion::V1,
            source:  ModuleSource::from(file_contents),
        };
        self.module_deploy_aux(sender, wasm_module)
    }

    /// Deploy a v1 wasm module as it is output from `cargo concordium build`,
    /// i.e. **including** the prefix of 4 version bytes and 4 module length
    /// bytes.
    ///
    /// - `sender`: The account paying for the transaction.
    /// - `module_path`: Path to a module file.
    pub fn module_deploy_v1<P: AsRef<Path>>(
        &mut self,
        sender: AccountAddress,
        module_path: P,
    ) -> Result<SuccessfulModuleDeployment, DeployModuleError> {
        // Load file
        let file_contents = std::fs::read(module_path)?;
        let mut cursor = std::io::Cursor::new(file_contents);
        let wasm_module: WasmModule = common::Deserial::deserial(&mut cursor)?;

        if wasm_module.version != WasmVersion::V1 {
            return Err(DeployModuleError::UnsupportedModuleVersion(
                wasm_module.version,
            ));
        }
        self.module_deploy_aux(sender, wasm_module)
    }

    /// Initialize a contract.
    ///
    /// - `sender`: The account paying for the transaction. Will also become the
    ///   owner of the instance created.
    /// - `module_reference`: The reference to the a module that has already
    ///   been deployed.
    /// - `contract_name`: Name of the contract to initialize.
    /// - `parameter`: Parameter provided to the init method.
    /// - `amount`: The initial balance of the contract. Subtracted from the
    ///   `sender` account.
    /// - `energy_reserved`: Amount of energy reserved for executing the init
    ///   method.
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
                energy: Chain::to_interpreter_energy(energy_reserved),
            },
            false,
            loader,
        )?;
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
                let energy_used = energy_reserved
                    - Chain::from_interpreter_energy(InterpreterEnergy {
                        energy: remaining_energy,
                    });
                transaction_fee += self.calculate_energy_cost(energy_used);

                let mut collector = v1::trie::SizeCollector::default();

                let contract_instance = ContractInstance {
                    module_reference,
                    contract_name: contract_name.to_owned(),
                    state: state.freeze(&mut loader, &mut collector), // TODO: Charge for storage.
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
                let energy_used = energy_reserved
                    - Chain::from_interpreter_energy(InterpreterEnergy {
                        energy: remaining_energy,
                    });
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
                let energy_used = energy_reserved
                    - Chain::from_interpreter_energy(InterpreterEnergy {
                        energy: remaining_energy,
                    });
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
                    FailedContractInteraction::OutOfEnergy {
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
        parameter: Parameter,
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

        let contract_name = instance.contract_name.clone();

        // Construct the instance state
        let mut loader = v1::trie::Loader::new(&[][..]);
        let mut changeset = self.instance_changeset(address);
        let mut mutable_state = changeset.state.make_fresh_generation(&mut loader);
        let inner = mutable_state.get_inner(&mut loader);
        let instance_state = v1::InstanceState::new(loader, inner);

        // Get the initial result from invoking receive
        let res = v1::invoke_receive(
            artifact,
            receive_ctx,
            v1::ReceiveInvocation {
                amount,
                receive_name: receive_name.as_receive_name(),
                parameter: &parameter.0,
                energy: Chain::to_interpreter_energy(remaining_energy),
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
            contract_name,
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
            Parameter(&parameter.0),
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
                    remaining_energy, /* TODO: Could we change this from `u64` to
                                       * `InterpreterEnergy` in chain_integration? */
                } => {
                    let energy_used = energy_reserved
                        - Chain::from_interpreter_energy(InterpreterEnergy {
                            energy: remaining_energy,
                        });
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
                    let energy_used = energy_reserved
                        - Chain::from_interpreter_energy(InterpreterEnergy {
                            energy: remaining_energy,
                        });
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
                    let energy_used = energy_reserved
                        - Chain::from_interpreter_energy(InterpreterEnergy {
                            energy: remaining_energy,
                        });
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
                        FailedContractInteraction::OutOfEnergy {
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
                Err(ContractUpdateError::InterpreterError(e))
            }
        };

        // Handle rollback
        if res.is_err() {
            self.accounts = accounts_backup;
            self.contracts = contracts_backup;
        }

        let mut loader = v1::trie::Loader::new(&[][..]);
        let mut collector = SizeCollector::default();
        for (addr, changeset) in self.instance_changesets.iter_mut() {
            self.contracts.get_mut(addr).expect("Must exist").state =
                changeset.state.freeze(&mut loader, &mut collector);
        }
        self.instance_changesets.clear();
        // TODO: Charge for size in collector;

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
            artifact,
            receive_ctx,
            v1::ReceiveInvocation {
                amount,
                receive_name: receive_name.as_receive_name(),
                parameter: &parameter.0,
                energy: Chain::to_interpreter_energy(energy_reserved),
            },
            instance_state,
            v1::ReceiveParams {
                max_parameter_size:           65535,
                limit_logs_and_return_values: false,
                support_queries:              true,
            },
        )?;

        match res {
            v1::ReceiveResult::Success {
                logs,
                state_changed,
                return_value,
                remaining_energy,
            } => {
                let energy_used = energy_reserved
                    - Chain::from_interpreter_energy(InterpreterEnergy {
                        energy: remaining_energy,
                    });
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
                let energy_used = energy_reserved
                    - Chain::from_interpreter_energy(InterpreterEnergy {
                        energy: remaining_energy,
                    });
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
                let energy_used = energy_reserved
                    - Chain::from_interpreter_energy(InterpreterEnergy {
                        energy: remaining_energy,
                    });
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
                    FailedContractInteraction::OutOfEnergy {
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

    /// Precondition: `address` exists in state.contracts.
    fn instance_changeset(&mut self, address: ContractAddress) -> InstanceChangeSet {
        self.instance_changesets
            .entry(address)
            .or_insert(InstanceChangeSet::from_state(
                self.contracts[&address].state.thaw(),
            ))
            .clone()
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

    /// Convert [`Energy`] to [`InterpreterEnergy`] by multiplying by `1000`.
    fn to_interpreter_energy(energy: Energy) -> InterpreterEnergy {
        InterpreterEnergy {
            energy: energy.energy * 1000,
        }
    }

    /// Convert [`InterpreterEnergy`] to [`Energy`] by dividing by `1000`.
    fn from_interpreter_energy(interpreter_energy: InterpreterEnergy) -> Energy {
        Energy {
            energy: interpreter_energy.energy / 1000,
        }
    }

    pub fn lookup_module_cost(&self, artifact: &ArtifactV1) -> Energy {
        // TODO: Is it just the `.code`?
        // Comes from Concordium/Cost.hs::lookupModule
        Energy::from(artifact.code.len() as u64 / 50)
    }

    /// Returns an Arc clone of the artifact.
    fn get_artifact(&self, module_ref: ModuleReference) -> Result<Arc<ArtifactV1>, ModuleMissing> {
        let artifact = self
            .modules
            .get(&module_ref)
            .ok_or(ModuleMissing(module_ref))?;
        Ok(Arc::clone(artifact))
    }

    fn get_instance(
        &self,
        address: ContractAddress,
    ) -> Result<&ContractInstance, ContractInstanceMissing> {
        self.contracts
            .get(&address)
            .ok_or(ContractInstanceMissing(address))
    }

    fn get_instance_mut(
        &mut self,
        address: ContractAddress,
    ) -> Result<&mut ContractInstance, ContractInstanceMissing> {
        self.contracts
            .get_mut(&address)
            .ok_or(ContractInstanceMissing(address))
    }

    fn get_account(&self, address: AccountAddress) -> Result<&AccountInfo, AccountMissing> {
        self.accounts.get(&address).ok_or(AccountMissing(address))
    }

    fn get_account_mut(
        &mut self,
        address: AccountAddress,
    ) -> Result<&mut AccountInfo, AccountMissing> {
        self.accounts
            .get_mut(&address)
            .ok_or(AccountMissing(address))
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
                        // let instance = self
                        //     .chain
                        //     .get_instance_mut(self.address)
                        //     .expect("Instance known to exist");
                        // let mut collector = v1::trie::SizeCollector::default();
                        self.chain.instance_changeset(self.address).state =
                            self.mutable_state.clone();
                        // instance.state =
                        //     self.mutable_state.freeze(&mut self.loader, &mut
                        // collector); TODO: Charge
                        // energy for this
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

                    // Create the interrupt event, which will be included for transfers, calls, and
                    // upgrades, but not for the remaining interrupts.
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
                                    let instance_new_balance = match (
                                        self.chain.accounts.get_mut(&to),
                                        self.chain.contracts.get_mut(&self.address),
                                    ) {
                                        (Some(acc), Some(contr)) => {
                                            contr.self_balance -= amount;
                                            acc.balance += amount;
                                            contr.self_balance
                                        }
                                        _ => anyhow::bail!(
                                            "Contract or Account missing when they are known to \
                                             exist."
                                        ),
                                    };

                                    // Add transfer event
                                    self.chain_events.push(ChainEvent::Transferred {
                                        from: self.address,
                                        amount,
                                        to,
                                    });

                                    InvokeResponse::Success {
                                        new_balance: instance_new_balance,
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
                                // let mut collector = SizeCollector::default();
                                let mut loader = v1::trie::Loader::new(&[][..]);
                                // Make new generation so that we might roll back.
                                self.chain.instance_changeset(self.address).state =
                                    self.mutable_state.make_fresh_generation(&mut loader);
                                // let persistent_state =
                                //     self.mutable_state.freeze(&mut
                                // self.loader, &mut collector);
                                // TODO: Charge for size of new state.
                                // self.chain.get_instance_mut(address)?.state =
                                // persistent_state;
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
                                Parameter(&parameter),
                                amount,
                                self.invoker_amount_reserved_for_nrg,
                                Chain::from_interpreter_energy(InterpreterEnergy {
                                    energy: remaining_energy,
                                }),
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
                                self.chain.instance_changeset(self.address).state.clone();

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
                        v1::Interrupt::Upgrade { module_ref } => {
                            println!("Upgrading contract to {:?}", module_ref);

                            // Add the interrupt event.
                            self.chain_events.push(interrupt_event);

                            // Charge a base cost.
                            let mut energy_after_invoke = remaining_energy
                                - Chain::to_interpreter_energy(
                                    INITIALIZE_CONTRACT_INSTANCE_BASE_COST,
                                )
                                .energy;

                            let response = match self.chain.modules.get(&module_ref) {
                                None => InvokeResponse::Failure {
                                    kind: v1::InvokeFailure::UpgradeInvalidModuleRef,
                                },
                                Some(artifact) => {
                                    // Charge for the module lookup.
                                    energy_after_invoke -= Chain::to_interpreter_energy(
                                        self.chain.lookup_module_cost(&artifact),
                                    )
                                    .energy;

                                    if artifact.export.contains_key(
                                        self.contract_name.as_contract_name().get_chain_name(),
                                    ) {
                                        let instance = self.chain.get_instance_mut(self.address)?;
                                        let old_module_ref = instance.module_reference;
                                        // Update module reference for the instance.
                                        instance.module_reference = module_ref;

                                        // Charge for the initialization cost.
                                        energy_after_invoke -= Chain::to_interpreter_energy(
                                            INITIALIZE_CONTRACT_INSTANCE_CREATE_COST,
                                        )
                                        .energy;

                                        let upgrade_event = ChainEvent::Upgraded {
                                            address: self.address,
                                            from:    old_module_ref,
                                            to:      module_ref,
                                        };

                                        self.chain_events.push(upgrade_event);

                                        InvokeResponse::Success {
                                            new_balance: instance.self_balance,
                                            data:        None,
                                        }
                                    } else {
                                        InvokeResponse::Failure {
                                            kind: v1::InvokeFailure::UpgradeInvalidContractName,
                                        }
                                    }
                                }
                            };

                            let success = matches!(response, InvokeResponse::Success { .. });
                            self.chain_events.push(ChainEvent::Resumed {
                                address: self.address,
                                success,
                            });

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

                            let energy_after_invoke = remaining_energy
                                - Chain::to_interpreter_energy(
                                    CONTRACT_INSTANCE_QUERY_ACCOUNT_BALANCE_COST,
                                )
                                .energy;

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

                            let energy_after_invoke = remaining_energy
                                - Chain::to_interpreter_energy(
                                    CONTRACT_INSTANCE_QUERY_CONTRACT_BALANCE_COST,
                                )
                                .energy;

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

                            let energy_after_invoke = remaining_energy
                                - Chain::to_interpreter_energy(
                                    CONTRACT_INSTANCE_QUERY_EXCHANGE_RATE_COST,
                                )
                                .energy;

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
#[error("Module {:?} does not exist.", 0)]
pub struct ModuleMissing(ModuleReference);

#[derive(Debug, Error)]
#[error("Contract instance {0} does not exist.")]
pub struct ContractInstanceMissing(ContractAddress);

#[derive(Debug, Error)]
#[error("Account {0} does not exist.")]
pub struct AccountMissing(AccountAddress);

#[derive(Clone)]
pub struct AccountInfo {
    /// The account balance. TODO: Do we need the three types of balances?
    pub balance:     Amount,
    /// Account policies.
    policies:        v0::OwnedPolicyBytes,
    /// The number of signatures. The number of signatures affect the cost of
    /// every transaction for the account.
    signature_count: u32,
}

pub struct TestPolicies(v0::OwnedPolicyBytes);

impl TestPolicies {
    // TODO: Make correctly structured policies ~= Vec<Tuple<Credential,
    // PolicyBytes>>.
    pub fn empty() -> Self { Self(v0::OwnedPolicyBytes::new()) }

    // TODO: Add helper functions for creating arbitrary valid policies.
}

impl AccountInfo {
    /// Create a new [`Self`] with the provided parameters.
    /// The `signature_count` must be >= 1 for transaction costs to be
    /// realistic.
    pub fn new_with_policy_and_signature_count(
        balance: Amount,
        policies: TestPolicies,
        signature_count: u32,
    ) -> Self {
        Self {
            balance,
            policies: policies.0,
            signature_count,
        }
    }

    /// Create new [`Self`] with empty account policies but the provided
    /// `signature_count`. The `signature_count` must be >= 1 for transaction
    /// costs to be realistic.
    pub fn new_with_signature_count(balance: Amount, signature_count: u32) -> Self {
        Self {
            signature_count,
            ..Self::new(balance)
        }
    }

    /// Create new [`Self`] with empty account policies and a signature
    /// count of `1`.
    pub fn new_with_policy(balance: Amount, policies: TestPolicies) -> Self {
        Self {
            balance,
            policies: policies.0,
            signature_count: 1,
        }
    }

    /// Create new [`Self`] with empty account policies and a signature
    /// count of `1`.
    pub fn new(balance: Amount) -> Self { Self::new_with_policy(balance, TestPolicies::empty()) }
}

#[derive(Debug, Error)]
pub enum ContractInitError {
    /// Initialization failed for a reason that also exists on the chain.
    #[error("failed due to a valid chain error: {:?}", 0)]
    ValidChainError(FailedContractInteraction),
    /// An error thrown by the interpreter.
    #[error("an error occured in the interpreter: {:?}", 0)]
    InterpreterError(#[from] anyhow::Error),
    /// Module has not been deployed in test environment.
    #[error("module {:?} does not exist", 0.0)]
    ModuleDoesNotExist(#[from] ModuleMissing),
    /// Account has not been created in test environment.
    #[error("account {} does not exist", 0.0)]
    AccountDoesNotExist(#[from] AccountMissing),
    /// The account does not have enough funds to pay for the energy.
    #[error("account does not have enough funds to pay for the energy")]
    InsufficientFunds,
}

#[derive(Debug, Error)]
pub enum ContractUpdateError {
    /// Update failed for a reason that also exists on the chain.
    #[error("failed due to a valid chain error: {:?}", 0)]
    ValidChainError(FailedContractInteraction),
    /// An error thrown by the wasm interpreter
    #[error("an error occured in the interpreter: {:?}", 0)]
    InterpreterError(#[from] anyhow::Error),
    /// Module has not been deployed in test environment.
    #[error("module {:?} does not exist", 0.0)]
    ModuleDoesNotExist(#[from] ModuleMissing),
    /// Contract instance has not been initialized in test environment.
    #[error("instance {} does not exist", 0.0)]
    InstanceDoesNotExist(#[from] ContractInstanceMissing),
    /// Entrypoint does not exist and neither does the fallback entrypoint.
    #[error("entrypoint does not exist")]
    EntrypointDoesNotExist,
    /// Account has not been created in test environment.
    #[error("account {} does not exist", 0.0)]
    AccountDoesNotExist(#[from] AccountMissing),
    /// The account does not have enough funds to pay for the energy.
    #[error("account does not have enough funds to pay for the energy")]
    InsufficientFunds,
}

// TODO: Implementing (Partial)Eq for this and the other error/success types
// would be nice. But `anyhow::Error` does not implement (Partial)Eq.
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
    OutOfEnergy {
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
            FailedContractInteraction::OutOfEnergy {
                transaction_fee, ..
            } => *transaction_fee,
        }
    }

    pub fn logs(&self) -> &v0::Logs {
        match self {
            FailedContractInteraction::Reject { logs, .. } => logs,
            FailedContractInteraction::Trap { logs, .. } => logs,
            FailedContractInteraction::OutOfEnergy { logs, .. } => logs,
        }
    }
}

#[derive(Debug)]
pub struct ContractError(Vec<u8>);

// TODO: Can we get Eq for this when using io::Error?
// TODO: Should this also have the energy used?
#[derive(Debug, Error)]
pub enum DeployModuleError {
    #[error("could not read the file due to: {0}")]
    ReadFileError(#[from] std::io::Error),
    #[error("module is invalid due to: {0}")]
    InvalidModule(#[from] anyhow::Error),
    #[error("account does not have sufficient funds to pay for the energy")]
    InsufficientFunds,
    #[error("account {} does not exist", 0.0)]
    AccountDoesNotExist(#[from] AccountMissing),
    #[error("wasm version {0} is not supported")]
    UnsupportedModuleVersion(WasmVersion),
    #[error("module with reference {:?} already exists", 0)]
    DuplicateModule(ModuleReference),
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
    /// The logs produced since the last interrupt.
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

    pub fn from_typed<T: Serial>(parameter: &T) -> Self { Self(to_bytes(parameter)) }
}

#[cfg(test)]
mod tests {
    use super::*;

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
            .module_deploy_v1(ACC_0, "examples/icecream/icecream.wasm.v1")
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
            .module_deploy_v1(ACC_0, "examples/icecream/icecream.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_weather"),
                ContractParameter::from_bytes(vec![0u8]),
                Amount::zero(),
                Energy::from(10000),
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
            .module_deploy_v1(ACC_0, "examples/icecream/icecream.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_weather"),
                ContractParameter::from_bytes(vec![99u8]), // Invalid param
                Amount::zero(),
                Energy::from(10000),
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
            .module_deploy_v1(ACC_0, "examples/icecream/icecream.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_weather"),
                ContractParameter::from_bytes(vec![0u8]), // Starts as 0
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");

        let res_update = chain
            .contract_update(
                ACC_0,
                res_init.contract_address,
                EntrypointName::new_unchecked("set"),
                ContractParameter::from_bytes(vec![1u8]), // Updated to 1
                Amount::zero(),
                Energy::from(10000),
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
            .module_deploy_v1(ACC_0, "examples/integrate/a.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_integrate"),
                ContractParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");

        let res_update = chain
            .contract_update(
                ACC_0,
                res_init.contract_address,
                EntrypointName::new_unchecked("receive"),
                ContractParameter::from_typed(&ACC_1),
                transfer_amount,
                Energy::from(10000),
            )
            .expect("Updating valid contract should work");

        let res_view = chain
            .contract_invoke(
                ACC_0,
                res_init.contract_address,
                EntrypointName::new_unchecked("view"),
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
            .module_deploy_v1(ACC_0, "examples/integrate/a.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_integrate"),
                ContractParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");

        let res_update = chain.contract_update(
            ACC_0,
            res_init.contract_address,
            EntrypointName::new_unchecked("receive"),
            ContractParameter::from_typed(&ACC_1), // We haven't created ACC_1.
            transfer_amount,
            Energy::from(100000),
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
            .module_deploy_v1(ACC_0, "examples/fib/a.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_fib"),
                ContractParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");

        let res_update = chain
            .contract_update(
                ACC_0,
                res_init.contract_address,
                EntrypointName::new_unchecked("receive"),
                ContractParameter::from_typed(&6u64),
                Amount::zero(),
                Energy::from(4000000),
            )
            .expect("Updating valid contract should work");

        let res_view = chain
            .contract_invoke(
                ACC_0,
                res_init.contract_address,
                EntrypointName::new_unchecked("view"),
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
            .module_deploy_v1(ACC_0, "examples/integrate/a.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_integrate"),
                ContractParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");

        let res_update = chain
            .contract_update(
                ACC_0,
                res_init.contract_address,
                EntrypointName::new_unchecked("recurse"),
                ContractParameter::from_typed(&10u32),
                Amount::zero(),
                Energy::from(1000000),
            )
            .expect("Updating valid contract should work");

        let res_view = chain
            .contract_invoke(
                ACC_0,
                res_init.contract_address,
                EntrypointName::new_unchecked("view"),
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
            .module_deploy_v1(ACC_0, "examples/integrate/a.wasm.v1")
            .expect("Deploying valid module should work");

        let input_param: u32 = 8;

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_integrate"),
                ContractParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");

        let res_update = chain
            .contract_update(
                ACC_0,
                res_init.contract_address,
                EntrypointName::new_unchecked("inc-fail-on-zero"),
                ContractParameter::from_typed(&input_param),
                Amount::zero(),
                Energy::from(100000000),
            )
            .expect("Updating valid contract should work");

        let res_view = chain
            .contract_invoke(
                ACC_0,
                res_init.contract_address,
                EntrypointName::new_unchecked("view"),
                ContractParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
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
                .module_deploy_wasm_v1(
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
                    Energy::from(10000),
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
                    Energy::from(100000),
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
            .module_deploy_wasm_v1(ACC_0, format!("{}/queries-account-balance.wasm", WASM_TEST_FOLDER)) // TODO: Add wasm files to the repo for tests.
            .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let update_amount = Amount::from_ccd(123);
            let energy_limit = Energy::from(100000);
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
                .module_deploy_wasm_v1(
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
                    Energy::from(10000),
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
                .module_deploy_wasm_v1(
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
                    Energy::from(10000),
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
                    Energy::from(100000),
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
                .module_deploy_wasm_v1(
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
                    Energy::from(10000),
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
                    Energy::from(100000),
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
                .module_deploy_wasm_v1(
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
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_init_other = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    init_amount, // Set up another contract with `init_amount` balance
                    Energy::from(10000),
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
                    Energy::from(100000),
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
                .module_deploy_wasm_v1(
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
                    Energy::from(10000),
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
                    Energy::from(100000),
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
                .module_deploy_wasm_v1(
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
                    Energy::from(10000),
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
                    Energy::from(100000),
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
                .module_deploy_wasm_v1(
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
                    Energy::from(10000),
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
                    Energy::from(100000),
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
                .module_deploy_wasm_v1(
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
                    Energy::from(10000),
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
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }
    }

    mod contract_upgrade {

        use super::*;

        /// Test a basic upgrade, ensuring that the new module is in place by
        /// checking the available entrypoints.
        #[test]
        fn test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            // Deploy the two modules `upgrading_0`, `upgrading_1`
            let res_deploy_0 = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/upgrading_0.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_deploy_1 = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/upgrading_1.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            // Initialize `upgrading_0`.
            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy_0.module_reference,
                    ContractName::new_unchecked("init_a"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            // Upgrade the contract to the `upgrading_1` module by calling the `bump`
            // entrypoint.
            let res_update_upgrade = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("bump"),
                    ContractParameter::from_typed(&res_deploy_1.module_reference),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            // Call the `newfun` entrypoint which only exists in `upgrading_1`.
            let res_update_new = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("newfun"),
                    ContractParameter::from_typed(&res_deploy_1.module_reference),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating the `newfun` from the `upgrading_1` module should work");

            assert!(matches!(res_update_upgrade.chain_events[..], [
                ChainEvent::Interrupted { .. },
                ChainEvent::Upgraded { from, to, .. },
                ChainEvent::Resumed { .. },
                ChainEvent::Updated { .. },
            ] if from == res_deploy_0.module_reference && to == res_deploy_1.module_reference));
            assert!(matches!(res_update_new.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }

        /// The contract in this test, triggers an upgrade and then in the same
        /// invocation, calls a function in the upgraded module.
        /// Checking the new module is being used.
        #[test]
        fn test_self_invoke() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy_0 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-self-invoke0.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");
            let res_deploy_1 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-self-invoke1.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy_0.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    ContractParameter::from_typed(&res_deploy_1.module_reference),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                // Invoking `contract.name`
                ChainEvent::Interrupted { .. },
                ChainEvent::Updated { .. },
                ChainEvent::Resumed { .. },
                // Making the upgrade
                ChainEvent::Interrupted { .. },
                ChainEvent::Upgraded { .. },
                ChainEvent::Resumed { .. },
                // Invoking contract.name again
                ChainEvent::Interrupted { .. },
                ChainEvent::Updated { .. },
                ChainEvent::Resumed { .. },
                // The successful update
                ChainEvent::Updated { .. },
            ]));
        }

        /// Test upgrading to a module that doesn't exist (it uses module
        /// `[0u8;32]` inside the contract). The contract checks whether
        /// the expected error is returned.
        #[test]
        fn test_missing_module() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-missing-module.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Interrupted { .. },
                // No upgrade event, as it is supposed to fail.
                ChainEvent::Resumed { success, .. },
                ChainEvent::Updated { .. },
            ] if success == false));
        }

        /// Test upgrading to a module where there isn't a matching contract
        /// name. The contract checks whether the expected error is
        /// returned.
        #[test]
        fn test_missing_contract() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy_0 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-missing-contract0.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_deploy_1 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-missing-contract1.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy_0.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    ContractParameter::from_typed(&res_deploy_1.module_reference),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Interrupted { .. },
                // No upgrade event, as it is supposed to fail.
                ChainEvent::Resumed { success, .. },
                ChainEvent::Updated { .. },
            ] if success == false));
        }

        /// Test upgrading twice in the same transaction. The effect of the
        /// second upgrade should be in effect at the end.
        #[test]
        fn test_twice_in_one_transaction() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy_0 = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/upgrading-twice0.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_deploy_1 = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/upgrading-twice1.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_deploy_2 = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/upgrading-twice2.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy_0.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let input_param = (res_deploy_1.module_reference, res_deploy_2.module_reference);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    ContractParameter::from_typed(&input_param),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                // Invoke the contract itself to check the name entrypoint return value.
                ChainEvent::Interrupted { .. },
                ChainEvent::Updated { .. },
                ChainEvent::Resumed { .. },
                // Upgrade from module 0 to 1
                ChainEvent::Interrupted { .. },
                ChainEvent::Upgraded { from: first_from, to: first_to, .. },
                ChainEvent::Resumed { .. },
                // Invoke the contract itself to check the name again.
                ChainEvent::Interrupted { .. },
                ChainEvent::Updated { .. },
                ChainEvent::Resumed { .. },
                // Upgrade again
                ChainEvent::Interrupted { .. },
                ChainEvent::Upgraded { from: second_from, to: second_to, .. },
                ChainEvent::Resumed { .. },
                // Invoke itself again to check name a final time.
                ChainEvent::Interrupted { .. },
                ChainEvent::Updated { .. },
                ChainEvent::Resumed { .. },
                // Final update event
                ChainEvent::Updated { .. },
            ] if first_from == res_deploy_0.module_reference
                && first_to == res_deploy_1.module_reference
                && second_from == res_deploy_1.module_reference
                && second_to == res_deploy_2.module_reference));
        }

        /// Test upgrading to a module where there isn't a matching contract
        /// name. The contract checks whether the expected error is
        /// returned.
        #[test]
        fn test_chained_contract() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-chained0.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let number_of_upgrades: u32 = 82; // TODO: Stack will overflow if larger than 82.
            let input_param = (number_of_upgrades, res_deploy.module_reference);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    ContractParameter::from_typed(&input_param),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect("Updating valid contract should work");

            // Per upgrade: 3 events for invoking itself + 3 events for the upgrade.
            // Ends with 4 extra events: 3 events for an upgrade and 1 event for succesful
            // update.
            assert_eq!(
                res_update.chain_events.len() as u32,
                6 * number_of_upgrades + 4
            )
        }

        /// Tests whether a contract which triggers a succesful upgrade,
        /// but rejects the transaction from another cause, rollbacks the
        /// upgrade as well.
        #[test]
        fn test_reject() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy_0 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-reject0.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_deploy_1 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-reject1.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy_0.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update_upgrade = chain.contract_update(
                ACC_0,
                res_init.contract_address,
                EntrypointName::new_unchecked("upgrade"),
                ContractParameter::from_typed(&res_deploy_1.module_reference),
                Amount::zero(),
                Energy::from(1000000),
            );

            let res_update_new_feature = chain.contract_update(
                ACC_0,
                res_init.contract_address,
                EntrypointName::new_unchecked("new_feature"),
                ContractParameter::empty(),
                Amount::zero(),
                Energy::from(1000000),
            );

            // Check the return value manually returned by the contract.
            assert!(matches!(res_update_upgrade,
                         Err(ContractUpdateError::ValidChainError(FailedContractInteraction::Reject { reason, ..}))
                         if reason == -1));

            // Assert that the new_feature entrypoint doesn't exist since the upgrade
            // failed.
            assert!(matches!(
            res_update_new_feature,
            Err(ContractUpdateError::InterpreterError(e)) if e.to_string() == "Entrypoint does not exist."
            ));
        }

        /// Tests calling an entrypoint introduced by an upgrade of the module
        /// can be called and whether an entrypoint removed by an upgrade fail
        /// with the appropriate reject reason.
        #[test]
        fn test_changing_entrypoint() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy_0 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-changing-entrypoints0.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_deploy_1 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-changing-entrypoints1.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy_0.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update_old_feature_0 = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("old_feature"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect("Updating old_feature on old module should work.");

            let res_update_new_feature_0 = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("new_feature"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect_err("Updating new_feature on old module should _not_ work");

            let res_update_upgrade = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    ContractParameter::from_typed(&res_deploy_1.module_reference),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect("Upgrading contract should work.");

            let res_update_old_feature_1 = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("old_feature"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect_err("Updating old_feature on _new_ module should _not_ work.");

            let res_update_new_feature_1 = chain
                .contract_update(
                    ACC_0,
                    res_init.contract_address,
                    EntrypointName::new_unchecked("new_feature"),
                    ContractParameter::empty(),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect("Updating new_feature on _new_ module should work");

            assert!(matches!(res_update_old_feature_0.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
            assert!(
                matches!(res_update_new_feature_0, ContractUpdateError::InterpreterError(e) if e.to_string() == "Entrypoint does not exist.")
            );
            assert!(matches!(res_update_upgrade.chain_events[..], [
                ChainEvent::Interrupted { .. },
                ChainEvent::Upgraded { .. },
                ChainEvent::Resumed { .. },
                ChainEvent::Updated { .. },
            ]));
            assert!(
                matches!(res_update_old_feature_1, ContractUpdateError::InterpreterError(e) if e.to_string() == "Entrypoint does not exist.")
            );
            assert!(matches!(res_update_new_feature_1.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }
    }
}
