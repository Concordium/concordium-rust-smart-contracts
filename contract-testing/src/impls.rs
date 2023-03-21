use crate::{constants, invocation::EntrypointInvocationHandler, types::*};
use anyhow::anyhow;
use concordium_base::{
    base::{self, Energy, OutOfEnergy},
    common::{self, to_bytes},
    constants::{MAX_ALLOWED_INVOKE_ENERGY, MAX_WASM_MODULE_SIZE},
    contracts_common::{
        self, AccountAddress, AccountBalance, Address, Amount, ChainMetadata, ContractAddress,
        ExchangeRate, ModuleReference, SlotTime, Timestamp,
    },
    smart_contracts::{ModuleSource, WasmModule, WasmVersion},
    transactions::{self, cost, InitContractPayload, UpdateContractPayload},
};
use concordium_smart_contract_engine::{v0, v1, InterpreterEnergy};
use num_bigint::BigUint;
use std::{collections::BTreeMap, path::Path, sync::Arc};

impl Default for Chain {
    fn default() -> Self { Self::new() }
}

impl Chain {
    /// Create a new [`Self`] where all the configurable parameters are
    /// provided.
    ///
    /// Returns an error if the exchange rates provided makes one energy cost
    /// more than `u64::MAX / MAX_ALLOWED_INVOKE_ENERGY`.
    pub fn new_with_time_and_rates(
        block_time: SlotTime,
        micro_ccd_per_euro: ExchangeRate,
        euro_per_energy: ExchangeRate,
    ) -> Result<Self, ExchangeRateError> {
        // Ensure the exchange rates are within a valid range.
        check_exchange_rates(euro_per_energy, micro_ccd_per_euro)?;

        Ok(Self {
            block_time,
            micro_ccd_per_euro,
            euro_per_energy,
            accounts: BTreeMap::new(),
            modules: BTreeMap::new(),
            contracts: BTreeMap::new(),
            next_contract_index: 0,
        })
    }

    /// Create a new [`Self`] with a specified `block_time` where
    ///  - `micro_ccd_per_euro` defaults to `147235241 / 1`
    ///  - `euro_per_energy` defaults to `1 / 50000`.
    pub fn new_with_time(block_time: SlotTime) -> Self {
        Self {
            block_time,
            ..Self::new()
        }
    }

    /// Create a new [`Self`] where
    ///  - `block_time` defaults to `0`,
    ///  - `micro_ccd_per_euro` defaults to `50000 / 1`
    ///  - `euro_per_energy` defaults to `1 / 50000`.
    ///
    /// With these exchange rates, one energy costs one microCCD.
    pub fn new() -> Self {
        Self::new_with_time_and_rates(
            Timestamp::from_timestamp_millis(0),
            ExchangeRate::new_unchecked(50000, 1),
            ExchangeRate::new_unchecked(1, 50000),
        )
        .expect("Rates known to be within range.")
    }

    /// Deploy a smart contract module.
    ///
    /// The `WasmModule` can be loaded from disk with either
    /// [`Chain::load_module_v1`] or [`Chain::load_module_v1_raw`].
    ///
    /// Parameters:
    ///  - `sender`: the sender account.
    ///  - `module`: the v1 wasm module.
    pub fn module_deploy_v1(
        &mut self,
        sender: AccountAddress,
        wasm_module: WasmModule,
    ) -> Result<SuccessfulModuleDeployment, ModuleDeployError> {
        // Ensure sender account exists.
        if !self.account_exists(sender) {
            return Err(ModuleDeployError {
                kind:            ModuleDeployErrorKind::SenderDoesNotExist(AccountDoesNotExist {
                    address: sender,
                }),
                energy_used:     0.into(),
                transaction_fee: Amount::zero(),
            });
        }

        let check_header_energy = {
            // +1 for the tag, +8 for size and version
            let payload_size = 1
                + 8
                + wasm_module.source.size()
                + transactions::construct::TRANSACTION_HEADER_SIZE;
            let number_of_sigs = self
                .account(sender)
                .expect("existence already checked")
                .signature_count;
            cost::base_cost(payload_size, number_of_sigs)
        };
        let check_header_cost = self.calculate_energy_cost(check_header_energy);

        if self
            .account(sender)
            .expect("existence already checked")
            .balance
            .available()
            < check_header_cost
        {
            return Err(ModuleDeployError {
                kind:            ModuleDeployErrorKind::InsufficientFunds,
                energy_used:     0.into(),
                transaction_fee: Amount::zero(),
            });
        }

        // Only v1 modules are supported in this testing library.
        if wasm_module.version != WasmVersion::V1 {
            return Err(ModuleDeployError {
                kind:            ModuleDeployErrorKind::UnsupportedModuleVersion(
                    wasm_module.version,
                ),
                energy_used:     0.into(),
                transaction_fee: Amount::zero(),
            });
        }

        let account = self.account_mut(sender).expect("existence already checked");

        // TODO: Ensure that this matches the node for both invalid and valid modules.
        // to_ccd(header_cost) + to_ccd(deploy_cost) != to_ccd(header_cost +
        // deploy_cost).
        account.balance.total -= check_header_cost;

        // Construct the artifact.
        let artifact =
            match concordium_wasm::utils::instantiate_with_metering::<v1::ProcessedImports, _>(
                &v1::ConcordiumAllowedImports {
                    support_upgrade: true,
                },
                wasm_module.source.as_ref(),
            ) {
                Ok(artifact) => artifact,
                Err(err) => {
                    return Err(ModuleDeployError {
                        kind:            ModuleInvalidError(err).into(),
                        energy_used:     check_header_energy,
                        transaction_fee: check_header_cost,
                    })
                }
            };

        // Calculate the deploy module cost.
        let deploy_module_energy = cost::deploy_module(wasm_module.source.size());
        let deploy_module_cost = self.calculate_energy_cost(deploy_module_energy);

        // Subtract the cost from the account if it has sufficient funds.
        let account = self.account_mut(sender).expect("existence already checked");
        if account.balance.available() < deploy_module_cost {
            return Err(ModuleDeployError {
                kind:            ModuleDeployErrorKind::InsufficientFunds,
                energy_used:     check_header_energy,
                transaction_fee: check_header_cost,
            });
        };
        account.balance.total -= deploy_module_cost;

        // Save the module.
        let module_reference: ModuleReference = wasm_module.get_module_ref();

        // Ensure module hasn't been deployed before.
        if self.modules.contains_key(&module_reference) {
            return Err(ModuleDeployError {
                kind:            ModuleDeployErrorKind::DuplicateModule(module_reference),
                energy_used:     check_header_energy + deploy_module_energy,
                transaction_fee: check_header_cost + deploy_module_cost,
            });
        }
        self.modules.insert(module_reference, ContractModule {
            size:     wasm_module.source.size(),
            artifact: Arc::new(artifact),
        });
        Ok(SuccessfulModuleDeployment {
            module_reference,
            energy_used: check_header_energy + deploy_module_energy,
            transaction_fee: check_header_cost + deploy_module_cost,
        })
    }

    /// Load a raw wasm module, i.e. one **without** the prefix of 4 version
    /// bytes and 4 module length bytes.
    /// The module still has to be a valid V1 smart contract module.
    pub fn module_load_v1_raw(
        module_path: impl AsRef<Path>,
    ) -> Result<WasmModule, ModuleLoadError> {
        let module_path = module_path.as_ref();
        // To avoid reading a giant file, we open the file for reading, check its size
        // and then load the contents.
        let (mut reader, metadata) = std::fs::File::open(module_path)
            .and_then(|reader| reader.metadata().map(|metadata| (reader, metadata)))
            .map_err(|e| ModuleLoadError {
                path: module_path.to_path_buf(),
                kind: e.into(),
            })?;
        if metadata.len() > MAX_WASM_MODULE_SIZE.into() {
            return Err(ModuleLoadError {
                path: module_path.to_path_buf(),
                kind: ModuleLoadErrorKind::ReadModule(
                    anyhow!("Maximum size of a Wasm module is {}", MAX_WASM_MODULE_SIZE).into(),
                ),
            });
        }
        // We cannot deserialize directly to [`ModuleSource`] as it expects the first
        // four bytes to be the length, which is isn't for this raw file.
        let mut buffer = Vec::new();
        std::io::Read::read_to_end(&mut reader, &mut buffer).map_err(|e| ModuleLoadError {
            path: module_path.to_path_buf(),
            kind: ModuleLoadErrorKind::OpenFile(e.into()), /* This is unlikely to happen, since
                                                            * we already opened it. */
        })?;
        Ok(WasmModule {
            version: WasmVersion::V1,
            source:  ModuleSource::from(buffer),
        })
    }

    /// Load a v1 wasm module as it is output from `cargo concordium build`,
    /// i.e. **including** the prefix of 4 version bytes and 4 module length
    /// bytes.
    pub fn module_load_v1(module_path: impl AsRef<Path>) -> Result<WasmModule, ModuleLoadError> {
        let module_path = module_path.as_ref();
        // To avoid reading a giant file, we just open the file for reading and then
        // parse it as a wasm module, which checks the length up front.
        let mut reader = std::fs::File::open(module_path).map_err(|e| ModuleLoadError {
            path: module_path.to_path_buf(),
            kind: e.into(),
        })?;
        let module: WasmModule = common::from_bytes(&mut reader).map_err(|e| ModuleLoadError {
            path: module_path.to_path_buf(),
            kind: ModuleLoadErrorKind::ReadModule(e.into()),
        })?;
        if module.version != WasmVersion::V1 {
            return Err(ModuleLoadError {
                path: module_path.to_path_buf(),
                kind: ModuleLoadErrorKind::UnsupportedModuleVersion(module.version),
            });
        }
        Ok(module)
    }

    /// Initialize a contract.
    ///
    /// **Parameters:**
    ///  - `sender`: The account paying for the transaction. Will also become
    ///    the owner of the instance created.
    ///  - `energy_reserved`: Amount of energy reserved for executing the init
    ///   method.
    ///  - `payload`:
    ///    - `amount`: The initial balance of the contract. Subtracted from the
    ///      `sender` account.
    ///    - `mod_ref`: The reference to the a module that has already been
    ///      deployed.
    ///    - `init_name`: Name of the contract to initialize.
    ///    - `param`: Parameter provided to the init method.
    pub fn contract_init(
        &mut self,
        sender: AccountAddress,
        energy_reserved: Energy,
        payload: InitContractPayload,
    ) -> Result<ContractInitSuccess, ContractInitError> {
        let mut remaining_energy = energy_reserved;
        if !self.account_exists(sender) {
            return Err(self.from_init_error_kind(
                ContractInitErrorKind::SenderDoesNotExist(AccountDoesNotExist { address: sender }),
                energy_reserved,
                remaining_energy,
            ));
        }

        let res =
            self.contract_init_worker(sender, energy_reserved, payload, &mut remaining_energy);

        let (res, transaction_fee) = match res {
            Ok(s) => {
                let transaction_fee = s.transaction_fee;
                (Ok(s), transaction_fee)
            }
            Err(e) => {
                let err = self.from_init_error_kind(e, energy_reserved, remaining_energy);
                let transaction_fee = err.transaction_fee;
                (Err(err), transaction_fee)
            }
        };

        // Charge the account.
        self.account_mut(sender)
            .expect("existence already checked")
            .balance
            .total -= transaction_fee;
        res
    }

    /// Helper method for initializing contracts, which does most of the actual
    /// work.
    ///
    /// The main reason for splitting init in two is to have this method return
    /// early if it runs out of energy. `contract_init` will then always
    /// ensure to charge the account for the energy used.
    fn contract_init_worker(
        &mut self,
        sender: AccountAddress,
        energy_reserved: Energy,
        payload: InitContractPayload,
        remaining_energy: &mut Energy,
    ) -> Result<ContractInitSuccess, ContractInitErrorKind> {
        // Get the account and check that it has sufficient balance to pay for the
        // reserved_energy and amount.
        let account_info = self.account(sender)?;
        if account_info.balance.available()
            < self.calculate_energy_cost(energy_reserved) + payload.amount
        {
            return Err(ContractInitErrorKind::InsufficientFunds);
        }

        // Ensure that the parameter has a valid size.
        if payload.param.as_ref().len() > contracts_common::constants::MAX_PARAMETER_LEN {
            return Err(ContractInitErrorKind::ParameterTooLarge);
        }

        // Compute the base cost for checking the transaction header.
        let check_header_cost = {
            let pre_account_trx = transactions::construct::init_contract(
                account_info.signature_count,
                sender,
                base::Nonce::from(0), // Value not matter, only used for serialized size.
                common::types::TransactionTime::from_seconds(0), /* Value does not matter, only
                                       * used for serialized size. */
                payload.clone(),
                energy_reserved,
            );
            let transaction_size = to_bytes(&pre_account_trx).len() as u64;
            transactions::cost::base_cost(transaction_size, account_info.signature_count)
        };

        // Charge the header cost.
        remaining_energy.tick_energy(check_header_cost)?;

        // Charge the base cost for initializing a contract.
        remaining_energy.tick_energy(constants::INITIALIZE_CONTRACT_INSTANCE_BASE_COST)?;

        // Lookup module.
        let module = self.contract_module(payload.mod_ref)?;
        let lookup_cost = lookup_module_cost(&module);
        // Charge the cost for looking up the module.
        remaining_energy.tick_energy(lookup_cost)?;

        // Construct the context.
        let init_ctx = v0::InitContext {
            metadata:        ChainMetadata {
                slot_time: self.block_time,
            },
            init_origin:     sender,
            sender_policies: account_info.policies.clone(),
        };
        // Initialize contract
        // We create an empty loader as no caching is used in this testing library
        // presently, so the loader is not used.
        let mut loader = v1::trie::Loader::new(&[][..]);

        let energy_given_to_interpreter = to_interpreter_energy(*remaining_energy);
        let res = v1::invoke_init(
            module.artifact,
            init_ctx,
            v1::InitInvocation {
                amount:    payload.amount,
                init_name: payload.init_name.as_contract_name().get_chain_name(),
                parameter: payload.param.as_ref(),
                energy:    energy_given_to_interpreter,
            },
            false,
            loader,
        );
        // Handle the result
        match res {
            Ok(v1::InitResult::Success {
                logs,
                return_value: _, /* Ignore return value for now, since our tools do not support
                                  * it for inits, currently. */
                remaining_energy: remaining_interpreter_energy,
                mut state,
            }) => {
                let contract_address = self.create_contract_address();
                let mut collector = v1::trie::SizeCollector::default();

                let persisted_state = state.freeze(&mut loader, &mut collector);

                // Perform the subtraction in the more finegrained (*1000) `InterpreterEnergy`,
                // and *then* convert to `Energy`. This is how it is done in the node, and if we
                // swap the operations, it can result in a small discrepancy due to rounding.
                let energy_used_in_interpreter = from_interpreter_energy(
                    energy_given_to_interpreter.saturating_sub(remaining_interpreter_energy),
                );
                remaining_energy.tick_energy(energy_used_in_interpreter)?;

                // Charge one energy per stored state byte.
                let energy_for_state_storage = Energy::from(collector.collect());
                remaining_energy.tick_energy(energy_for_state_storage)?;

                // Charge the constant cost for initializing a contract.
                remaining_energy
                    .tick_energy(constants::INITIALIZE_CONTRACT_INSTANCE_CREATE_COST)?;

                let contract_instance = Contract {
                    module_reference: payload.mod_ref,
                    contract_name:    payload.init_name,
                    state:            persisted_state,
                    owner:            sender,
                    self_balance:     payload.amount,
                };

                // Save the contract instance
                self.contracts.insert(contract_address, contract_instance);

                // Subtract the amount from the invoker.
                self.account_mut(sender)
                    .expect("Account known to exist")
                    .balance
                    .total -= payload.amount;

                let energy_used = energy_reserved - *remaining_energy;
                let transaction_fee = self.calculate_energy_cost(energy_used);

                Ok(ContractInitSuccess {
                    contract_address,
                    logs,
                    energy_used,
                    transaction_fee,
                })
            }
            Ok(v1::InitResult::Reject {
                reason,
                return_value,
                remaining_energy: remaining_interpreter_energy,
            }) => {
                let energy_used_in_interpreter = from_interpreter_energy(
                    energy_given_to_interpreter.saturating_sub(remaining_interpreter_energy),
                );
                remaining_energy.tick_energy(energy_used_in_interpreter)?;
                Err(ContractInitErrorKind::ExecutionError {
                    failure_kind: InitFailure::Reject {
                        reason,
                        return_value,
                    },
                })
            }
            Ok(v1::InitResult::Trap {
                error,
                remaining_energy: remaining_interpreter_energy,
            }) => {
                let energy_used_in_interpreter = from_interpreter_energy(
                    energy_given_to_interpreter.saturating_sub(remaining_interpreter_energy),
                );
                remaining_energy.tick_energy(energy_used_in_interpreter)?;
                Err(ContractInitErrorKind::ExecutionError {
                    failure_kind: InitFailure::Trap {
                        error: ExecutionError(error),
                    },
                })
            }
            Ok(v1::InitResult::OutOfEnergy) => {
                *remaining_energy = Energy::from(0);
                Err(ContractInitErrorKind::ExecutionError {
                    failure_kind: InitFailure::OutOfEnergy,
                })
            }
            Err(err) => Err(ContractInitErrorKind::ExecutionError {
                failure_kind: InitFailure::Trap {
                    error: ExecutionError(err),
                },
            }),
        }
    }

    /// Helper method that handles contract invocation.
    ///
    /// *Preconditions:*
    ///  - `invoker` exists.
    ///  - `sender` exists.
    ///  - `invoker`s balance is >= `amount`.
    fn contract_invocation_worker(
        &mut self,
        invoker: AccountAddress,
        sender: Address,
        energy_reserved: Energy,
        payload: UpdateContractPayload,
        remaining_energy: &mut Energy,
        should_persist: bool,
    ) -> Result<ContractInvocationSuccess, ContractInvocationError> {
        // Ensure that the parameter has a valid size.
        if payload.message.as_ref().len() > contracts_common::constants::MAX_PARAMETER_LEN {
            return Err(self.from_invocation_error_kind(
                ContractInvocationErrorKind::ParameterTooLarge,
                energy_reserved,
                *remaining_energy,
            ));
        }
        let contract_address = payload.address;
        let (result, changeset, chain_events) =
            EntrypointInvocationHandler::invoke_entrypoint_and_get_changes(
                self,
                invoker,
                sender,
                remaining_energy,
                payload,
            )
            .map_err(|_| self.invocation_out_of_energy_error(energy_reserved))?;

        // Get the energy to be charged for extra state bytes. Or return an error if out
        // of energy.
        let state_changed = if result.is_success() {
            let res = if should_persist {
                changeset.persist(
                    *remaining_energy,
                    contract_address,
                    &mut self.accounts,
                    &mut self.contracts,
                )
            } else {
                changeset.collect_energy_for_state(*remaining_energy, contract_address)
            };

            let (energy_for_state_increase, state_changed) =
                res.map_err(|_| self.invocation_out_of_energy_error(energy_reserved))?;

            // Charge for the potential state size increase.
            remaining_energy
                .tick_energy(energy_for_state_increase)
                .map_err(|_| self.invocation_out_of_energy_error(energy_reserved))?;

            state_changed
        } else {
            // An error occured, so state hasn't changed.
            false
        };

        match result.invoke_response {
            v1::InvokeResponse::Success { new_balance, data } => {
                let energy_used = energy_reserved - *remaining_energy;
                let transaction_fee = self.calculate_energy_cost(energy_used);
                Ok(ContractInvocationSuccess {
                    chain_events,
                    energy_used,
                    transaction_fee,
                    return_value: data.unwrap_or_default(),
                    state_changed,
                    new_balance,
                    logs: result.logs,
                })
            }
            v1::InvokeResponse::Failure { kind } => Err(self.from_invocation_error_kind(
                ContractInvocationErrorKind::ExecutionError { failure_kind: kind },
                energy_reserved,
                *remaining_energy,
            )),
        }
    }

    /// Update a contract by calling one of its entrypoints.
    ///
    /// If successful, all changes will be saved.
    ///
    /// **Parameters:**
    ///  - `invoker`: the account paying for the transaction.
    ///  - `sender`: the sender of the transaction, can also be a contract.
    ///  - `contract_address`: the contract to update.
    ///  - `entrypoint`: the entrypoint to call.
    ///  - `parameter`: the contract parameter.
    ///  - `amount`: the amount sent to the contract.
    ///  - `energy_reserved`: the maximum energy that can be used in the update.
    pub fn contract_update(
        &mut self,
        invoker: AccountAddress,
        sender: Address,
        energy_reserved: Energy,
        payload: UpdateContractPayload,
    ) -> Result<ContractInvocationSuccess, ContractInvocationError> {
        // Ensure the invoker exists.
        if !self.account_exists(invoker) {
            return Err(ContractInvocationError {
                energy_used:     Energy::from(0),
                transaction_fee: Amount::zero(),
                kind:            ContractInvocationErrorKind::InvokerDoesNotExist(
                    AccountDoesNotExist { address: invoker },
                ),
            });
        }
        // Ensure the sender exists.
        if !self.address_exists(sender) {
            // TODO: Should we charge the header cost if the invoker exists but the sender
            // doesn't?
            return Err(ContractInvocationError {
                energy_used:     Energy::from(0),
                transaction_fee: Amount::zero(),
                kind:            ContractInvocationErrorKind::SenderDoesNotExist(sender),
            });
        }

        // Get the signature count. TODO: Add as parameter instead?
        let invoker_signature_count = self
            .account_mut(invoker)
            .expect("existence already checked")
            .signature_count;

        // Compute the base cost for checking the transaction header.
        let check_header_cost = {
            let pre_account_trx = transactions::construct::update_contract(
                invoker_signature_count,
                invoker,
                base::Nonce::from(0), // Value does not matter, only used for serialized size.
                common::types::TransactionTime::from_seconds(0), /* Value does not matter, only
                                       * used for serialized size. */
                payload.clone(),
                energy_reserved,
            );
            let transaction_size = to_bytes(&pre_account_trx).len() as u64;
            transactions::cost::base_cost(transaction_size, invoker_signature_count)
        };

        // Charge the header cost.
        let mut remaining_energy =
            energy_reserved
                .checked_sub(check_header_cost)
                .ok_or(ContractInvocationError {
                    energy_used:     Energy::from(0),
                    transaction_fee: Amount::zero(),
                    kind:            ContractInvocationErrorKind::OutOfEnergy,
                })?;

        let invoker_amount_reserved_for_nrg = self.calculate_energy_cost(energy_reserved);
        let account_info = self
            .account_mut(invoker)
            .expect("existence already checked");

        // Ensure the account has sufficient funds to pay for the energy and amount.
        if account_info.balance.available() < invoker_amount_reserved_for_nrg + payload.amount {
            let energy_used = energy_reserved - remaining_energy;
            return Err(ContractInvocationError {
                energy_used,
                transaction_fee: self.calculate_energy_cost(energy_used),
                kind: ContractInvocationErrorKind::InsufficientFunds,
            });
        }

        // Charge account for the reserved energy up front. This is to ensure that
        // contract queries for the invoker balance are correct.
        // The `amount` is handled in contract_invocation_worker.
        //
        // *It is vital that we do not return early before returning the amount for
        // remaining energy.*
        account_info.balance.total -= invoker_amount_reserved_for_nrg;

        let res = self.contract_invocation_worker(
            invoker,
            sender,
            energy_reserved,
            payload,
            &mut remaining_energy,
            true,
        );

        let transaction_fee = match &res {
            Ok(s) => s.transaction_fee,
            Err(e) => e.transaction_fee,
        };
        // The `invoker` was charged for all the `reserved_energy` up front.
        // Here, we return the amount for any remaining energy.
        let return_amount = invoker_amount_reserved_for_nrg - transaction_fee;
        self.account_mut(invoker)
            .expect("existence already checked")
            .balance
            .total += return_amount;

        res
    }

    /// Invoke a contract by calling an entrypoint.
    ///
    /// Similar to [`Self::contract_update`] except that all changes are
    /// discarded afterwards. Typically used for "view" functions.
    ///
    /// **Parameters:**
    ///  - `invoker`: the account paying for the transaction.
    ///  - `sender`: the sender of the transaction, can also be a contract.
    ///  - `contract_address`: the contract to update.
    ///  - `entrypoint`: the entrypoint to call.
    ///  - `parameter`: the contract parameter.
    ///  - `amount`: the amount sent to the contract.
    ///  - `energy_reserved`: the maximum energy that can be used in the update.
    pub fn contract_invoke(
        &mut self,
        invoker: AccountAddress,
        sender: Address,
        energy_reserved: Energy,
        payload: UpdateContractPayload,
    ) -> Result<ContractInvocationSuccess, ContractInvocationError> {
        // Ensure the invoker exists.
        if !self.account_exists(invoker) {
            return Err(ContractInvocationError {
                energy_used:     Energy::from(0),
                transaction_fee: Amount::zero(),
                kind:            ContractInvocationErrorKind::InvokerDoesNotExist(
                    AccountDoesNotExist { address: invoker },
                ),
            });
        }
        // Ensure the sender exists.
        if !self.address_exists(sender) {
            return Err(ContractInvocationError {
                energy_used:     Energy::from(0),
                transaction_fee: Amount::zero(),
                kind:            ContractInvocationErrorKind::SenderDoesNotExist(sender),
            });
        }

        let invoker_amount_reserved_for_nrg = self.calculate_energy_cost(energy_reserved);
        // Ensure account exists and can pay for the reserved energy and amount
        let account_info = self
            .account_mut(invoker)
            .expect("existence already checked");

        if account_info.balance.available() < invoker_amount_reserved_for_nrg + payload.amount {
            let energy_used = Energy::from(0);
            return Err(ContractInvocationError {
                energy_used,
                transaction_fee: self.calculate_energy_cost(energy_used),
                kind: ContractInvocationErrorKind::InsufficientFunds,
            });
        }

        // Charge account for the reserved energy up front. This is to ensure that
        // contract queries for the invoker balance are correct.
        account_info.balance.total -= invoker_amount_reserved_for_nrg;

        let mut remaining_energy = energy_reserved;

        let result = self.contract_invocation_worker(
            invoker,
            sender,
            energy_reserved,
            payload,
            &mut remaining_energy,
            false,
        );

        // Return the amount charged for the reserved energy, as this is not a
        // transaction.
        self.account_mut(invoker)
            .expect("Known to exist")
            .balance
            .total += invoker_amount_reserved_for_nrg;

        result
    }

    /// Create an account.
    ///
    /// Will override an existing account and return it.
    pub fn create_account(
        &mut self,
        account: AccountAddress,
        account_info: Account,
    ) -> Option<Account> {
        self.accounts.insert(account, account_info)
    }

    /// Create a contract address by giving it the next available index.
    fn create_contract_address(&mut self) -> ContractAddress {
        let index = self.next_contract_index;
        let subindex = 0;
        self.next_contract_index += 1;
        ContractAddress::new(index, subindex)
    }

    /// Returns the balance of an account if it exists.
    pub fn account_balance(&self, address: AccountAddress) -> Option<AccountBalance> {
        self.accounts.get(&address).map(|ai| ai.balance)
    }

    /// Returns the available balance of an account if it exists.
    pub fn account_balance_available(&self, address: AccountAddress) -> Option<Amount> {
        self.accounts.get(&address).map(|ai| ai.balance.available())
    }

    /// Returns the balance of an contract if it exists.
    pub fn contract_balance(&self, address: ContractAddress) -> Option<Amount> {
        self.contracts.get(&address).map(|ci| ci.self_balance)
    }

    /// Helper method for looking up part of the state of a smart contract,
    /// which is a key-value store.
    pub fn contract_state_lookup(&self, address: ContractAddress, key: &[u8]) -> Option<Vec<u8>> {
        let mut loader = v1::trie::Loader::new(&[][..]);
        self.contracts.get(&address)?.state.lookup(&mut loader, key)
    }

    /// Return a clone of the [`ContractModule`] (which has an `Arc` around the
    /// artifact).
    fn contract_module(
        &self,
        module_ref: ModuleReference,
    ) -> Result<ContractModule, ModuleDoesNotExist> {
        let module = self.modules.get(&module_ref).ok_or(ModuleDoesNotExist {
            module_reference: module_ref,
        })?;
        Ok(module.clone())
    }

    /// Returns an immutable reference to an [`Account`].
    pub fn account(&self, address: AccountAddress) -> Result<&Account, AccountDoesNotExist> {
        self.accounts
            .get(&address)
            .ok_or(AccountDoesNotExist { address })
    }

    /// Returns a mutable reference to [`Account`].
    fn account_mut(
        &mut self,
        address: AccountAddress,
    ) -> Result<&mut Account, AccountDoesNotExist> {
        self.accounts
            .get_mut(&address)
            .ok_or(AccountDoesNotExist { address })
    }

    /// Check whether an [`Account`] exists.
    pub fn account_exists(&self, address: AccountAddress) -> bool {
        self.accounts.contains_key(&address)
    }

    /// Check whether a [`Contract`] exists.
    pub fn contract_exists(&self, address: ContractAddress) -> bool {
        self.contracts.contains_key(&address)
    }

    /// Check whether an object with the [`Address`] exists.
    ///
    /// That is, if it is an account address, whether the account exists,
    /// and if it is a contract address, whether the contract exists.
    fn address_exists(&self, address: Address) -> bool {
        match address {
            Address::Account(acc) => self.account_exists(acc),
            Address::Contract(contr) => self.contract_exists(contr),
        }
    }

    /// Convert a [`ContractInvocationErrorKind`] to a
    /// [`ContractInvocationError`] by calculating the `energy_used` and
    /// `transaction_fee`.
    fn from_invocation_error_kind(
        &self,
        kind: ContractInvocationErrorKind,
        energy_reserved: Energy,
        remaining_energy: Energy,
    ) -> ContractInvocationError {
        let energy_used = energy_reserved - remaining_energy;
        let transaction_fee = self.calculate_energy_cost(energy_used);
        ContractInvocationError {
            energy_used,
            transaction_fee,
            kind,
        }
    }

    /// Construct a [`ContractInvocationError`] of the `OutOfEnergy` kind with
    /// the energy and transaction fee fields based on the `energy_reserved`
    /// parameter.
    fn invocation_out_of_energy_error(&self, energy_reserved: Energy) -> ContractInvocationError {
        self.from_invocation_error_kind(
            ContractInvocationErrorKind::OutOfEnergy,
            energy_reserved,
            Energy::from(0),
        )
    }

    /// Convert a [`ContractInitErrorKind`] to a
    /// [`ContractInitError`] by calculating the `energy_used` and
    /// `transaction_fee`.
    fn from_init_error_kind(
        &self,
        kind: ContractInitErrorKind,
        energy_reserved: Energy,
        remaining_energy: Energy,
    ) -> ContractInitError {
        let energy_used = energy_reserved - remaining_energy;
        let transaction_fee = self.calculate_energy_cost(energy_used);
        ContractInitError {
            energy_used,
            transaction_fee,
            kind,
        }
    }

    /// Helper function for converting [`Energy`] to [`Amount`] using the two
    /// [`ExchangeRate`]s `euro_per_energy` and `micro_ccd_per_euro`.
    pub fn calculate_energy_cost(&self, energy: Energy) -> Amount {
        energy_to_amount(energy, self.euro_per_energy, self.micro_ccd_per_euro)
    }

    /// Try to set the exchange rates on the chain.
    ///
    /// Will fail if they result in the cost of one energy being larger than
    /// `u64::MAX / MAX_ALLOWED_INVOKE_ENERGY`.
    pub fn set_exchange_rate(
        &mut self,
        micro_ccd_per_euro: ExchangeRate,
        euro_per_energy: ExchangeRate,
    ) -> Result<(), ExchangeRateError> {
        // Ensure the exchange rates are within a valid range.
        check_exchange_rates(euro_per_energy, micro_ccd_per_euro)?;
        self.micro_ccd_per_euro = micro_ccd_per_euro;
        self.euro_per_energy = euro_per_energy;
        Ok(())
    }

    /// Return the current microCCD per euro exchange rate.
    pub fn micro_ccd_per_euro(&self) -> ExchangeRate { self.micro_ccd_per_euro }

    /// Return the current euro per energy exchange rate.
    pub fn euro_per_energy(&self) -> ExchangeRate { self.euro_per_energy }
}

impl TestPolicies {
    // TODO: Make correctly structured policies ~= Vec<Tuple<Credential,
    // PolicyBytes>>.
    pub fn empty() -> Self { Self(Vec::new()) }

    // TODO: Add helper functions for creating arbitrary valid policies.
}

impl AsRef<[u8]> for TestPolicies {
    fn as_ref(&self) -> &[u8] { &self.0 }
}

impl Account {
    /// Create a new [`Self`] with the provided parameters.
    ///
    /// The `signature_count` must be >= 1 for transaction costs to be
    /// realistic.
    pub fn new_with_policy_and_signature_count(
        balance: AccountBalance,
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
    /// `signature_count`.
    ///
    /// The `signature_count` must be >= 1 for transaction
    /// costs to be realistic.
    pub fn new_with_signature_count(balance: AccountBalance, signature_count: u32) -> Self {
        Self {
            signature_count,
            ..Self::new_with_balance(balance)
        }
    }

    /// Create new [`Self`] with the provided account policies and a signature
    /// count of `1`.
    pub fn new_with_policy(balance: AccountBalance, policies: TestPolicies) -> Self {
        Self {
            balance,
            policies: policies.0,
            signature_count: 1,
        }
    }

    /// Create new [`Self`] with empty account policies and a signature
    /// count of `1`.
    pub fn new_with_balance(balance: AccountBalance) -> Self {
        Self::new_with_policy(balance, TestPolicies::empty())
    }

    /// Create new [`Self`] with
    ///  - empty account policies,
    ///  - a signature count of `1`,
    ///  - an [`AccountBalance`] from the `total_balance` provided.
    pub fn new(total_balance: Amount) -> Self {
        Self::new_with_policy(
            AccountBalance {
                total:  total_balance,
                staked: Amount::zero(),
                locked: Amount::zero(),
            },
            TestPolicies::empty(),
        )
    }
}

impl ContractInvocationSuccess {
    /// Get an iterator of all transfers that were made from contracts to
    /// accounts.
    pub fn transfers(&self) -> impl Iterator<Item = Transfer> + '_ {
        self.chain_events.iter().filter_map(|e| {
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
    }

    /// Get the chain events grouped by which contract they originated from.
    pub fn chain_events_per_contract(&self) -> BTreeMap<ContractAddress, Vec<ChainEvent>> {
        let mut map: BTreeMap<ContractAddress, Vec<ChainEvent>> = BTreeMap::new();
        for event in self.chain_events.iter() {
            map.entry(event.contract_address())
                .and_modify(|v| v.push(event.clone()))
                .or_insert(vec![event.clone()]);
        }
        map
    }
}

impl ChainEvent {
    /// Get the contract address that this event relates to.
    /// This means the `address` field for all variant except `Transferred`,
    /// where it returns the `from`.
    pub fn contract_address(&self) -> ContractAddress {
        match self {
            ChainEvent::Interrupted { address, .. } => *address,
            ChainEvent::Resumed { address, .. } => *address,
            ChainEvent::Upgraded { address, .. } => *address,
            ChainEvent::Updated { address, .. } => *address,
            ChainEvent::Transferred { from, .. } => *from,
        }
    }
}

impl From<OutOfEnergy> for ContractInvocationErrorKind {
    fn from(_: OutOfEnergy) -> Self { Self::OutOfEnergy }
}

impl From<OutOfEnergy> for ContractInitErrorKind {
    fn from(_: OutOfEnergy) -> Self { Self::OutOfEnergy }
}

/// Convert [`Energy`] to [`InterpreterEnergy`] by multiplying by `1000`.
pub(crate) fn to_interpreter_energy(energy: Energy) -> InterpreterEnergy {
    InterpreterEnergy::from(energy.energy * 1000)
}

/// Convert [`InterpreterEnergy`] to [`Energy`] by dividing by `1000`.
pub(crate) fn from_interpreter_energy(interpreter_energy: InterpreterEnergy) -> Energy {
    Energy::from(interpreter_energy.energy / 1000)
}

/// Calculate the energy for looking up a [`ContractModule`].
pub(crate) fn lookup_module_cost(module: &ContractModule) -> Energy {
    // The ratio is from Concordium/Cost.hs::lookupModule
    Energy::from(module.size / 50)
}

/// Calculate the microCCD(mCCD) cost of energy(NRG) using the two exchange
/// rates provided.
///
/// To find the mCCD/NRG exchange rate:
/// ```ignore
///  euro     mCCD   euro * mCCD   mCCD
///  ----  *  ---- = ----------- = ----
///  NRG      euro   NRG * euro    NRG
/// ```
///
/// To convert the `energy` parameter to mCCD:
/// ```ignore
/// 
///        mCCD   NRG * mCCD
///  NRG * ---- = ---------- = mCCD
///        NRG       NRG
/// ```
pub(crate) fn energy_to_amount(
    energy: Energy,
    euro_per_energy: ExchangeRate,
    micro_ccd_per_euro: ExchangeRate,
) -> Amount {
    let micro_ccd_per_energy_numerator: BigUint =
        BigUint::from(euro_per_energy.numerator()) * micro_ccd_per_euro.numerator();
    let micro_ccd_per_energy_denominator: BigUint =
        BigUint::from(euro_per_energy.denominator()) * micro_ccd_per_euro.denominator();
    let cost: BigUint =
        (micro_ccd_per_energy_numerator * energy.energy) / micro_ccd_per_energy_denominator;
    let cost: u64 = u64::try_from(cost).expect(
        "Should never overflow since reasonable exchange rates are ensured when constructing the \
         [`Chain`].",
    );
    Amount::from_micro_ccd(cost)
}

/// Helper function that checks the validity of the exchange rates.
///
/// More specifically, it checks that the cost of one energy is <= `u64::MAX /
/// MAX_ALLOWED_INVOKE_ENERGY`, which ensures that overflows won't occur.
fn check_exchange_rates(
    euro_per_energy: ExchangeRate,
    micro_ccd_per_euro: ExchangeRate,
) -> Result<(), ExchangeRateError> {
    let micro_ccd_per_energy_numerator: BigUint =
        BigUint::from(euro_per_energy.numerator()) * micro_ccd_per_euro.numerator();
    let micro_ccd_per_energy_denominator: BigUint =
        BigUint::from(euro_per_energy.denominator()) * micro_ccd_per_euro.denominator();
    let max_allowed_micro_ccd_to_energy = u64::MAX / MAX_ALLOWED_INVOKE_ENERGY.energy;
    let micro_ccd_per_energy =
        u64::try_from(micro_ccd_per_energy_numerator / micro_ccd_per_energy_denominator)
            .map_err(|_| ExchangeRateError)?;
    if micro_ccd_per_energy > max_allowed_micro_ccd_to_energy {
        return Err(ExchangeRateError);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A few checks that test whether the function behavior matches its doc
    /// comments.
    #[test]
    fn check_exchange_rates_works() {
        let max_allowed_micro_ccd_per_energy = u64::MAX / MAX_ALLOWED_INVOKE_ENERGY.energy;
        check_exchange_rates(
            ExchangeRate::new_unchecked(max_allowed_micro_ccd_per_energy + 1, 1),
            ExchangeRate::new_unchecked(1, 1),
        )
        .expect_err("should fail");

        check_exchange_rates(
            ExchangeRate::new_unchecked(max_allowed_micro_ccd_per_energy / 2 + 1, 1),
            ExchangeRate::new_unchecked(2, 1),
        )
        .expect_err("should fail");

        check_exchange_rates(
            ExchangeRate::new_unchecked(max_allowed_micro_ccd_per_energy, 1),
            ExchangeRate::new_unchecked(1, 1),
        )
        .expect("should succeed");

        check_exchange_rates(
            ExchangeRate::new_unchecked(50000, 1),
            ExchangeRate::new_unchecked(1, 50000),
        )
        .expect("should succeed");
    }
}
