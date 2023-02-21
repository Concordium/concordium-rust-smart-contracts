use concordium_base::{
    base::{self, Energy},
    common::{self, to_bytes},
    contracts_common::{
        AccountAddress, AccountBalance, Address, Amount, ChainMetadata, ContractAddress,
        ContractName, EntrypointName, ExchangeRate, ModuleReference, OwnedParameter, Parameter,
        SlotTime, Timestamp,
    },
    smart_contracts::{ModuleSource, WasmModule, WasmVersion},
    transactions::{self, cost, InitContractPayload},
};
use num_bigint::BigUint;
use std::{collections::BTreeMap, path::Path, sync::Arc};
use wasm_chain_integration::{v0, v1, InterpreterEnergy};

use crate::{
    constants,
    invocation::{EntrypointInvocationHandler, InvokeEntrypointResult},
    types::*,
};

impl Default for Chain {
    fn default() -> Self { Self::new() }
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
            &v1::ConcordiumAllowedImports {
                support_upgrade: true,
            },
            wasm_module.source.as_ref(),
        )?;

        // Calculate transaction fee of deployment
        let energy = {
            // +1 for the tag, +8 for size and version
            let payload_size = 1
                + 8
                + wasm_module.source.size()
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
        if account.balance.available() < transaction_fee {
            return Err(DeployModuleError::InsufficientFunds);
        };
        account.balance.total -= transaction_fee;

        // Save the module
        let module_reference: ModuleReference = wasm_module.get_module_ref().into();
        // Ensure module hasn't been deployed before.
        if self.modules.contains_key(&module_reference) {
            return Err(DeployModuleError::DuplicateModule(module_reference));
        }
        self.modules.insert(module_reference, ContractModule {
            size:     wasm_module.source.size(),
            artifact: Arc::new(artifact),
        });
        Ok(SuccessfulModuleDeployment {
            module_reference,
            energy_used: energy,
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
        parameter: OwnedParameter,
        amount: Amount,
        energy_reserved: Energy,
    ) -> Result<SuccessfulContractInit, ContractInitError> {
        // Get the account and check that it has sufficient balance to pay for the
        // reserved_energy and amount.
        let account_info = self.get_account(sender)?;
        if account_info.balance.available() < self.calculate_energy_cost(energy_reserved) + amount {
            return Err(ContractInitError::InsufficientFunds);
        }

        let mut remaining_energy = energy_reserved;

        // Compute the base cost for checking the transaction header.
        let check_header_cost = {
            let payload = InitContractPayload {
                amount,
                mod_ref: module_reference.into(),
                init_name: contract_name.to_owned(),
                param: parameter.clone().into(),
            };
            let pre_account_trx = transactions::construct::init_contract(
                account_info.signature_count,
                sender,
                base::Nonce::from(0), // Value not matter, only used for serialized size.
                common::types::TransactionTime::from_seconds(0), /* Value does not matter, only
                                       * used for serialized size. */
                payload,
                energy_reserved,
            );
            let transaction_size = to_bytes(&pre_account_trx).len() as u64;
            transactions::cost::base_cost(transaction_size, account_info.signature_count)
        };

        // Charge the header cost.
        remaining_energy = remaining_energy.saturating_sub(check_header_cost);

        // Charge the base cost for initializing a contract.
        remaining_energy =
            remaining_energy.saturating_sub(constants::INITIALIZE_CONTRACT_INSTANCE_BASE_COST);

        // Lookup module.
        let module = self.contract_module(module_reference)?;
        let lookup_cost = lookup_module_cost(&module);
        // Charge the cost for looking up the module.
        remaining_energy = remaining_energy.saturating_sub(lookup_cost);

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
            module.artifact,
            init_ctx,
            v1::InitInvocation {
                amount,
                init_name: contract_name.get_chain_name(),
                parameter: &parameter.0,
                energy: to_interpreter_energy(remaining_energy),
            },
            false,
            loader,
        );
        // Handle the result and compute the transaction fee.
        let (res, transaction_fee) = match res {
            Ok(v1::InitResult::Success {
                logs,
                return_value: _, /* Ignore return value for now, since our tools do not support
                                  * it for inits, currently. */
                remaining_energy,
                mut state,
            }) => {
                let contract_address = self.create_contract_address();
                let mut collector = v1::trie::SizeCollector::default();

                let persisted_state = state.freeze(&mut loader, &mut collector);

                let mut remaining_energy = InterpreterEnergy::from(remaining_energy);

                // Charge one energy per stored state byte.
                let energy_for_state_storage =
                    to_interpreter_energy(Energy::from(collector.collect()));
                remaining_energy = remaining_energy.saturating_sub(energy_for_state_storage);

                // Charge the constant cost for initializing a contract.
                remaining_energy = remaining_energy.saturating_sub(to_interpreter_energy(
                    constants::INITIALIZE_CONTRACT_INSTANCE_CREATE_COST,
                ));

                if remaining_energy.energy == 0 {
                    // Ran out of energy. Charge the `energy_reserved`.
                    let transaction_fee = self.calculate_energy_cost(energy_reserved);
                    (
                        Err(ContractInitError::ValidChainError(
                            FailedContractInteraction::OutOfEnergy {
                                energy_used:     energy_reserved,
                                transaction_fee: self.calculate_energy_cost(energy_reserved),
                            },
                        )),
                        transaction_fee,
                    )
                } else {
                    // Perform the subtraction in the more finegrained (*1000) `InterpreterEnergy`,
                    // and *then* convert to `Energy`. This is how it is done in the node, and if we
                    // swap the operations, it can result in a small discrepancy due to rounding.
                    let energy_reserved = to_interpreter_energy(energy_reserved);
                    let energy_used =
                        from_interpreter_energy(energy_reserved.saturating_sub(remaining_energy));
                    let transaction_fee = self.calculate_energy_cost(energy_used);

                    let contract_instance = Contract {
                        module_reference,
                        contract_name: contract_name.to_owned(),
                        state: persisted_state,
                        owner: sender,
                        self_balance: amount,
                    };

                    // Save the contract instance
                    self.contracts.insert(contract_address, contract_instance);

                    // Subtract the amount from the invoker.
                    self.get_account_mut(sender)
                        .expect("Account known to exist")
                        .balance
                        .total -= amount;

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
            }
            Ok(v1::InitResult::Reject {
                reason,
                return_value,
                remaining_energy,
            }) => {
                let energy_reserved = to_interpreter_energy(energy_reserved);
                let energy_used = from_interpreter_energy(
                    energy_reserved.saturating_sub(InterpreterEnergy::from(remaining_energy)),
                );
                let transaction_fee = self.calculate_energy_cost(energy_used);
                (
                    Err(ContractInitError::ValidChainError(
                        FailedContractInteraction::Reject {
                            reason,
                            return_value,
                            energy_used,
                            transaction_fee,
                        },
                    )),
                    transaction_fee,
                )
            }
            Ok(v1::InitResult::Trap {
                error: _, // TODO: Should we forward this to the user?
                remaining_energy,
            }) => {
                let energy_reserved = to_interpreter_energy(energy_reserved);
                let energy_used = from_interpreter_energy(
                    energy_reserved.saturating_sub(InterpreterEnergy::from(remaining_energy)),
                );
                let transaction_fee = self.calculate_energy_cost(energy_used);
                (
                    Err(ContractInitError::ValidChainError(
                        FailedContractInteraction::Trap {
                            energy_used,
                            transaction_fee,
                        },
                    )),
                    transaction_fee,
                )
            }
            Ok(v1::InitResult::OutOfEnergy) => {
                let transaction_fee = self.calculate_energy_cost(energy_reserved);
                (
                    Err(ContractInitError::ValidChainError(
                        FailedContractInteraction::OutOfEnergy {
                            energy_used: energy_reserved,
                            transaction_fee,
                        },
                    )),
                    transaction_fee,
                )
            }
            Err(e) => panic!("Internal error: init failed with interpreter error: {}", e),
        };
        // Charge the account.
        // We have to get the account info again because of the borrow checker.
        self.get_account_mut(sender)?.balance.total -= transaction_fee;
        res
    }

    /// Update a contract by calling one of its entrypoints.
    ///
    /// If successful, any changes will be saved.
    pub fn contract_update(
        &mut self,
        invoker: AccountAddress,
        sender: Address,
        contract_address: ContractAddress,
        entrypoint: EntrypointName,
        parameter: OwnedParameter,
        amount: Amount,
        energy_reserved: Energy,
    ) -> Result<SuccessfulContractUpdate, ContractUpdateError> {
        println!(
            "Updating contract {}, with parameter: {:?}",
            contract_address, parameter.0
        );

        // Ensure the sender exists.
        if !self.address_exists(sender) {
            return Err(ContractUpdateError::SenderDoesNotExist(sender));
        }

        // Ensure account exists and can pay for the reserved energy and amount
        // TODO: Could we just remove this amount in the changeset and then put back the
        // to_ccd(remaining_energy) afterwards?
        let account_info = self.get_account(invoker)?;
        let invoker_amount_reserved_for_nrg = self.calculate_energy_cost(energy_reserved);
        if account_info.balance.available() < invoker_amount_reserved_for_nrg + amount {
            return Err(ContractUpdateError::InsufficientFunds);
        }

        // TODO: Should chain events be part of the changeset?
        let (result, changeset, chain_events) =
            EntrypointInvocationHandler::invoke_entrypoint_and_get_changes(
                &self,
                invoker,
                sender,
                contract_address,
                entrypoint.to_owned(),
                Parameter(&parameter.0),
                amount,
                invoker_amount_reserved_for_nrg,
                energy_reserved,
            );

        // Get the energy to be charged for extra state bytes. Or return an error if out
        // of energy.
        let (energy_for_state_increase, state_changed) = if result.is_success() {
            match changeset.persist(
                from_interpreter_energy(result.remaining_energy),
                contract_address,
                &mut self.accounts,
                &mut self.contracts,
            ) {
                Ok(energy) => energy,
                Err(_) => {
                    return Err(ContractUpdateError::OutOfEnergy {
                        energy_used:     energy_reserved,
                        transaction_fee: self.calculate_energy_cost(energy_reserved),
                    });
                }
            }
        } else {
            // An error occured, so no energy should be charged for storing the state.
            (Energy::from(0), false)
        };

        let (res, transaction_fee) = self.convert_invoke_entrypoint_result(
            result,
            chain_events,
            energy_reserved,
            energy_for_state_increase,
            state_changed,
        );

        // Charge the transaction fee irrespective of the result.
        // TODO: If we charge up front, then we should return to_ccd(remaining_energy)
        // here instead.
        self.get_account_mut(invoker)?.balance.total -= transaction_fee;
        res
    }

    /// Invoke a contract by calling an entrypoint.
    ///
    /// Similar to [`contract_update`] except that all changes are discarded
    /// afterwards. Typically used for "view" functions.
    pub fn contract_invoke(
        &mut self,
        invoker: AccountAddress,
        sender: Address,
        contract_address: ContractAddress,
        entrypoint: EntrypointName,
        parameter: OwnedParameter,
        amount: Amount,
        energy_reserved: Energy,
    ) -> Result<SuccessfulContractUpdate, ContractUpdateError> {
        println!(
            "Invoking contract {}, with parameter: {:?}",
            contract_address, parameter.0
        );

        // Ensure the sender exists.
        if !self.address_exists(sender) {
            return Err(ContractUpdateError::SenderDoesNotExist(sender));
        }

        // Ensure account exists and can pay for the reserved energy and amount
        let account_info = self.get_account(invoker)?;
        let invoker_amount_reserved_for_nrg = self.calculate_energy_cost(energy_reserved);
        if account_info.balance.available() < invoker_amount_reserved_for_nrg + amount {
            return Err(ContractUpdateError::InsufficientFunds);
        }

        let (result, changeset, chain_events) =
            EntrypointInvocationHandler::invoke_entrypoint_and_get_changes(
                &self,
                invoker,
                sender,
                contract_address,
                entrypoint.to_owned(),
                Parameter(&parameter.0),
                amount,
                invoker_amount_reserved_for_nrg,
                energy_reserved,
            );

        let (energy_for_state_increase, state_changed) = if result.is_success() {
            match changeset.collect_energy_for_state(
                from_interpreter_energy(result.remaining_energy),
                contract_address,
            ) {
                Ok(energy) => energy,
                Err(_) => {
                    return Err(ContractUpdateError::OutOfEnergy {
                        energy_used:     energy_reserved,
                        transaction_fee: self.calculate_energy_cost(energy_reserved),
                    });
                }
            }
        } else {
            // An error occured, so no energy should be charged for storing state.
            (Energy::from(0), false)
        };

        let (result, _) = self.convert_invoke_entrypoint_result(
            result,
            chain_events,
            energy_reserved,
            energy_for_state_increase,
            state_changed,
        );

        result
    }

    /// Create an account. Will override existing account if already present.
    pub fn create_account(&mut self, account: AccountAddress, account_info: Account) {
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

    /// Set the chain's slot time.
    pub fn set_slot_time(&mut self, slot_time: SlotTime) { self.slot_time = slot_time; }

    /// Set the chain's Euro per NRG conversion rate.
    pub fn set_euro_per_energy(&mut self, euro_per_energy: ExchangeRate) {
        self.euro_per_energy = euro_per_energy;
    }

    /// Set the chain's microCCD per Euro conversion rate.
    pub fn set_micro_ccd_per_euro(&mut self, micro_ccd_per_euro: ExchangeRate) {
        self.micro_ccd_per_euro = micro_ccd_per_euro;
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

    /// Return a clone of the [`ContractModule`] (which has an `Arc` around the
    /// artifact).
    fn contract_module(
        &self,
        module_ref: ModuleReference,
    ) -> Result<ContractModule, ModuleMissing> {
        let module = self
            .modules
            .get(&module_ref)
            .ok_or(ModuleMissing(module_ref))?;
        Ok(module.clone())
    }

    /// Returns an immutable reference to an [`Account`].
    pub fn get_account(&self, address: AccountAddress) -> Result<&Account, AccountMissing> {
        self.accounts.get(&address).ok_or(AccountMissing(address))
    }

    /// Returns a mutable reference to [`Account`].
    fn get_account_mut(&mut self, address: AccountAddress) -> Result<&mut Account, AccountMissing> {
        self.accounts
            .get_mut(&address)
            .ok_or(AccountMissing(address))
    }

    /// Check whether an [`Account`] exists.
    pub fn account_exists(&self, address: AccountAddress) -> bool {
        self.accounts.contains_key(&address)
    }

    /// Check whether a [`Contract`] exists.
    pub fn contract_exists(&self, address: ContractAddress) -> bool {
        self.contracts.contains_key(&address)
    }

    /// Check whether the [`Address`] exists. I.e. if it is an
    /// account, whether the account exists, and if it is a contract, whether
    /// the contract exists.
    fn address_exists(&self, address: Address) -> bool {
        match address {
            Address::Account(acc) => self.account_exists(acc),
            Address::Contract(contr) => self.contract_exists(contr),
        }
    }

    /// Convert the [`InvokeEntrypointResult`] to a contract success or error.
    ///
    /// The `energy_for_state_increase` is only used if the result was a
    /// success.
    ///
    /// The `state_changed` should refer to whether the state of the top-level
    /// contract invoked has changed.
    ///
    /// *Preconditions*:
    /// - `energy_reserved - remaining_energy + energy_for_state_increase >= 0`
    fn convert_invoke_entrypoint_result(
        &self,
        update_aux_response: InvokeEntrypointResult,
        chain_events: Vec<ChainEvent>,
        energy_reserved: Energy,
        energy_for_state_increase: Energy,
        state_changed: bool,
    ) -> (
        Result<SuccessfulContractUpdate, ContractUpdateError>,
        Amount,
    ) {
        let remaining_energy = from_interpreter_energy(update_aux_response.remaining_energy);
        match update_aux_response.invoke_response {
            v1::InvokeResponse::Success { new_balance, data } => {
                let energy_used = energy_reserved - remaining_energy + energy_for_state_increase;
                let transaction_fee = self.calculate_energy_cost(energy_used);
                let result = Ok(SuccessfulContractUpdate {
                    chain_events,
                    energy_used,
                    transaction_fee,
                    return_value: data.unwrap_or_default(),
                    state_changed,
                    new_balance,
                    logs: update_aux_response.logs.unwrap_or_default(),
                });
                (result, transaction_fee)
            }
            v1::InvokeResponse::Failure { kind } => {
                let energy_used = energy_reserved - remaining_energy + energy_for_state_increase;
                let transaction_fee = self.calculate_energy_cost(energy_used);
                let result = Err(ContractUpdateError::ExecutionError {
                    failure_kind: kind,
                    energy_used,
                    transaction_fee,
                });
                (result, transaction_fee)
            }
        }
    }

    /// Helper function for converting [`Energy`] to [`Amount`] using the two
    /// [`ExchangeRate`]s `euro_per_energy` and `micro_ccd_per_euro`.
    pub fn calculate_energy_cost(&self, energy: Energy) -> Amount {
        energy_to_amount(energy, self.euro_per_energy, self.micro_ccd_per_euro)
    }
}

impl TestPolicies {
    // TODO: Make correctly structured policies ~= Vec<Tuple<Credential,
    // PolicyBytes>>.
    pub fn empty() -> Self { Self(v0::OwnedPolicyBytes::new()) }

    // TODO: Add helper functions for creating arbitrary valid policies.
}

impl Account {
    /// Create a new [`Self`] with the provided parameters.
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
    /// `signature_count`. The `signature_count` must be >= 1 for transaction
    /// costs to be realistic.
    pub fn new_with_signature_count(balance: AccountBalance, signature_count: u32) -> Self {
        Self {
            signature_count,
            ..Self::new_with_balance(balance)
        }
    }

    /// Create new [`Self`] with empty account policies and a signature
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

impl FailedContractInteraction {
    /// Get the transaction fee.
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
}

impl SuccessfulContractUpdate {
    /// Get a list of all transfers that were made from contracts to accounts.
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

/// Convert [`Energy`] to [`InterpreterEnergy`] by multiplying by `1000`.
pub(crate) fn to_interpreter_energy(energy: Energy) -> InterpreterEnergy {
    InterpreterEnergy::from(energy.energy * 1000)
}

/// Convert [`InterpreterEnergy`] to [`Energy`] by dividing by `1000`.
pub(crate) fn from_interpreter_energy(interpreter_energy: InterpreterEnergy) -> Energy {
    Energy::from(interpreter_energy.energy / 1000)
}

/// Calculate the energy energy for looking up a [`ContractModule`].
pub(crate) fn lookup_module_cost(module: &ContractModule) -> Energy {
    // The ratio is from Concordium/Cost.hs::lookupModule
    Energy::from(module.size / 50)
}

/// Calculate the microCCD(mCCD) cost of energy(NRG) using the two exchange
/// rates provided.
// TODO: Find a way to make this parse the doc tests
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
    let cost: u64 = u64::try_from(cost).expect("Should never overflow due to use of BigUint");
    Amount::from_micro_ccd(cost)
}

#[cfg(test)]
mod tests {
    use super::*;

    const ACC_0: AccountAddress = AccountAddress([0; 32]);
    const ACC_1: AccountAddress = AccountAddress([1; 32]);

    #[test]
    fn calculate_cost_will_not_overflow() {
        let micro_ccd_per_euro = ExchangeRate::new_unchecked(u64::MAX, u64::MAX - 1);
        let euro_per_energy = ExchangeRate::new_unchecked(u64::MAX - 2, u64::MAX - 3);
        let energy = Energy::from(u64::MAX - 4);
        energy_to_amount(energy, euro_per_energy, micro_ccd_per_euro);
    }

    #[test]
    fn creating_accounts_work() {
        let mut chain = Chain::new();
        chain.create_account(ACC_0, Account::new(Amount::from_ccd(1)));
        chain.create_account(ACC_1, Account::new(Amount::from_ccd(2)));

        assert_eq!(chain.accounts.len(), 2);
        assert_eq!(
            chain.account_balance_available(ACC_0),
            Some(Amount::from_ccd(1))
        );
        assert_eq!(
            chain.account_balance_available(ACC_1),
            Some(Amount::from_ccd(2))
        );
    }
}
