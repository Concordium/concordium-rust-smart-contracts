use super::types::*;
use crate::{
    constants,
    impls::{from_interpreter_energy, lookup_module_cost, to_interpreter_energy},
    types::{
        Account, Chain, ChainEvent, Contract, ContractModule, InsufficientBalanceError,
        TransferError,
    },
};
use concordium_base::{
    base::{Energy, OutOfEnergy},
    contracts_common::{
        to_bytes, AccountAddress, AccountBalance, Address, Amount, ChainMetadata, ContractAddress,
        ExchangeRates, ModuleReference, OwnedReceiveName,
    },
    smart_contracts::{OwnedContractName, OwnedParameter},
    transactions::UpdateContractPayload,
};
use concordium_smart_contract_engine::{
    v0,
    v1::{self, trie},
    ExecResult, InterpreterEnergy,
};
use concordium_wasm::artifact;
use std::collections::{btree_map, BTreeMap};

impl<'a> EntrypointInvocationHandler<'a> {
    /// Invoke an entrypoint and get the result, [`Changeset`], and chain
    /// events.
    ///
    /// **Preconditions:**
    ///  - `invoker` exists
    ///  - `invoker` has sufficient balance to pay for `remaining_energy`
    ///  - `sender` exists
    ///  - if the contract (`contract_address`) exists, then its `module` must
    ///    also exist.
    pub(crate) fn invoke_entrypoint_and_get_changes(
        chain: &Chain,
        invoker: AccountAddress,
        sender: Address,
        remaining_energy: &'a mut Energy,
        payload: UpdateContractPayload,
    ) -> Result<(InvokeEntrypointResult, ChangeSet, Vec<ChainEvent>), OutOfEnergy> {
        let mut contract_invocation = Self {
            changeset: ChangeSet::new(),
            remaining_energy,
            accounts: chain.accounts.clone(), /* TODO: These three maps should ideally
                                               * be
                                               * immutable references. */
            modules: chain.modules.clone(),
            contracts: chain.contracts.clone(),
            block_time: chain.block_time,
            euro_per_energy: chain.euro_per_energy,
            micro_ccd_per_euro: chain.micro_ccd_per_euro,
        };

        let mut chain_events = Vec::new();
        let result =
            contract_invocation.invoke_entrypoint(invoker, sender, payload, &mut chain_events)?;
        Ok((result, contract_invocation.changeset, chain_events))
    }

    /// Used for handling contract entrypoint invocations internally.
    ///
    /// **Preconditions:**
    ///  - `invoker` exists
    ///  - `invoker` has sufficient balance to pay for `remaining_energy`
    ///  - `sender` exists
    ///  - if the contract (`contract_address`) exists, then its `module` must
    ///    also exist.
    fn invoke_entrypoint(
        &mut self,
        invoker: AccountAddress,
        sender: Address,
        payload: UpdateContractPayload,
        chain_events: &mut Vec<ChainEvent>,
    ) -> Result<InvokeEntrypointResult, OutOfEnergy> {
        // Charge the base cost for updating a contract.
        self.remaining_energy
            .tick_energy(constants::UPDATE_CONTRACT_INSTANCE_BASE_COST)?;

        // Move the amount from the sender to the contract, if any.
        // And get the new self_balance.
        let instance_self_balance = if payload.amount.micro_ccd() > 0 {
            let transfer_result = match sender {
                Address::Account(sender_account) => self.transfer_from_account_to_contract(
                    payload.amount,
                    sender_account,
                    payload.address,
                ),
                Address::Contract(sender_contract) => self.transfer_from_contract_to_contract(
                    payload.amount,
                    sender_contract,
                    payload.address,
                ),
            };
            match transfer_result {
                Ok(new_balance_from) => new_balance_from,
                Err(transfer_error) => {
                    let kind = match transfer_error {
                        TransferError::InsufficientBalance => v1::InvokeFailure::InsufficientAmount,
                        TransferError::ToMissing => v1::InvokeFailure::NonExistentContract,
                    };
                    // Return early.
                    return Ok(InvokeEntrypointResult {
                        invoke_response: v1::InvokeResponse::Failure { kind },
                        logs:            v0::Logs::new(),
                    });
                }
            }
        } else {
            match self.contract_balance(payload.address) {
                Some(self_balance) => self_balance,
                None => {
                    // Return early.
                    // TODO: For the top-most update, we should catch this in `contract_update` and
                    // return `ContractUpdateError::EntrypointDoesNotExist`.
                    return Ok(InvokeEntrypointResult {
                        invoke_response: v1::InvokeResponse::Failure {
                            kind: v1::InvokeFailure::NonExistentContract,
                        },
                        logs:            v0::Logs::new(),
                    });
                }
            }
        };

        // Get the instance and artifact. To be used in several places.
        let instance = self
            .contracts
            .get(&payload.address)
            .expect("Contract known to exist at this point");
        let module = self.contract_module(payload.address);

        // Construct the receive name (or fallback receive name) and ensure its presence
        // in the contract. Also returns the contract name and entrypoint name as they
        // are needed further down.
        let (contract_name, receive_name, entrypoint_name) = {
            let borrowed_receive_name = payload.receive_name.as_receive_name();
            let contract_name = borrowed_receive_name.contract_name();
            let owned_contract_name =
                OwnedContractName::new_unchecked(format!("init_{}", contract_name));
            let owned_entrypoint_name = borrowed_receive_name.entrypoint_name().to_owned();
            let receive_name = borrowed_receive_name.get_chain_name();
            let fallback_receive_name = format!("{}.", contract_name);
            if module.artifact.has_entrypoint(receive_name) {
                (
                    owned_contract_name,
                    payload.receive_name,
                    owned_entrypoint_name,
                )
            } else if module
                .artifact
                .has_entrypoint(fallback_receive_name.as_str())
            {
                (
                    owned_contract_name,
                    OwnedReceiveName::new_unchecked(fallback_receive_name),
                    owned_entrypoint_name,
                )
            } else {
                // Return early.
                return Ok(InvokeEntrypointResult {
                    invoke_response: v1::InvokeResponse::Failure {
                        kind: v1::InvokeFailure::NonExistentEntrypoint,
                    },
                    logs:            v0::Logs::new(),
                });
            }
        };

        // Subtract the cost of looking up the module
        self.remaining_energy
            .tick_energy(lookup_module_cost(&module))?;

        // Construct the receive context
        let receive_ctx = v1::ReceiveContext {
            // This should be the entrypoint specified, even if we end up
            // calling the fallback entrypoint, as this will be visible to the
            // contract via a host function.
            entrypoint: entrypoint_name.clone(),
            common:     v0::ReceiveContext {
                metadata: ChainMetadata {
                    slot_time: self.block_time,
                },
                invoker,
                self_address: payload.address,
                self_balance: instance_self_balance,
                sender,
                owner: instance.owner,
                sender_policies: self
                    .accounts
                    .get(&invoker)
                    .expect("Precondition violation: invoker must exist.")
                    .policies
                    .clone(),
            },
        };

        // Construct the instance state
        let mut loader = v1::trie::Loader::new(&[][..]); // An empty loader is fine currently, as we do not use caching in this lib.
        let mut mutable_state = self.contract_state(payload.address);
        let inner = mutable_state.get_inner(&mut loader);
        let instance_state = v1::InstanceState::new(loader, inner);

        // Get the initial result from invoking receive
        let initial_result = self.run_interpreter(|energy| {
            v1::invoke_receive(
                module.artifact,
                receive_ctx,
                v1::ReceiveInvocation {
                    amount: payload.amount,
                    // This will either be the one provided on the fallback receive name.
                    receive_name: receive_name.as_receive_name(),
                    parameter: payload.message.as_ref(),
                    energy,
                },
                instance_state,
                v1::ReceiveParams {
                    max_parameter_size:           65535,
                    limit_logs_and_return_values: false,
                    support_queries:              true,
                },
            )
        })?;

        // Set up some data needed for recursively processing the receive until the end,
        // i.e. beyond interrupts.
        let mut data = InvocationData {
            invoker,
            address: payload.address,
            contract_name,
            amount: payload.amount,
            entrypoint: entrypoint_name,
            invocation_handler: self,
            state: mutable_state,
            chain_events: Vec::new(),
        };

        // Process the receive invocation to the completion.
        let result = data.process(initial_result)?;
        let mut new_chain_events = data.chain_events;

        let result = match result {
            v1::ReceiveResult::Success {
                logs,
                state_changed: _, /* This only reflects changes since last interrupt, we use
                                   * the changeset later to get a more precise result. */
                return_value,
                remaining_energy: _,
            } => InvokeEntrypointResult {
                invoke_response: v1::InvokeResponse::Success {
                    new_balance: self.contract_balance_unchecked(payload.address),
                    data:        Some(return_value),
                },
                logs,
            },
            v1::ReceiveResult::Interrupt { .. } => {
                panic!("Internal error: `data.process` returned an interrupt.")
            }
            v1::ReceiveResult::Reject {
                reason,
                return_value,
                remaining_energy: _,
            } => InvokeEntrypointResult {
                invoke_response: v1::InvokeResponse::Failure {
                    kind: v1::InvokeFailure::ContractReject {
                        code: reason,
                        data: return_value,
                    },
                },
                logs:            v0::Logs::new(),
            },
            v1::ReceiveResult::Trap {
                error: _, // TODO: Should we return this to the user?
                remaining_energy: _,
            } => InvokeEntrypointResult {
                invoke_response: v1::InvokeResponse::Failure {
                    kind: v1::InvokeFailure::RuntimeError,
                },
                logs:            v0::Logs::new(),
            },
            v1::ReceiveResult::OutOfEnergy => {
                // Convert to an error so that we will short-circuit the processing.
                return Err(OutOfEnergy);
            }
        };

        // Append the new chain events if the invocation succeeded.
        if result.is_success() {
            chain_events.append(&mut new_chain_events);
        }

        Ok(result)
    }

    /// Make a transfer from a contract to an account in the changeset.
    /// Returns the new balance of `from`.
    ///
    /// **Preconditions:**
    ///  - Assumes that `from` contract exists.
    fn transfer_from_contract_to_account(
        &mut self,
        amount: Amount,
        from: ContractAddress,
        to: AccountAddress,
    ) -> Result<Amount, TransferError> {
        // Ensure the `to` account exists.
        if !self.accounts.contains_key(&to) {
            return Err(TransferError::ToMissing);
        }

        // Make the transfer.
        let new_balance = self.change_contract_balance(from, AmountDelta::Negative(amount))?;
        self.change_account_balance(to, AmountDelta::Positive(amount))
            .expect("Cannot fail when adding");

        Ok(new_balance)
    }

    /// Make a transfer between contracts in the changeset.
    ///
    /// Returns the new balance of `from`.
    ///
    /// **Preconditions:**
    ///  - Assumes that `from` contract exists.
    fn transfer_from_contract_to_contract(
        &mut self,
        amount: Amount,
        from: ContractAddress,
        to: ContractAddress,
    ) -> Result<Amount, TransferError> {
        // Ensure the `to` contract exists.
        if !self.contracts.contains_key(&to) {
            return Err(TransferError::ToMissing);
        }

        // Make the transfer.
        let new_balance = self.change_contract_balance(from, AmountDelta::Negative(amount))?;
        self.change_contract_balance(to, AmountDelta::Positive(amount))
            .expect("Cannot fail when adding");

        Ok(new_balance)
    }

    /// Make a transfer from an account to a contract in the changeset.
    ///
    /// Returns the new balance of `from`.
    ///
    /// **Preconditions:**
    ///  - Assumes that `from` account exists.
    fn transfer_from_account_to_contract(
        &mut self,
        amount: Amount,
        from: AccountAddress,
        to: ContractAddress,
    ) -> Result<Amount, TransferError> {
        // Ensure the `to` account exists.
        if !self.contracts.contains_key(&to) {
            return Err(TransferError::ToMissing);
        }

        // Make the transfer.
        let new_balance = self.change_account_balance(from, AmountDelta::Negative(amount))?;
        self.change_contract_balance(to, AmountDelta::Positive(amount))
            .expect("Cannot fail when adding");
        Ok(new_balance)
    }

    // TODO: Should we handle overflows explicitly?
    /// Changes the contract balance in the topmost checkpoint on the changeset.
    ///
    /// If contract isn't already present in the changeset, it is added.
    ///
    /// Returns the new balance.
    ///
    /// **Preconditions:**
    ///  - Contract must exist.
    fn change_contract_balance(
        &mut self,
        address: ContractAddress,
        delta: AmountDelta,
    ) -> Result<Amount, InsufficientBalanceError> {
        match self.changeset.current_mut().contracts.entry(address) {
            btree_map::Entry::Vacant(vac) => {
                // get original balance
                let original_balance = self
                    .contracts
                    .get(&address)
                    .expect("Precondition violation: contract assumed to exist")
                    .self_balance;
                // Try to apply the balance or return an error if insufficient funds.
                let new_contract_balance = delta.apply_to_balance(original_balance)?;
                // Insert the changes into the changeset.
                vac.insert(ContractChanges {
                    self_balance_delta: delta,
                    ..ContractChanges::new(original_balance)
                });
                Ok(new_contract_balance)
            }
            btree_map::Entry::Occupied(mut occ) => {
                let contract_changes = occ.get_mut();
                let new_delta = contract_changes.self_balance_delta.add_delta(delta);
                // Try to apply the balance or return an error if insufficient funds.
                let new_contract_balance =
                    new_delta.apply_to_balance(contract_changes.self_balance_original)?;
                contract_changes.self_balance_delta = new_delta;
                Ok(new_contract_balance)
            }
        }
    }

    // TODO: Should we handle overflows explicitly?
    /// Changes the account balance in the topmost checkpoint on the changeset.
    ///
    /// If account isn't already present in the changeset, it is added.
    ///
    /// Returns the new balance.
    ///
    /// **Preconditions:**
    ///  - Account must exist.
    fn change_account_balance(
        &mut self,
        address: AccountAddress,
        delta: AmountDelta,
    ) -> Result<Amount, InsufficientBalanceError> {
        match self.changeset.current_mut().accounts.entry(address) {
            btree_map::Entry::Vacant(vac) => {
                // get original balance
                let original_balance = self
                    .accounts
                    .get(&address)
                    .expect("Precondition violation: account assumed to exist")
                    .balance
                    .available();
                // Try to apply the balance or return an error if insufficient funds.
                let new_account_balance = delta.apply_to_balance(original_balance)?;
                // Insert the changes into the changeset.
                vac.insert(AccountChanges {
                    original_balance,
                    balance_delta: delta,
                });
                Ok(new_account_balance)
            }
            btree_map::Entry::Occupied(mut occ) => {
                let account_changes = occ.get_mut();
                let new_delta = account_changes.balance_delta.add_delta(delta);
                // Try to apply the balance or return an error if insufficient funds.
                let new_account_balance =
                    new_delta.apply_to_balance(account_changes.original_balance)?;
                account_changes.balance_delta = new_delta;
                Ok(new_account_balance)
            }
        }
    }

    /// Returns the contract balance from the topmost checkpoint on the
    /// changeset. Or, alternatively, from persistence.
    ///
    /// **Preconditions:**
    ///  - Contract must exist.
    fn contract_balance_unchecked(&self, address: ContractAddress) -> Amount {
        self.contract_balance(address)
            .expect("Precondition violation: contract must exist")
    }

    /// Looks up the contract balance from the topmost checkpoint on the
    /// changeset. Or, alternatively, from persistence.
    fn contract_balance(&self, address: ContractAddress) -> Option<Amount> {
        match self.changeset.current().contracts.get(&address) {
            Some(changes) => Some(changes.current_balance()),
            None => self.contracts.get(&address).map(|c| c.self_balance),
        }
    }

    /// Returns the contract module from the topmost checkpoint on
    /// the changeset. Or, alternatively, from persistence.
    ///
    /// **Preconditions:**
    ///  - Contract instance must exist (and therefore also the artifact).
    ///  - If the changeset contains a module reference, then it must refer a
    ///    deployed module.
    fn contract_module(&self, address: ContractAddress) -> ContractModule {
        match self
            .changeset
            .current()
            .contracts
            .get(&address)
            .and_then(|c| c.module)
        {
            // Contract has been upgrade, new module exists.
            Some(new_module) => self
                .modules
                .get(&new_module)
                .expect("Precondition violation: module must exist.")
                .clone(),
            // Contract hasn't been upgraded. Use persisted module.
            None => {
                let module_ref = self
                    .contracts
                    .get(&address)
                    .expect("Precondition violation: contract must exist.")
                    .module_reference;
                self.modules
                    .get(&module_ref)
                    .expect("Precondition violation: module must exist.")
                    .clone()
            }
        }
    }

    /// Get the contract state, either from the changeset or by thawing it from
    /// persistence.
    ///
    /// **Preconditions:**
    ///  - Contract instance must exist.
    fn contract_state(&self, address: ContractAddress) -> trie::MutableState {
        match self
            .changeset
            .current()
            .contracts
            .get(&address)
            .and_then(|c| c.state.clone())
        {
            // Contract state has been modified.
            Some(modified_state) => modified_state,
            // Contract state hasn't been modified. Thaw from persistence.
            None => self
                .contracts
                .get(&address)
                .expect("Precondition violation: contract must exist")
                .state
                .thaw(),
        }
    }

    /// Looks up the account balance for an account by first checking
    /// the changeset, then the persisted values.
    fn account_balance(&self, address: AccountAddress) -> Option<AccountBalance> {
        let account_balance = self.accounts.get(&address).map(|a| a.balance)?;
        match self
            .changeset
            .current()
            .accounts
            .get(&address)
            .map(|a| a.current_balance())
        {
            // Account exists in changeset.
            // Return the staked and locked balances from persistence, as they can't change during
            // entrypoint invocation.
            Some(total) => Some(AccountBalance {
                total,
                staked: account_balance.staked,
                locked: account_balance.locked,
            }),
            // Account doesn't exist in changeset.
            None => Some(account_balance),
        }
    }

    /// Saves a mutable state for a contract in the changeset.
    ///
    /// If `with_fresh_generation`, then it will use the
    /// [`MutableState::make_fresh_generation`] function, otherwise it will
    /// make a clone.
    ///
    /// If the contract already has an entry in the changeset, the old state
    /// will be replaced. Otherwise, the entry is created and the state is
    /// added.
    ///
    /// This also increments the modification index. It will be set to 1 if the
    /// contract has no entry in the changeset.
    ///
    /// **Preconditions:**
    ///  - Contract must exist.
    fn save_state_changes(
        &mut self,
        address: ContractAddress,
        state: &mut trie::MutableState,
        with_fresh_generation: bool,
    ) {
        let state = if with_fresh_generation {
            let mut loader = v1::trie::Loader::new(&[][..]); // An empty loader is fine currently, as we do not use caching in this lib.
            state.make_fresh_generation(&mut loader)
        } else {
            state.clone()
        };
        match self.changeset.current_mut().contracts.entry(address) {
            btree_map::Entry::Vacant(vac) => {
                let original_balance = self
                    .contracts
                    .get(&address)
                    .expect("Precondition violation: contract must exist.")
                    .self_balance;
                vac.insert(ContractChanges {
                    state: Some(state),
                    modification_index: 1, // Increment from default, 0, to 1.
                    ..ContractChanges::new(original_balance)
                });
            }
            btree_map::Entry::Occupied(mut occ) => {
                let changes = occ.get_mut();
                changes.state = Some(state);
                changes.modification_index += 1;
            }
        }
    }

    /// Saves a new module reference for the contract in the changeset.
    ///
    /// If the contract already has an entry in the changeset, the old module is
    /// replaced. Otherwise, the entry is created and the module is added.
    ///
    /// Returns the previous module, which is either the one from persistence,
    /// or the most recent one from the changeset.
    ///
    /// **Preconditions:**
    ///  - Contract must exist.
    ///  - Module must exist.
    fn save_module_upgrade(
        &mut self,
        address: ContractAddress,
        module_reference: ModuleReference,
    ) -> ModuleReference {
        match self.changeset.current_mut().contracts.entry(address) {
            btree_map::Entry::Vacant(vac) => {
                let contract = self
                    .contracts
                    .get(&address)
                    .expect("Precondition violation: contract must exist.");
                let old_module_ref = contract.module_reference;
                let original_balance = contract.self_balance;
                vac.insert(ContractChanges {
                    module: Some(module_reference),
                    ..ContractChanges::new(original_balance)
                });
                old_module_ref
            }
            btree_map::Entry::Occupied(mut occ) => {
                let changes = occ.get_mut();
                let old_module_ref = match changes.module {
                    Some(old_module) => old_module,
                    None => {
                        self.contracts
                            .get(&address)
                            .expect("Precondition violation: contract must exist.")
                            .module_reference
                    }
                };
                changes.module = Some(module_reference);
                old_module_ref
            }
        }
    }

    /// Returns the modification index for a contract.
    ///
    /// It looks it up in the changeset, and if it isn't there, it will return
    /// `0`.
    fn modification_index(&self, address: ContractAddress) -> u32 {
        self.changeset
            .current()
            .contracts
            .get(&address)
            .map_or(0, |c| c.modification_index)
    }

    /// Makes a new checkpoint.
    fn checkpoint(&mut self) { self.changeset.checkpoint(); }

    /// Roll back to the previous checkpoint.
    fn rollback(&mut self) { self.changeset.rollback(); }

    /// Update the `remaining_energy` field by converting the input to
    /// [`InterpreterEnergy`] and then [`Energy`].
    fn update_energy(&mut self, remaining_energy: u64) {
        *self.remaining_energy = from_interpreter_energy(InterpreterEnergy::from(remaining_energy));
    }

    /// Run the interpreter with the provided function and the
    /// `self.remaining_energy`.
    ///
    /// This function ensures that the energy calculations is handled as in the
    /// node.
    fn run_interpreter<F>(
        &mut self,
        f: F,
    ) -> Result<v1::ReceiveResult<artifact::CompiledFunction>, OutOfEnergy>
    where
        F: FnOnce(InterpreterEnergy) -> ExecResult<v1::ReceiveResult<artifact::CompiledFunction>>,
    {
        let available_interpreter_energy = to_interpreter_energy(*self.remaining_energy);
        let res = match f(available_interpreter_energy) {
            Ok(res) => res,
            Err(err) => {
                // An error occured in the interpreter and it doesn't return the remaining
                // energy. We convert this to a trap and set the energy to the
                // last known amount.
                return Ok(v1::ReceiveResult::Trap {
                    error:            err,
                    remaining_energy: available_interpreter_energy.energy,
                });
            }
        };
        let mut subtract_then_convert = |remaining_energy| -> Result<u64, OutOfEnergy> {
            let remaining_energy = InterpreterEnergy::from(remaining_energy);
            // Using `saturating_sub` here should be ok since we should never be able to use
            // more energy than what is available.
            let used_energy = from_interpreter_energy(
                available_interpreter_energy.saturating_sub(remaining_energy),
            );
            self.remaining_energy.tick_energy(used_energy)?;
            Ok(to_interpreter_energy(*self.remaining_energy).energy)
        };
        match res {
            v1::ReceiveResult::Success {
                logs,
                state_changed,
                return_value,
                remaining_energy,
            } => Ok(v1::ReceiveResult::Success {
                logs,
                state_changed,
                return_value,
                remaining_energy: subtract_then_convert(remaining_energy)?,
            }),

            v1::ReceiveResult::Interrupt {
                remaining_energy,
                state_changed,
                logs,
                config,
                interrupt,
            } => Ok(v1::ReceiveResult::Interrupt {
                remaining_energy: subtract_then_convert(remaining_energy)?,
                state_changed,
                logs,
                config,
                interrupt,
            }),
            v1::ReceiveResult::Reject {
                reason,
                return_value,
                remaining_energy,
            } => Ok(v1::ReceiveResult::Reject {
                reason,
                return_value,
                remaining_energy: subtract_then_convert(remaining_energy)?,
            }),
            v1::ReceiveResult::Trap {
                error,
                remaining_energy,
            } => Ok(v1::ReceiveResult::Trap {
                error,
                remaining_energy: subtract_then_convert(remaining_energy)?,
            }),
            // Convert this to an error so that we will short-circuit the processing.
            v1::ReceiveResult::OutOfEnergy => Err(OutOfEnergy),
        }
    }
}

impl ChangeSet {
    /// Creates a new changeset with one empty [`Changes`] element on the
    /// stack..
    fn new() -> Self {
        Self {
            stack: vec![Changes {
                contracts: BTreeMap::new(),
                accounts:  BTreeMap::new(),
            }],
        }
    }

    /// Make a checkpoint by putting a clone of the top element onto the stack.
    fn checkpoint(&mut self) {
        let cloned_top_element = self.current().clone();
        self.stack.push(cloned_top_element);
    }

    /// Perform a rollback by popping the top element of the stack.
    fn rollback(&mut self) {
        self.stack
            .pop()
            .expect("Internal error: change set stack should never be empty.");
    }

    /// Get an immutable reference the current (latest) checkpoint.
    fn current(&self) -> &Changes {
        self.stack
            .last()
            .expect("Internal error: change set stack should never be empty.")
    }

    /// Get a mutable reference to the current (latest) checkpoint.
    fn current_mut(&mut self) -> &mut Changes {
        self.stack
            .last_mut()
            .expect("Internal error: change set stack should never be empty.")
    }

    /// Try to persist all changes from the changeset.
    ///
    /// If the energy needed for storing extra state is larger than the
    /// `remaining_energy`, then:
    ///  - no changes will be persisted,
    ///  - an [`OutOfEnergy`] error is returned.
    ///
    /// Otherwise, it returns the [`Energy`] to be charged for the additional
    /// bytes added to contract states. It also returns whether the state of the
    /// provided `invoked_contract` was changed.
    ///
    /// **Preconditions:**
    ///  - All contracts, modules, accounts referred must exist in persistence.
    ///  - All amount deltas must be valid (i.e. not cause underflows when added
    ///    to balance).
    pub(crate) fn persist(
        mut self,
        mut remaining_energy: Energy,
        invoked_contract: ContractAddress,
        persisted_accounts: &mut BTreeMap<AccountAddress, Account>,
        persisted_contracts: &mut BTreeMap<ContractAddress, Contract>,
    ) -> Result<(Energy, bool), OutOfEnergy> {
        let current = self.current_mut();
        let mut invoked_contract_has_state_changes = false;
        // Persist contract changes and collect the total increase in states sizes.
        let mut collector = v1::trie::SizeCollector::default();
        let mut loader = v1::trie::Loader::new(&[][..]); // An empty loader is fine currently, as we do not use caching in this lib.

        let mut frozen_states: BTreeMap<ContractAddress, trie::PersistentState> = BTreeMap::new();

        // Create frozen versions of all the states, to compute the energy needed.
        for (addr, changes) in current.contracts.iter_mut() {
            if let Some(modified_state) = &mut changes.state {
                frozen_states.insert(*addr, modified_state.freeze(&mut loader, &mut collector));
            }
        }

        // One energy per extra byte of state.
        let energy_for_state_increase = Energy::from(collector.collect());

        // Return an error if out of energy.
        remaining_energy.tick_energy(energy_for_state_increase)?;

        // Then persist all the changes.
        for (addr, changes) in current.contracts.iter_mut() {
            let mut contract = persisted_contracts
                .get_mut(addr)
                .expect("Precondition violation: contract must exist");
            // Update balance.
            if !changes.self_balance_delta.is_zero() {
                contract.self_balance = changes
                    .self_balance_delta
                    .apply_to_balance(changes.self_balance_original)
                    .expect("Precondition violation: amount delta causes underflow");
            }
            // Update module reference.
            if let Some(new_module_ref) = changes.module {
                contract.module_reference = new_module_ref;
            }
            // Update state.
            if changes.state.is_some() {
                if *addr == invoked_contract {
                    invoked_contract_has_state_changes = true;
                }
                // Replace with the frozen state we created earlier.
                contract.state = frozen_states
                    .remove(addr)
                    .expect("Known to exist since we just added it.");
            }
        }
        // Persist account changes.
        for (addr, changes) in current.accounts.iter() {
            let mut account = persisted_accounts
                .get_mut(addr)
                .expect("Precondition violation: account must exist");
            // Update balance.
            if !changes.balance_delta.is_zero() {
                account.balance.total = changes
                    .balance_delta
                    .apply_to_balance(changes.original_balance)
                    .expect("Precondition violation: amount delta causes underflow");
            }
        }

        Ok((
            energy_for_state_increase,
            invoked_contract_has_state_changes,
        ))
    }

    /// Traverses the last checkpoint in the changeset and collects the energy
    /// needed to be charged for additional state bytes.
    ///
    /// Returns an [`OutOfEnergy`] error if the energy needed for storing the
    /// extra state is larger than `remaining_energy`.
    ///
    /// Otherwise, it returns
    /// the [`Energy`] needed for storing the extra state. It also returns
    /// whether the state of the provided `invoked_contract` has changed.
    pub(crate) fn collect_energy_for_state(
        mut self,
        mut remaining_energy: Energy,
        invoked_contract: ContractAddress,
    ) -> Result<(Energy, bool), OutOfEnergy> {
        let mut invoked_contract_has_state_changes = false;
        let mut loader = v1::trie::Loader::new(&[][..]); // An empty loader is fine currently, as we do not use caching in this lib.
        let mut collector = v1::trie::SizeCollector::default();
        for (addr, changes) in self.current_mut().contracts.iter_mut() {
            if let Some(modified_state) = &mut changes.state {
                if *addr == invoked_contract {
                    invoked_contract_has_state_changes = true;
                }
                modified_state.freeze(&mut loader, &mut collector);
            }
        }

        // One energy per extra byte in the state.
        let energy_for_state_increase = Energy::from(collector.collect());

        // Return an error if we run out of energy.
        remaining_energy.tick_energy(energy_for_state_increase)?;

        Ok((
            energy_for_state_increase,
            invoked_contract_has_state_changes,
        ))
    }
}

impl Default for ChangeSet {
    fn default() -> Self { Self::new() }
}

impl AmountDelta {
    /// Create a new [`Self`], with the value `+0`.
    fn new() -> Self { Self::Positive(Amount::zero()) }

    /// Subtract an [`Amount`] from [`Self`].
    fn subtract_amount(self, amount: Amount) -> Self {
        match self {
            Self::Positive(current) => {
                if current >= amount {
                    Self::Positive(current.subtract_micro_ccd(amount.micro_ccd))
                } else {
                    Self::Negative(amount.subtract_micro_ccd(current.micro_ccd))
                }
            }
            Self::Negative(current) => Self::Negative(current.add_micro_ccd(amount.micro_ccd)),
        }
    }

    /// Add an [`Amount`] from [`Self`].
    fn add_amount(self, amount: Amount) -> Self {
        match self {
            Self::Positive(current) => Self::Positive(current.add_micro_ccd(amount.micro_ccd)),
            Self::Negative(current) => {
                if current >= amount {
                    Self::Negative(current.subtract_micro_ccd(amount.micro_ccd))
                } else {
                    Self::Positive(amount.subtract_micro_ccd(current.micro_ccd))
                }
            }
        }
    }

    /// Add two [`Self`] to create a new one.
    fn add_delta(self, delta: AmountDelta) -> Self {
        match delta {
            AmountDelta::Positive(d) => self.add_amount(d),
            AmountDelta::Negative(d) => self.subtract_amount(d),
        }
    }

    /// Whether the [`Self`] is zero (either `+0` or `-0`).
    fn is_zero(&self) -> bool {
        match self {
            AmountDelta::Positive(d) => d.micro_ccd == 0,
            AmountDelta::Negative(d) => d.micro_ccd == 0,
        }
    }

    /// Returns a new balance with the `AmountDelta` applied, or, an
    /// error if `balance + self < 0`.
    ///
    /// Panics if an overflow occurs.
    fn apply_to_balance(&self, balance: Amount) -> Result<Amount, UnderflowError> {
        match self {
            AmountDelta::Positive(d) => Ok(balance
                .checked_add(*d)
                .expect("Overflow occured when adding Amounts.")), // TODO: Should we return an
            // error for this?
            AmountDelta::Negative(d) => balance.checked_sub(*d).ok_or(UnderflowError),
        }
    }
}

impl ContractChanges {
    /// Create a new `Self`. The original balance must be provided, all other
    /// fields take on default values.
    fn new(original_balance: Amount) -> Self {
        Self {
            modification_index:    0,
            self_balance_delta:    AmountDelta::new(),
            self_balance_original: original_balance,
            state:                 None,
            module:                None,
        }
    }

    /// Get the current balance by adding the original balance and the balance
    /// delta.
    ///
    /// **Preconditions:**
    ///  - `balance_delta + original_balance` must be larger than `0`.
    fn current_balance(&self) -> Amount {
        self.self_balance_delta
            .apply_to_balance(self.self_balance_original)
            .expect("Precondition violation: invalid `balance_delta`.")
    }
}

impl AccountChanges {
    /// Get the current balance by adding the original balance and the balance
    /// delta.
    ///
    /// **Preconditions:**
    ///  - `balance_delta + original_balance` must be larger than `0`.
    fn current_balance(&self) -> Amount {
        self.balance_delta
            .apply_to_balance(self.original_balance)
            .expect("Precondition violation: invalid `balance_delta`.")
    }
}

impl<'a, 'b> InvocationData<'a, 'b> {
    /// Process a receive function until completion.
    ///
    /// **Preconditions**:
    ///  - Contract instance exists in `invocation_handler.contracts`.
    ///  - Account exists in `invocation_handler.accounts`.
    fn process(
        &mut self,
        receive_result: v1::ReceiveResult<artifact::CompiledFunction>,
    ) -> Result<v1::ReceiveResult<artifact::CompiledFunction>, OutOfEnergy> {
        match receive_result {
            v1::ReceiveResult::Success {
                logs,
                state_changed,
                return_value,
                remaining_energy,
            } => {
                // Update the remaining_energy field.
                self.invocation_handler.update_energy(remaining_energy);

                let update_event = ChainEvent::Updated {
                    address:    self.address,
                    contract:   self.contract_name.clone(),
                    entrypoint: self.entrypoint.clone(),
                    amount:     self.amount,
                };
                // Add update event
                self.chain_events.push(update_event);

                // Save changes to changeset.
                if state_changed {
                    self.invocation_handler.save_state_changes(
                        self.address,
                        &mut self.state,
                        false,
                    );
                }

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
                // Update the remaining_energy field.
                self.invocation_handler.update_energy(remaining_energy);
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

                        let response = match self
                            .invocation_handler
                            .transfer_from_contract_to_account(amount, self.address, to)
                        {
                            Ok(new_balance) => v1::InvokeResponse::Success {
                                new_balance,
                                data: None,
                            },
                            Err(err) => {
                                let kind = match err {
                                    TransferError::ToMissing => {
                                        v1::InvokeFailure::NonExistentAccount
                                    }
                                    TransferError::InsufficientBalance => {
                                        v1::InvokeFailure::InsufficientAmount
                                    }
                                };
                                v1::InvokeResponse::Failure { kind }
                            }
                        };

                        let success = matches!(response, v1::InvokeResponse::Success { .. });
                        if success {
                            // Add transfer event
                            self.chain_events.push(ChainEvent::Transferred {
                                from: self.address,
                                amount,
                                to,
                            });
                        }
                        // Add resume event
                        self.chain_events.push(ChainEvent::Resumed {
                            address: self.address,
                            success,
                        });

                        self.invocation_handler
                            .remaining_energy
                            .tick_energy(concordium_base::transactions::cost::SIMPLE_TRANSFER)?;

                        let resume_res = self.invocation_handler.run_interpreter(|energy| {
                            v1::resume_receive(
                                config,
                                response,
                                energy,
                                &mut self.state,
                                false, // never changes on transfers
                                // An empty loader is fine currently, as we do not use caching
                                // in this lib.
                                v1::trie::Loader::new(&[][..]),
                            )
                        })?;

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
                            self.invocation_handler.save_state_changes(
                                self.address,
                                &mut self.state,
                                true,
                            );
                        }

                        // Save the modification index before the invoke.
                        let mod_idx_before_invoke =
                            self.invocation_handler.modification_index(self.address);

                        // Make a checkpoint before calling another contract so that we may roll
                        // back.
                        self.invocation_handler.checkpoint();

                        let res = match self
                            .invocation_handler
                            .contracts
                            .get(&address)
                            .map(|c| c.contract_name.as_contract_name())
                        {
                            // The contract to call does not exist.
                            None => InvokeEntrypointResult {
                                invoke_response: v1::InvokeResponse::Failure {
                                    kind: v1::InvokeFailure::NonExistentContract,
                                },
                                logs:            v0::Logs::new(),
                            },
                            Some(contract_name) => {
                                let receive_name = OwnedReceiveName::construct_unchecked(
                                    contract_name,
                                    name.as_entrypoint_name(),
                                );
                                let message = OwnedParameter::new_unchecked(parameter);
                                self.invocation_handler.invoke_entrypoint(
                                    self.invoker,
                                    Address::Contract(self.address),
                                    UpdateContractPayload {
                                        amount,
                                        address,
                                        receive_name,
                                        message,
                                    },
                                    &mut self.chain_events,
                                )?
                            }
                        };

                        let success = res.is_success();

                        // Remove the last state changes if the invocation failed.
                        let state_changed = if !success {
                            self.invocation_handler.rollback();
                            false // We rolled back, so no changes were made
                                  // to this contract.
                        } else {
                            let mod_idx_after_invoke =
                                self.invocation_handler.modification_index(self.address);
                            let state_changed = mod_idx_after_invoke != mod_idx_before_invoke;
                            if state_changed {
                                // Update the state field with the newest value from the
                                // changeset.
                                self.state = self.invocation_handler.contract_state(self.address);
                            }
                            state_changed
                        };

                        // Add resume event
                        let resume_event = ChainEvent::Resumed {
                            address: self.address,
                            success,
                        };

                        self.chain_events.push(resume_event);

                        let resume_res = self.invocation_handler.run_interpreter(|energy| {
                            v1::resume_receive(
                                config,
                                res.invoke_response,
                                energy,
                                &mut self.state,
                                state_changed,
                                v1::trie::Loader::new(&[][..]),
                            )
                        })?;

                        self.process(resume_res)
                    }
                    v1::Interrupt::Upgrade { module_ref } => {
                        // Add the interrupt event.
                        self.chain_events.push(interrupt_event);

                        // Charge a base cost.
                        self.invocation_handler
                            .remaining_energy
                            .tick_energy(constants::INITIALIZE_CONTRACT_INSTANCE_BASE_COST)?;

                        let response = match self.invocation_handler.modules.get(&module_ref) {
                            None => v1::InvokeResponse::Failure {
                                kind: v1::InvokeFailure::UpgradeInvalidModuleRef,
                            },
                            Some(module) => {
                                // Charge for the module lookup.
                                self.invocation_handler
                                    .remaining_energy
                                    .tick_energy(lookup_module_cost(module))?;

                                if module.artifact.export.contains_key(
                                    self.contract_name.as_contract_name().get_chain_name(),
                                ) {
                                    // Update module reference in the changeset.
                                    let old_module_ref = self
                                        .invocation_handler
                                        .save_module_upgrade(self.address, module_ref);

                                    // Charge for the initialization cost.
                                    self.invocation_handler.remaining_energy.tick_energy(
                                        constants::INITIALIZE_CONTRACT_INSTANCE_CREATE_COST,
                                    )?;

                                    let upgrade_event = ChainEvent::Upgraded {
                                        address: self.address,
                                        from:    old_module_ref,
                                        to:      module_ref,
                                    };

                                    self.chain_events.push(upgrade_event);

                                    v1::InvokeResponse::Success {
                                        new_balance: self
                                            .invocation_handler
                                            .contract_balance_unchecked(self.address),
                                        data:        None,
                                    }
                                } else {
                                    v1::InvokeResponse::Failure {
                                        kind: v1::InvokeFailure::UpgradeInvalidContractName,
                                    }
                                }
                            }
                        };

                        let success = matches!(response, v1::InvokeResponse::Success { .. });
                        self.chain_events.push(ChainEvent::Resumed {
                            address: self.address,
                            success,
                        });

                        let resume_res = self.invocation_handler.run_interpreter(|energy| {
                            v1::resume_receive(
                                config,
                                response,
                                energy,
                                &mut self.state,
                                state_changed,
                                v1::trie::Loader::new(&[][..]),
                            )
                        })?;

                        self.process(resume_res)
                    }
                    v1::Interrupt::QueryAccountBalance { address } => {
                        let response = match self.invocation_handler.account_balance(address) {
                            Some(balance) => v1::InvokeResponse::Success {
                                new_balance: self
                                    .invocation_handler
                                    .contract_balance_unchecked(self.address),
                                data:        Some(to_bytes(&balance)),
                            },
                            None => v1::InvokeResponse::Failure {
                                kind: v1::InvokeFailure::NonExistentAccount,
                            },
                        };

                        self.invocation_handler
                            .remaining_energy
                            .tick_energy(constants::CONTRACT_INSTANCE_QUERY_ACCOUNT_BALANCE_COST)?;

                        let resume_res = self.invocation_handler.run_interpreter(|energy| {
                            v1::resume_receive(
                                config,
                                response,
                                energy,
                                &mut self.state,
                                false, // State never changes on queries.
                                v1::trie::Loader::new(&[][..]),
                            )
                        })?;

                        self.process(resume_res)
                    }
                    v1::Interrupt::QueryContractBalance { address } => {
                        let response = match self.invocation_handler.contract_balance(address) {
                            None => v1::InvokeResponse::Failure {
                                kind: v1::InvokeFailure::NonExistentContract,
                            },
                            Some(bal) => v1::InvokeResponse::Success {
                                // Balance of contract querying. Won't change. Notice the
                                // `self.address`.
                                new_balance: self
                                    .invocation_handler
                                    .contract_balance_unchecked(self.address),
                                data:        Some(to_bytes(&bal)),
                            },
                        };

                        self.invocation_handler.remaining_energy.tick_energy(
                            constants::CONTRACT_INSTANCE_QUERY_CONTRACT_BALANCE_COST,
                        )?;

                        let resume_res = self.invocation_handler.run_interpreter(|energy| {
                            v1::resume_receive(
                                config,
                                response,
                                energy,
                                &mut self.state,
                                false, // State never changes on queries.
                                v1::trie::Loader::new(&[][..]),
                            )
                        })?;

                        self.process(resume_res)
                    }
                    v1::Interrupt::QueryExchangeRates => {
                        let exchange_rates = ExchangeRates {
                            euro_per_energy:    self.invocation_handler.euro_per_energy,
                            micro_ccd_per_euro: self.invocation_handler.micro_ccd_per_euro,
                        };

                        let response = v1::InvokeResponse::Success {
                            new_balance: self
                                .invocation_handler
                                .contract_balance_unchecked(self.address),
                            data:        Some(to_bytes(&exchange_rates)),
                        };

                        self.invocation_handler
                            .remaining_energy
                            .tick_energy(constants::CONTRACT_INSTANCE_QUERY_EXCHANGE_RATE_COST)?;

                        let resume_res = self.invocation_handler.run_interpreter(|energy| {
                            v1::resume_receive(
                                config,
                                response,
                                energy,
                                &mut self.state,
                                false, // State never changes on queries.
                                v1::trie::Loader::new(&[][..]),
                            )
                        })?;

                        self.process(resume_res)
                    }
                }
            }
            v1::ReceiveResult::Reject {
                reason,
                return_value,
                remaining_energy,
            } => {
                self.invocation_handler.update_energy(remaining_energy);
                Ok(v1::ReceiveResult::Reject {
                    reason,
                    return_value,
                    remaining_energy,
                })
            }
            v1::ReceiveResult::Trap {
                error,
                remaining_energy,
            } => {
                self.invocation_handler.update_energy(remaining_energy);
                Ok(v1::ReceiveResult::Trap {
                    error,
                    remaining_energy,
                })
            }
            // Convert this to an error here, so that we will short circuit processing.
            v1::ReceiveResult::OutOfEnergy => Err(OutOfEnergy),
        }
    }
}

impl InvokeEntrypointResult {
    /// Whether the invoke was successful.
    pub(crate) fn is_success(&self) -> bool {
        matches!(self.invoke_response, v1::InvokeResponse::Success { .. })
    }
}

impl From<UnderflowError> for InsufficientBalanceError {
    fn from(_: UnderflowError) -> Self { InsufficientBalanceError }
}

impl From<InsufficientBalanceError> for TransferError {
    fn from(_: InsufficientBalanceError) -> Self { Self::InsufficientBalance }
}

#[cfg(test)]
mod tests {
    mod amount_delta {
        use crate::{invocation::types::AmountDelta, Amount};
        #[test]
        fn test() {
            let mut x = AmountDelta::new();
            assert_eq!(x, AmountDelta::Positive(Amount::zero()));

            let one = Amount::from_ccd(1);
            let two = Amount::from_ccd(2);
            let three = Amount::from_ccd(3);
            let five = Amount::from_ccd(5);

            x = x.subtract_amount(one); // -1 CCD
            x = x.subtract_amount(one); // -2 CCD
            assert_eq!(x, AmountDelta::Negative(two));
            x = x.add_amount(five); // +3 CCD
            assert_eq!(x, AmountDelta::Positive(three));
            x = x.subtract_amount(five); // -2 CCD
            assert_eq!(x, AmountDelta::Negative(two));
            x = x.add_amount(two); // 0

            x = x.add_amount(Amount::from_micro_ccd(1)); // 1 mCCD
            assert_eq!(x, AmountDelta::Positive(Amount::from_micro_ccd(1)));
            x = x.subtract_amount(Amount::from_micro_ccd(2)); // -1 mCCD
            assert_eq!(x, AmountDelta::Negative(Amount::from_micro_ccd(1)));
        }
    }
}
