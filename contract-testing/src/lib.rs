use concordium_base::{
    base::{Energy, ExchangeRate},
    common,
    contracts_common::*,
    smart_contracts::{ModuleSource, WasmModule, WasmVersion},
    transactions::{self, cost},
};
use num_bigint::BigUint;
use sha2::{Digest, Sha256};
use std::{
    collections::{btree_map, BTreeMap},
    path::Path,
    sync::Arc,
};
use thiserror::Error;
use wasm_chain_integration::{
    v0,
    v1::{
        self,
        trie::{MutableState, PersistentState, SizeCollector},
        ConcordiumAllowedImports, InvokeFailure, InvokeResponse, ReturnValue,
    },
    ExecResult, InterpreterEnergy,
};
use wasm_transform::artifact;
mod constants;

/// A V1 artifact, with concrete types for the generic parameters.
type ContractModule = artifact::Artifact<v1::ProcessedImports, artifact::CompiledFunction>;

/// Whether the current [`Changes`] should be printed before and after an
/// internal contract invoke. TODO: Remove before publishing.
const VERBOSE_DEBUG: bool = false;

/// Represents the block chain and supports a number of operations, including
/// creating accounts, deploying modules, initializing contract, updating
/// contracts and invoking contracts.
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
    pub modules:             BTreeMap<ModuleReference, Arc<ContractModule>>,
    /// Smart contract instances.
    pub contracts:           BTreeMap<ContractAddress, Contract>,
    /// Next contract index to use when creating a new instance.
    pub next_contract_index: u64,
    /// The changeset used during a contract update or invocation.
    changeset:               ChangeSet,
}

/// A smart contract instance along.
#[derive(Clone)]
pub struct Contract {
    /// The module which contains this contract.
    pub module_reference: ModuleReference,
    /// The name of the contract.
    pub contract_name:    OwnedContractName,
    /// The contract state.
    pub state:            v1::trie::PersistentState,
    /// The owner of the contract.
    pub owner:            AccountAddress,
    /// The balance of the contract.
    pub self_balance:     Amount,
}

/// A positive or negative delta in for an [`Amount`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AmountDelta {
    /// A posittive delta.
    Positive(Amount),
    /// A negative delta.
    Negative(Amount),
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

/// Data held for a contract during the execution of a contract update or
/// invocation.
#[derive(Clone, Debug)]
pub struct ContractChanges {
    /// An index that is used to check whether a caller contract has been
    /// modified after invoking another contract (due to reentrancy).
    modification_index:    u32,
    /// Represents how much the contract's self balance has changed.
    self_balance_delta:    AmountDelta,
    /// The original contract balance, i.e. the one that is persisted. Should
    /// never be modified.
    self_balance_original: Amount,
    /// The potentially modified contract state.
    state:                 Option<MutableState>,
    /// The potentially changed module.
    module:                Option<ModuleReference>,
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
    /// *Preconditions:*
    ///  - `balance_delta + original_balance` must be larger than `0`.
    fn current_balance(&self) -> Amount {
        self.self_balance_delta
            .apply_to_balance(self.self_balance_original)
            .expect("Precondition violation: invalid `balance_delta`.")
    }
}

/// Data held for an account during the execution of an update or invoke
/// transaction.
#[derive(Clone, Debug)]
pub struct AccountChanges {
    /// Should never be modified.
    original_balance: Amount,
    balance_delta:    AmountDelta,
}

impl AccountChanges {
    /// Get the current balance by adding the original balance and the balance
    /// delta.
    ///
    /// *Preconditions:*
    ///  - `balance_delta + original_balance` must be larger than `0`.
    fn current_balance(&self) -> Amount {
        self.balance_delta
            .apply_to_balance(self.original_balance)
            .expect("Precondition violation: invalid `balance_delta`.")
    }
}

/// Data held for accounts and contracts during the execution of a contract
/// update or invocation.
#[derive(Clone, Debug)]
struct Changes {
    /// The contracts which have changes.
    contracts: BTreeMap<ContractAddress, ContractChanges>,
    /// The accounts which have changes.
    accounts:  BTreeMap<AccountAddress, AccountChanges>,
}

/// The set of [`Changes`] represented as a stack.
#[derive(Debug)]
struct ChangeSet {
    /// The stack of changes.
    stack: Vec<Changes>,
}

/// The message to use when an internal error occurs in the changeset.
const INTERNAL_CHANGESET_ERROR_MESSAGE: &str =
    "Internal error: change set stack should never be empty.";

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
    fn rollback(&mut self) { self.stack.pop().expect(INTERNAL_CHANGESET_ERROR_MESSAGE); }

    /// Get an immutable reference the current (latest) checkpoint.
    fn current(&self) -> &Changes { self.stack.last().expect(INTERNAL_CHANGESET_ERROR_MESSAGE) }

    /// Get a mutable reference to the current (latest) checkpoint.
    fn current_mut(&mut self) -> &mut Changes {
        self.stack
            .last_mut()
            .expect(INTERNAL_CHANGESET_ERROR_MESSAGE)
    }

    /// Clear all changes.
    ///
    /// This replaces the `Self` with a completely new `Self`.
    fn clear(&mut self) { *self = Self::new() }
}

impl Default for Chain {
    fn default() -> Self { Self::new() }
}

// Private methods
impl Chain {
    /// Check whether an account exists.
    fn persistence_account_exists(&self, address: AccountAddress) -> bool {
        self.accounts.contains_key(&address)
    }

    /// Check whether a contract exists.
    fn persistence_contract_exists(&self, address: ContractAddress) -> bool {
        self.contracts.contains_key(&address)
    }

    /// Check whether the address exists in persistence. I.e. if it is an
    /// account, whether the account exists, and if it is a contract, whether
    /// the contract exists.
    fn persistence_address_exists(&self, address: Address) -> bool {
        match address {
            Address::Account(acc) => self.persistence_account_exists(acc),
            Address::Contract(contr) => self.persistence_contract_exists(contr),
        }
    }

    /// Make a transfer from a contract to an account in the changeset.
    /// Returns the new balance of `from`.
    ///
    /// Precondition:
    /// - Assumes that `from` contract exists.
    fn changeset_transfer_contract_to_account(
        &mut self,
        amount: Amount,
        from: ContractAddress,
        to: AccountAddress,
    ) -> Result<Amount, TransferError> {
        // Ensure the `to` account exists.
        if !self.persistence_account_exists(to) {
            return Err(TransferError::ToMissing);
        }

        // Make the transfer.
        let new_balance =
            self.changeset_change_contract_balance(from, AmountDelta::Negative(amount))?;
        self.changeset_change_account_balance(to, AmountDelta::Positive(amount))
            .expect("Cannot fail when adding");

        Ok(new_balance)
    }

    /// Make a transfer between contracts in the changeset.
    /// Returns the new balance of `from`.
    ///
    /// Precondition:
    /// - Assumes that `from` contract exists.
    fn changeset_transfer_contract_to_contract(
        &mut self,
        amount: Amount,
        from: ContractAddress,
        to: ContractAddress,
    ) -> Result<Amount, TransferError> {
        // Ensure the `to` contract exists.
        if !self.persistence_contract_exists(to) {
            return Err(TransferError::ToMissing);
        }

        // Make the transfer.
        let new_balance =
            self.changeset_change_contract_balance(from, AmountDelta::Negative(amount))?;
        self.changeset_change_contract_balance(to, AmountDelta::Positive(amount))
            .expect("Cannot fail when adding");

        Ok(new_balance)
    }

    /// Make a transfer from an account to a contract in the changeset.
    /// Returns the new balance of `from`.
    ///
    /// Precondition:
    /// - Assumes that `from` account exists.
    fn changeset_transfer_account_to_contract(
        &mut self,
        amount: Amount,
        from: AccountAddress,
        to: ContractAddress,
    ) -> Result<Amount, TransferError> {
        // Ensure the `to` account exists.
        if !self.persistence_contract_exists(to) {
            return Err(TransferError::ToMissing);
        }

        // Make the transfer.
        let new_balance =
            self.changeset_change_account_balance(from, AmountDelta::Negative(amount))?;
        self.changeset_change_contract_balance(to, AmountDelta::Positive(amount))
            .expect("Cannot fail when adding");
        Ok(new_balance)
    }

    // TODO: Should we handle overflows explicitly?
    /// Changes the contract balance in the topmost checkpoint on the changeset.
    /// If contract isn't already present in the changeset, it is added.
    /// Returns the new balance.
    ///
    /// Precondition:
    ///  - Contract must exist.
    fn changeset_change_contract_balance(
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
    /// If account isn't already present in the changeset, it is added.
    /// Returns the new balance.
    ///
    /// Precondition:
    ///  - Account must exist.
    fn changeset_change_account_balance(
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
                    .balance;
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
    /// *Preconditions:*
    ///  - Contract must exist.
    fn changeset_contract_balance_unchecked(&self, address: ContractAddress) -> Amount {
        self.changeset_contract_balance(address)
            .expect("Precondition violation: contract must exist")
    }

    /// Looks up the contract balance from the topmost checkpoint on the
    /// changeset. Or, alternatively, from persistence.
    fn changeset_contract_balance(&self, address: ContractAddress) -> Option<Amount> {
        match self.changeset.current().contracts.get(&address) {
            Some(changes) => Some(changes.current_balance()),
            None => self.contracts.get(&address).map(|c| c.self_balance),
        }
    }

    /// Returns the contract module from the topmost checkpoint on
    /// the changeset. Or, alternatively, from persistence.
    ///
    /// *Preconditions:*
    ///  - Contract instance must exist (and therefore also the artifact).
    ///  - If the changeset contains a module reference, then it must refer a
    ///    deployed module.
    fn changeset_contract_module(&self, address: ContractAddress) -> Arc<ContractModule> {
        match self
            .changeset
            .current()
            .contracts
            .get(&address)
            .and_then(|c| c.module)
        {
            // Contract has been upgrade, new module exists.
            Some(new_module) => Arc::clone(
                self.modules
                    .get(&new_module)
                    .expect("Precondition violation: module must exist."),
            ),
            // Contract hasn't been upgraded. Use persisted module.
            None => {
                let module_ref = self
                    .contracts
                    .get(&address)
                    .expect("Precondition violation: contract must exist.")
                    .module_reference;
                Arc::clone(
                    self.modules
                        .get(&module_ref)
                        .expect("Precondition violation: module must exist."),
                )
            }
        }
    }

    /// Get the contract state, either from the changeset or by thawing it from
    /// persistence.
    ///
    /// *Preconditions:*
    ///  - Contract instance must exist.
    fn changeset_contract_state(&self, address: ContractAddress) -> MutableState {
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

    /// Looks up the account balance for an account by first checking the
    /// changeset, then the persisted values.
    fn changeset_account_balance(&self, address: AccountAddress) -> Option<Amount> {
        match self
            .changeset
            .current()
            .accounts
            .get(&address)
            .map(|a| a.current_balance())
        {
            // Account exists in changeset.
            Some(bal) => Some(bal),
            // Account doesn't exist in changeset.
            None => self.accounts.get(&address).map(|a| a.balance),
        }
    }

    /// Try to persist all changes from the changeset.
    ///
    /// Always clears the changeset.
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
    /// *Preconditions:*
    ///  - All contracts, modules, accounts referred must exist in persistence.
    ///  - All amount deltas must be valid (i.e. not cause underflows when added
    ///    to balance).
    fn changeset_persist_and_clear(
        &mut self,
        remaining_energy: Energy,
        invoked_contract: ContractAddress,
    ) -> Result<(Energy, bool), OutOfEnergy> {
        let mut invoked_contract_has_state_changes = false;
        let changes = self.changeset.current_mut();
        // Persist contract changes and collect the total increase in states sizes.
        let mut collector = SizeCollector::default();
        let mut loader = v1::trie::Loader::new(&[][..]);

        let mut frozen_states: BTreeMap<ContractAddress, PersistentState> = BTreeMap::new();

        // Create frozen versions of all the states, to compute the energy needed.
        for (addr, changes) in changes.contracts.iter_mut() {
            if let Some(modified_state) = &mut changes.state {
                frozen_states.insert(*addr, modified_state.freeze(&mut loader, &mut collector));
            }
        }

        // One energy per extra byte of state.
        let energy_for_state_increase = Energy::from(collector.collect());

        // Return an error if out of energy, and clear the changeset.
        if remaining_energy
            .checked_sub(energy_for_state_increase)
            .is_none()
        {
            self.changeset_clear();
            return Err(OutOfEnergy);
        }

        // Then persist all the changes.
        for (addr, changes) in changes.contracts.iter_mut() {
            let mut contract = self
                .contracts
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
        for (addr, changes) in changes.accounts.iter() {
            let mut account = self
                .accounts
                .get_mut(addr)
                .expect("Precondition violation: account must exist");
            // Update balance.
            if !changes.balance_delta.is_zero() {
                account.balance = changes
                    .balance_delta
                    .apply_to_balance(changes.original_balance)
                    .expect("Precondition violation: amount delta causes underflow");
            }
        }
        // Clear the changeset.
        self.changeset_clear();

        Ok((
            energy_for_state_increase,
            invoked_contract_has_state_changes,
        ))
    }

    /// Traverses the last checkpoint in the changeset and collects the energy
    /// needed to be charged for additional state bytes.
    ///
    /// Always clears the changeset.
    ///
    /// Returns an [`OutOfEnergy`] error if the energy needed for storing the
    /// extra state is larger than `remaining_energy`.
    ///
    /// Otherwise, it returns
    /// the [`Energy`] needed for storing the extra state. It also returns
    /// whether the state of the provided `invoked_contract` has changed.
    fn changeset_collect_energy_for_state_and_clear(
        &mut self,
        remaining_energy: Energy,
        invoked_contract: ContractAddress,
    ) -> Result<(Energy, bool), OutOfEnergy> {
        let mut invoked_contract_has_state_changes = false;
        let mut loader = v1::trie::Loader::new(&[][..]);
        let mut collector = SizeCollector::default();
        for (addr, changes) in self.changeset.current_mut().contracts.iter_mut() {
            if let Some(modified_state) = &mut changes.state {
                if *addr == invoked_contract {
                    invoked_contract_has_state_changes = true;
                }
                modified_state.freeze(&mut loader, &mut collector);
            }
        }
        // Clear the changeset.
        self.changeset_clear();

        // One energy per extra byte in the state.
        let energy_for_state_increase = Energy::from(collector.collect());

        if remaining_energy
            .checked_sub(energy_for_state_increase)
            .is_none()
        {
            return Err(OutOfEnergy);
        }
        Ok((
            energy_for_state_increase,
            invoked_contract_has_state_changes,
        ))
    }

    /// Saves a mutable state for a contract in the changeset.
    ///
    /// If the contract already has an entry in the changeset, the old state
    /// will be replaced. Otherwise, the entry is created and the state is
    /// added.
    ///
    /// This also increments the modification index. It will be set to 1 if the
    /// contract has no entry in the changeset.
    ///
    /// *Preconditions:*
    ///  - Contract must exist.
    fn changeset_save_state_changes(&mut self, address: ContractAddress, state: &mut MutableState) {
        let mut loader = v1::trie::Loader::new(&[][..]);
        self.changeset
            .current_mut()
            .contracts
            .entry(address)
            .and_modify(|changes| {
                changes.state = Some(state.make_fresh_generation(&mut loader));
                changes.modification_index += 1;
            })
            .or_insert({
                let original_balance = self
                    .contracts
                    .get(&address)
                    .expect("Precondition violation: contract must exist.")
                    .self_balance;
                ContractChanges {
                    state: Some(state.make_fresh_generation(&mut loader)),
                    modification_index: 1, // Increment from default, 0, to 1.
                    ..ContractChanges::new(original_balance)
                }
            });
    }

    /// Saves a new module reference for the contract in the changeset.
    ///
    /// If the contract already has an entry in the changeset, the old module is
    /// replaced. Otherwise, the entry is created and the module is added.
    ///
    /// Returns the previous module, which is either the one from persistence,
    /// or the most recent one from the changeset.
    ///
    /// *Preconditions:*
    ///  - Contract must exist.
    ///  - Module must exist.
    fn changeset_save_module_upgrade(
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
    fn changeset_modification_index(&self, address: ContractAddress) -> u32 {
        self.changeset
            .current()
            .contracts
            .get(&address)
            .map_or(0, |c| c.modification_index)
    }

    /// Clears the changeset.
    fn changeset_clear(&mut self) { self.changeset.clear(); }

    /// Makes a new checkpoint.
    fn changeset_checkpoint(&mut self) { self.changeset.checkpoint(); }

    /// Roll back to the previous checkpoint.
    fn changeset_rollback(&mut self) { self.changeset.rollback(); }
}

/// A transfer of [`Amount`]s failed because the sender had insufficient
/// balance.
#[derive(Debug)]
struct InsufficientBalanceError;

/// An underflow occurred.
#[derive(Debug)]
struct UnderflowError;

impl From<UnderflowError> for InsufficientBalanceError {
    fn from(_: UnderflowError) -> Self { InsufficientBalanceError }
}

impl From<InsufficientBalanceError> for TransferError {
    fn from(_: InsufficientBalanceError) -> Self { Self::InsufficientBalance }
}

struct UpdateAuxResponse {
    /// The result from the invoke.
    invoke_response:  InvokeResponse,
    /// Will be `Some` if and only if `invoke_response` is `Success`.
    logs:             Option<v0::Logs>,
    /// The remaining energy after the invocation.
    remaining_energy: InterpreterEnergy,
}

impl UpdateAuxResponse {
    fn is_success(&self) -> bool { matches!(self.invoke_response, InvokeResponse::Success { .. }) }
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
            changeset: ChangeSet::new(),
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
                + wasm_module.source.size()
                + transactions::construct::TRANSACTION_HEADER_SIZE;
            let number_of_sigs = self.persistence_get_account(sender)?.signature_count;
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
        let account = self.persistence_get_account_mut(sender)?;
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
        parameter: OwnedParameter,
        amount: Amount,
        energy_reserved: Energy,
    ) -> Result<SuccessfulContractInit, ContractInitError> {
        // Lookup artifact
        let artifact = self.persistence_contract_module(module_reference)?;
        let mut transaction_fee = self.calculate_energy_cost(self.lookup_module_cost(&artifact));
        // Get the account and check that it has sufficient balance to pay for the
        // reserved_energy and amount.
        let account_info = self.persistence_get_account(sender)?;
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
        );
        // Handle the result and update the transaction fee.
        // TODO: Extract to helper function.
        let res = match res {
            Ok(v1::InitResult::Success {
                logs,
                return_value: _, /* Ignore return value for now, since our tools do not support
                                  * it for inits, currently. */
                remaining_energy,
                mut state,
            }) => {
                let contract_address = self.create_contract_address();
                let energy_used = energy_reserved
                    - Chain::from_interpreter_energy(InterpreterEnergy {
                        energy: remaining_energy,
                    });
                transaction_fee += self.calculate_energy_cost(energy_used);

                let mut collector = v1::trie::SizeCollector::default();

                let contract_instance = Contract {
                    module_reference,
                    contract_name: contract_name.to_owned(),
                    state: state.freeze(&mut loader, &mut collector), // TODO: Charge for storage.
                    owner: sender,
                    self_balance: amount,
                };

                // Save the contract instance
                self.contracts.insert(contract_address, contract_instance);
                // Subtract the from the invoker.
                self.persistence_get_account_mut(sender)?.balance -= amount;

                Ok(SuccessfulContractInit {
                    contract_address,
                    logs,
                    energy_used,
                    transaction_fee,
                })
            }
            Ok(v1::InitResult::Reject {
                reason,
                return_value,
                remaining_energy,
            }) => {
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
                    },
                ))
            }
            Ok(v1::InitResult::Trap {
                error: _, // TODO: Should we forward this to the user?
                remaining_energy,
            }) => {
                let energy_used = energy_reserved
                    - Chain::from_interpreter_energy(InterpreterEnergy {
                        energy: remaining_energy,
                    });
                transaction_fee += self.calculate_energy_cost(energy_used);
                Err(ContractInitError::ValidChainError(
                    FailedContractInteraction::Trap {
                        energy_used,
                        transaction_fee,
                    },
                ))
            }
            Ok(v1::InitResult::OutOfEnergy) => {
                transaction_fee += self.calculate_energy_cost(energy_reserved);
                Err(ContractInitError::ValidChainError(
                    FailedContractInteraction::OutOfEnergy {
                        energy_used: energy_reserved,
                        transaction_fee,
                    },
                ))
            }
            Err(e) => panic!("Internal error: init failed with interpreter error: {}", e),
        };
        // Charge the account.
        // We have to get the account info again because of the borrow checker.
        self.persistence_get_account_mut(sender)?.balance -= transaction_fee;
        res
    }

    /// Used for handling contract invokes internally.
    ///
    /// *Preconditions:*
    ///  - `invoker` exists
    ///  - `invoker` has sufficient balance to pay for `remaining_energy`
    ///  - `sender` exists
    ///  - if the contract (`contract_address`) exists, then its `module` must
    ///    also exist.
    fn contract_update_aux(
        &mut self,
        invoker: AccountAddress,
        sender: Address,
        contract_address: ContractAddress,
        entrypoint: OwnedEntrypointName,
        parameter: Parameter,
        amount: Amount,
        // The CCD amount reserved from the invoker account. While the amount
        // is reserved, it is not subtracted in the chain.accounts map.
        // Used to handle account balance queries for the invoker account.
        invoker_amount_reserved_for_nrg: Amount,
        // Uses [`Interpreter`] energy to avoid rounding issues when converting to and fro
        // [`Energy`].
        mut remaining_energy: InterpreterEnergy,
        chain_events: &mut Vec<ChainEvent>,
    ) -> UpdateAuxResponse {
        // Move the amount from the sender to the contract, if any.
        // And get the new self_balance.
        let instance_self_balance = if amount.micro_ccd() > 0 {
            let transfer_result = match sender {
                Address::Account(sender_account) => self.changeset_transfer_account_to_contract(
                    amount,
                    sender_account,
                    contract_address,
                ),
                Address::Contract(sender_contract) => self.changeset_transfer_contract_to_contract(
                    amount,
                    sender_contract,
                    contract_address,
                ),
            };
            match transfer_result {
                Ok(new_balance_from) => new_balance_from,
                Err(transfer_error) => {
                    let kind = match transfer_error {
                        TransferError::InsufficientBalance => InvokeFailure::InsufficientAmount,
                        TransferError::ToMissing => InvokeFailure::NonExistentContract,
                    };
                    // Return early.
                    // TODO: Should we charge any energy for this?
                    return UpdateAuxResponse {
                        invoke_response: InvokeResponse::Failure { kind },
                        logs: None,
                        remaining_energy,
                    };
                }
            }
        } else {
            match self.changeset_contract_balance(contract_address) {
                Some(self_balance) => self_balance,
                None => {
                    // Return early.
                    // TODO: For the top-most update, we should catch this in `contract_update` and
                    // return `ContractUpdateError::EntrypointMissing`.
                    return UpdateAuxResponse {
                        invoke_response: InvokeResponse::Failure {
                            kind: InvokeFailure::NonExistentContract,
                        },
                        logs: None,
                        remaining_energy,
                    };
                }
            }
        };

        // Get the instance and artifact. To be used in several places.
        let instance = self
            .persistence_get_contract(contract_address)
            .expect("Contract known to exist at this point");
        let artifact = self.changeset_contract_module(contract_address);

        // Subtract the cost of looking up the module
        remaining_energy = remaining_energy
            .subtract(Chain::to_interpreter_energy(self.lookup_module_cost(&artifact)).energy);

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
                // Return early.
                return UpdateAuxResponse {
                    invoke_response: InvokeResponse::Failure {
                        kind: InvokeFailure::NonExistentEntrypoint,
                    },
                    logs: None,
                    remaining_energy,
                };
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
                self_address: contract_address,
                self_balance: instance_self_balance,
                sender,
                owner: instance.owner,
                sender_policies: self
                    .persistence_get_account(invoker)
                    .expect("Precondition violation: invoker must exist.")
                    .policies
                    .clone(),
            },
        };

        let contract_name = instance.contract_name.clone();

        // Construct the instance state
        let mut loader = v1::trie::Loader::new(&[][..]);
        let mut mutable_state = self.changeset_contract_state(contract_address);
        let inner = mutable_state.get_inner(&mut loader);
        let instance_state = v1::InstanceState::new(loader, inner);

        // Get the initial result from invoking receive
        let initial_result = v1::invoke_receive(
            artifact,
            receive_ctx,
            v1::ReceiveInvocation {
                amount,
                receive_name: receive_name.as_receive_name(),
                parameter: parameter.0,
                energy: remaining_energy,
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
            address: contract_address,
            contract_name,
            amount,
            invoker_amount_reserved_for_nrg,
            entrypoint,
            chain: self,
            state: mutable_state,
            chain_events: Vec::new(),
            loader,
        };

        // Process the receive invocation to the completion.
        let result = data.process(initial_result);
        let mut new_chain_events = data.chain_events;

        let result = match result {
            Ok(r) => match r {
                v1::ReceiveResult::Success {
                    logs,
                    state_changed: _, /* This only reflects changes since last interrupt, we use
                                       * the changeset later to get a more precise result. */
                    return_value,
                    remaining_energy,
                } => {
                    let remaining_energy = InterpreterEnergy::from(remaining_energy);
                    UpdateAuxResponse {
                        invoke_response: InvokeResponse::Success {
                            new_balance: self
                                .changeset_contract_balance_unchecked(contract_address),
                            data:        Some(return_value),
                        },
                        logs: Some(logs),
                        remaining_energy,
                    }
                }
                v1::ReceiveResult::Interrupt { .. } => {
                    panic!("Internal error: `data.process` returned an interrupt.")
                }
                v1::ReceiveResult::Reject {
                    reason,
                    return_value,
                    remaining_energy,
                } => {
                    let remaining_energy = InterpreterEnergy::from(remaining_energy);
                    UpdateAuxResponse {
                        invoke_response: InvokeResponse::Failure {
                            kind: InvokeFailure::ContractReject {
                                code: reason,
                                data: return_value,
                            },
                        },
                        logs: None,
                        remaining_energy,
                    }
                }
                v1::ReceiveResult::Trap {
                    error: _, // TODO: Should we return this to the user?
                    remaining_energy,
                } => {
                    let remaining_energy = InterpreterEnergy::from(remaining_energy);
                    UpdateAuxResponse {
                        invoke_response: InvokeResponse::Failure {
                            kind: InvokeFailure::RuntimeError,
                        },
                        logs: None,
                        remaining_energy,
                    }
                }
                v1::ReceiveResult::OutOfEnergy => {
                    let remaining_energy = InterpreterEnergy::from(0);
                    UpdateAuxResponse {
                        invoke_response: InvokeResponse::Failure {
                            kind: InvokeFailure::RuntimeError,
                        },
                        logs: None,
                        remaining_energy,
                    }
                }
            },
            Err(internal_error) => {
                panic!("Internal error: Got interpreter error {}", internal_error)
            }
        };

        // Append the new chain events if the invocation succeeded.
        if result.is_success() {
            chain_events.append(&mut new_chain_events);
        }

        result
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
        if !self.persistence_address_exists(sender) {
            return Err(ContractUpdateError::SenderDoesNotExist(sender));
        }

        // Ensure account exists and can pay for the reserved energy and amount
        // TODO: Could we just remove this amount in the changeset and then put back the
        // to_ccd(remaining_energy) afterwards?
        let account_info = self.persistence_get_account(invoker)?;
        let invoker_amount_reserved_for_nrg = self.calculate_energy_cost(energy_reserved);
        if account_info.balance < invoker_amount_reserved_for_nrg + amount {
            return Err(ContractUpdateError::InsufficientFunds);
        }

        // TODO: Should chain events be part of the changeset?
        let mut chain_events = Vec::new();
        let result = self.contract_update_aux(
            invoker,
            sender,
            contract_address,
            entrypoint.to_owned(),
            Parameter(&parameter.0),
            amount,
            invoker_amount_reserved_for_nrg,
            Chain::to_interpreter_energy(energy_reserved),
            &mut chain_events,
        );

        // Get the energy to be charged for extra state bytes. Or return an error if out
        // of energy.
        let (energy_for_state_increase, state_changed) = if result.is_success() {
            match self.changeset_persist_and_clear(
                Chain::from_interpreter_energy(result.remaining_energy),
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
            // An error occured, so we don't save the changes. Just clear.
            self.changeset_clear();
            (Energy::from(0), false)
        };

        let (res, transaction_fee) = self.convert_update_aux_response(
            result,
            chain_events,
            energy_reserved,
            energy_for_state_increase,
            state_changed,
        );

        // Charge the transaction fee irrespective of the result.
        // TODO: If we charge up front, then we should return to_ccd(remaining_energy)
        // here instead.
        self.persistence_get_account_mut(invoker)?.balance -= transaction_fee;
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
        if !self.persistence_address_exists(sender) {
            return Err(ContractUpdateError::SenderDoesNotExist(sender));
        }

        // Ensure account exists and can pay for the reserved energy and amount
        let account_info = self.persistence_get_account(invoker)?;
        let invoker_amount_reserved_for_nrg = self.calculate_energy_cost(energy_reserved);
        if account_info.balance < invoker_amount_reserved_for_nrg + amount {
            return Err(ContractUpdateError::InsufficientFunds);
        }

        let mut chain_events = Vec::new();
        let result = self.contract_update_aux(
            invoker,
            sender,
            contract_address,
            entrypoint.to_owned(),
            Parameter(&parameter.0),
            amount,
            invoker_amount_reserved_for_nrg,
            Chain::to_interpreter_energy(energy_reserved),
            &mut chain_events,
        );

        let (energy_for_state_increase, state_changed) = if result.is_success() {
            match self.changeset_collect_energy_for_state_and_clear(
                Chain::from_interpreter_energy(result.remaining_energy),
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
            // An error occured, so we just clear the changeset.
            self.changeset_clear();
            (Energy::from(0), false)
        };

        let (result, _) = self.convert_update_aux_response(
            result,
            chain_events,
            energy_reserved,
            energy_for_state_increase,
            state_changed,
        );

        result
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
    /// This will always be the persisted account balance.
    pub fn persistence_account_balance(&self, address: AccountAddress) -> Option<Amount> {
        self.accounts.get(&address).map(|ai| ai.balance)
    }

    /// Returns the balance of an contract if it exists.
    /// This will always be the persisted contract balance.
    pub fn persistence_contract_balance(&self, address: ContractAddress) -> Option<Amount> {
        self.contracts.get(&address).map(|ci| ci.self_balance)
    }

    /// Calculate the microCCD(mCCD) cost of energy(NRG) using the two exchange
    /// rates available:
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
    pub fn calculate_energy_cost(&self, energy: Energy) -> Amount {
        let micro_ccd_per_energy_numerator: BigUint =
            BigUint::from(self.euro_per_energy.numerator()) * self.micro_ccd_per_euro.numerator();
        let micro_ccd_per_energy_denominator: BigUint =
            BigUint::from(self.euro_per_energy.denominator())
                * self.micro_ccd_per_euro.denominator();
        let cost: BigUint =
            (micro_ccd_per_energy_numerator * energy.energy) / micro_ccd_per_energy_denominator;
        let cost: u64 = u64::try_from(cost).expect("Should never overflow due to use of BigUint");
        Amount::from_micro_ccd(cost)
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

    /// Calculate the energy energy for looking up a [`ContractModule`].
    fn lookup_module_cost(&self, module: &ContractModule) -> Energy {
        // TODO: Is it just the `.code`?
        // Comes from Concordium/Cost.hs::lookupModule
        Energy::from(module.code.len() as u64 / 50)
    }

    /// Returns an Arc clone of the [`ContractModule`] from persistence.
    fn persistence_contract_module(
        &self,
        module_ref: ModuleReference,
    ) -> Result<Arc<ContractModule>, ModuleMissing> {
        let module = self
            .modules
            .get(&module_ref)
            .ok_or(ModuleMissing(module_ref))?;
        Ok(Arc::clone(module))
    }

    /// Returns an immutable reference to a [`Contract`] from persistence.
    fn persistence_get_contract(
        &self,
        address: ContractAddress,
    ) -> Result<&Contract, ContractInstanceMissing> {
        self.contracts
            .get(&address)
            .ok_or(ContractInstanceMissing(address))
    }

    /// Returns an immutable reference to [`AccountInfo`] from persistence.
    fn persistence_get_account(
        &self,
        address: AccountAddress,
    ) -> Result<&AccountInfo, AccountMissing> {
        self.accounts.get(&address).ok_or(AccountMissing(address))
    }

    /// Returns a mutable reference to [`AccountInfo`] from persistence.
    fn persistence_get_account_mut(
        &mut self,
        address: AccountAddress,
    ) -> Result<&mut AccountInfo, AccountMissing> {
        self.accounts
            .get_mut(&address)
            .ok_or(AccountMissing(address))
    }

    /// Convert the wasm_chain_integration result to the one used here and
    /// calculate the transaction fee.
    ///
    /// The `energy_for_state_increase` is only used if the result was a
    /// success.
    ///
    /// The `state_changed` should refer to whether the state of the top-level
    /// contract invoked has changed.
    ///
    /// *Preconditions*:
    /// - `energy_reserved - remaining_energy + energy_for_state_increase >= 0`
    fn convert_update_aux_response(
        &self,
        update_aux_response: UpdateAuxResponse,
        chain_events: Vec<ChainEvent>,
        energy_reserved: Energy,
        energy_for_state_increase: Energy,
        state_changed: bool,
    ) -> (
        Result<SuccessfulContractUpdate, ContractUpdateError>,
        Amount,
    ) {
        let remaining_energy = Chain::from_interpreter_energy(update_aux_response.remaining_energy);
        match update_aux_response.invoke_response {
            InvokeResponse::Success { new_balance, data } => {
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
            InvokeResponse::Failure { kind } => {
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
}

/// Errors related to transfers.
#[derive(PartialEq, Eq, Debug, Error)]
enum TransferError {
    /// The receiver does not exist.
    #[error("The receiver does not exist.")]
    ToMissing,
    /// The sender does not have sufficient balance.
    #[error("The sender does not have sufficient balance.")]
    InsufficientBalance,
}

/// The contract ran out of energy during execution of an update or invocation.
#[derive(PartialEq, Eq, Debug)]
struct OutOfEnergy;

/// The entrypoint does not exist.
#[derive(PartialEq, Eq, Debug, Error)]
#[error("The entrypoint '{0}' does not exist.")]
pub struct EntrypointDoesNotExist(OwnedEntrypointName);

/// Data needed to recursively process a contract update or invocation to
/// completion.
struct ProcessReceiveData<'a, 'b> {
    /// The invoker.
    invoker: AccountAddress,
    /// The contract being called.
    address: ContractAddress,
    /// The name of the contract.
    contract_name: OwnedContractName,
    /// The amount sent from the sender to the contract.
    amount: Amount,
    /// The CCD amount reserved from the invoker account for the energy. While
    /// the amount is reserved, it is not subtracted in the chain.accounts
    /// map. Used to handle account balance queries for the invoker account.
    /// TODO: We could use a changeset for accounts -> balance, and then look up
    /// the "chain.accounts" values for chain queries.
    invoker_amount_reserved_for_nrg: Amount,
    /// The entrypoint to execute.
    entrypoint: OwnedEntrypointName,
    /// A reference to the chain.
    chain: &'a mut Chain,
    /// The current state.
    state: MutableState,
    /// Chain events that have occurred during the execution.
    chain_events: Vec<ChainEvent>,
    ///
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
                    // Add update event
                    self.chain_events.push(update_event);

                    // Save changes to changeset.
                    if state_changed {
                        self.chain
                            .changeset_save_state_changes(self.address, &mut self.state);
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

                            println!("\t\tTransferring {} CCD to {}", amount, to);

                            let response = match self.chain.changeset_transfer_contract_to_account(
                                amount,
                                self.address,
                                to,
                            ) {
                                Ok(new_balance) => InvokeResponse::Success {
                                    new_balance,
                                    data: None,
                                },
                                Err(err) => {
                                    let kind = match err {
                                        TransferError::ToMissing => {
                                            InvokeFailure::NonExistentAccount
                                        }
                                        TransferError::InsufficientBalance => {
                                            InvokeFailure::InsufficientAmount
                                        }
                                    };
                                    InvokeResponse::Failure { kind }
                                }
                            };

                            let success = matches!(response, InvokeResponse::Success { .. });
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

                            let resume_res = v1::resume_receive(
                                config,
                                response,
                                InterpreterEnergy::from(remaining_energy),
                                &mut self.state,
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
                                self.chain
                                    .changeset_save_state_changes(self.address, &mut self.state);
                            }

                            // Save the modification index before the invoke.
                            let mod_idx_before_invoke =
                                self.chain.changeset_modification_index(self.address);

                            // Make a checkpoint before calling another contract so that we may roll
                            // back.
                            self.chain.changeset_checkpoint();

                            if VERBOSE_DEBUG {
                                println!(
                                    "Before call (after checkpoint): {:#?}",
                                    self.chain.changeset.current()
                                );
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
                                InterpreterEnergy::from(remaining_energy),
                                &mut self.chain_events,
                            );

                            let success = res.is_success();

                            // Remove the last state changes if the invocation failed.
                            let state_changed = if !success {
                                self.chain.changeset_rollback();
                                false // We rolled back, so no changes were made
                                      // to this contract.
                            } else {
                                let mod_idx_after_invoke =
                                    self.chain.changeset_modification_index(self.address);
                                let state_changed = mod_idx_after_invoke != mod_idx_before_invoke;
                                if state_changed {
                                    // Update the state field with the newest value from the
                                    // changeset.
                                    self.state = self.chain.changeset_contract_state(self.address);
                                }
                                state_changed
                            };

                            if VERBOSE_DEBUG {
                                println!(
                                    "After call (and potential rollback):\n{:#?}",
                                    self.chain.changeset.current()
                                );
                            }

                            println!(
                                "\tResuming contract {}\n\t\tafter {}",
                                self.address,
                                if success {
                                    "succesful invocation"
                                } else {
                                    "failed invocation"
                                }
                            );

                            // Add resume event
                            let resume_event = ChainEvent::Resumed {
                                address: self.address,
                                success,
                            };

                            self.chain_events.push(resume_event);

                            let resume_res = v1::resume_receive(
                                config,
                                res.invoke_response,
                                res.remaining_energy,
                                &mut self.state,
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
                                    constants::INITIALIZE_CONTRACT_INSTANCE_BASE_COST,
                                )
                                .energy;

                            let response = match self.chain.modules.get(&module_ref) {
                                None => InvokeResponse::Failure {
                                    kind: InvokeFailure::UpgradeInvalidModuleRef,
                                },
                                Some(module) => {
                                    // Charge for the module lookup.
                                    energy_after_invoke -= Chain::to_interpreter_energy(
                                        self.chain.lookup_module_cost(module),
                                    )
                                    .energy;

                                    if module.export.contains_key(
                                        self.contract_name.as_contract_name().get_chain_name(),
                                    ) {
                                        // Update module reference in the changeset.
                                        let old_module_ref =
                                            self.chain.changeset_save_module_upgrade(
                                                self.address,
                                                module_ref,
                                            );

                                        // Charge for the initialization cost.
                                        energy_after_invoke -= Chain::to_interpreter_energy(
                                            constants::INITIALIZE_CONTRACT_INSTANCE_CREATE_COST,
                                        )
                                        .energy;

                                        let upgrade_event = ChainEvent::Upgraded {
                                            address: self.address,
                                            from:    old_module_ref,
                                            to:      module_ref,
                                        };

                                        self.chain_events.push(upgrade_event);

                                        InvokeResponse::Success {
                                            new_balance: self
                                                .chain
                                                .changeset_contract_balance_unchecked(self.address),
                                            data:        None,
                                        }
                                    } else {
                                        InvokeResponse::Failure {
                                            kind: InvokeFailure::UpgradeInvalidContractName,
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
                                &mut self.state,
                                state_changed,
                                self.loader,
                            );

                            self.process(resume_res)
                        }
                        v1::Interrupt::QueryAccountBalance { address } => {
                            println!("\t\tQuerying account balance of {}", address);
                            // When querying an account, the amounts from any `invoke_transfer`s
                            // should be included. That is handled by
                            // the `chain` struct already. transaction.
                            // However, that is hand
                            let response = match self.chain.changeset_account_balance(address) {
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
                                            .changeset_contract_balance_unchecked(self.address),
                                        data:        Some(balances),
                                    }
                                }
                                None => InvokeResponse::Failure {
                                    kind: InvokeFailure::NonExistentAccount,
                                },
                            };

                            let energy_after_invoke = remaining_energy
                                - Chain::to_interpreter_energy(
                                    constants::CONTRACT_INSTANCE_QUERY_ACCOUNT_BALANCE_COST,
                                )
                                .energy;

                            let resume_res = v1::resume_receive(
                                config,
                                response,
                                InterpreterEnergy::from(energy_after_invoke),
                                &mut self.state,
                                false, // State never changes on queries.
                                self.loader,
                            );

                            self.process(resume_res)
                        }
                        v1::Interrupt::QueryContractBalance { address } => {
                            println!("Querying contract balance of {}", address);

                            let response = match self.chain.changeset_contract_balance(address) {
                                None => InvokeResponse::Failure {
                                    kind: InvokeFailure::NonExistentContract,
                                },
                                Some(bal) => InvokeResponse::Success {
                                    // Balance of contract querying. Won't change. Notice the
                                    // `self.address`.
                                    new_balance: self
                                        .chain
                                        .changeset_contract_balance_unchecked(self.address),
                                    data:        Some(to_bytes(&bal)),
                                },
                            };

                            let energy_after_invoke = remaining_energy
                                - Chain::to_interpreter_energy(
                                    constants::CONTRACT_INSTANCE_QUERY_CONTRACT_BALANCE_COST,
                                )
                                .energy;

                            let resume_res = v1::resume_receive(
                                config,
                                response,
                                InterpreterEnergy::from(energy_after_invoke),
                                &mut self.state,
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
                                new_balance: self
                                    .chain
                                    .changeset_contract_balance_unchecked(self.address),
                                data:        Some(to_bytes(&exchange_rates)),
                            };

                            let energy_after_invoke = remaining_energy
                                - Chain::to_interpreter_energy(
                                    constants::CONTRACT_INSTANCE_QUERY_EXCHANGE_RATE_COST,
                                )
                                .energy;

                            let resume_res = v1::resume_receive(
                                config,
                                response,
                                InterpreterEnergy::from(energy_after_invoke),
                                &mut self.state,
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

/// The contract module does not exist.
#[derive(Debug, Error)]
#[error("Module {:?} does not exist.", 0)]
pub struct ModuleMissing(ModuleReference);

/// The contract instance does not exist.
#[derive(Debug, Error)]
#[error("Contract instance {0} does not exist.")]
pub struct ContractInstanceMissing(ContractAddress);

/// The account does not exist.
#[derive(Debug, Error)]
#[error("Account {0} does not exist.")]
pub struct AccountMissing(AccountAddress);

/// Data about an [`AccountAddress`].
#[derive(Clone)]
pub struct AccountInfo {
    /// The account balance. TODO: Add all three types of balances.
    pub balance:     Amount,
    /// Account policies.
    policies:        v0::OwnedPolicyBytes,
    /// The number of signatures. The number of signatures affect the cost of
    /// every transaction for the account.
    signature_count: u32,
}

/// Account policies for testing.
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

/// Errors that can occur while initializing a contract.
#[derive(Debug, Error)]
pub enum ContractInitError {
    /// Initialization failed for a reason that also exists on the chain.
    #[error("failed due to a valid chain error: {:?}", 0)]
    ValidChainError(FailedContractInteraction),
    /// Module has not been deployed in the test environment.
    #[error("module {:?} does not exist", 0.0)]
    ModuleDoesNotExist(#[from] ModuleMissing),
    /// Account has not been created in test environment.
    #[error("account {} does not exist", 0.0)]
    AccountDoesNotExist(#[from] AccountMissing),
    /// The account does not have enough funds to pay for the energy.
    #[error("account does not have enough funds to pay for the energy")]
    InsufficientFunds,
}

/// Errors that can occur during a [`Chain::contract_update]` or
/// [`Chain::contract_invoke`] call.
///
/// There are two categories of errors here:
///  - `ExecutionError` and `OutOfEnergy` can occur if the preconditions for the
///    function is valid, and a contract is executed.
///  - The rest represent incorrect usage of the function, where some
///    precondition wasn't met.
#[derive(Debug, Error)]
pub enum ContractUpdateError {
    /// Update failed for a reason that also exists on the chain.
    #[error("failed during execution")]
    ExecutionError {
        failure_kind:    InvokeFailure,
        energy_used:     Energy,
        transaction_fee: Amount,
    },
    #[error("ran out of energy")]
    OutOfEnergy {
        energy_used:     Energy,
        transaction_fee: Amount,
    },
    /// Module has not been deployed in test environment.
    #[error("module {:?} does not exist", 0.0)]
    ModuleDoesNotExist(#[from] ModuleMissing),
    /// Contract instance has not been initialized in the test environment.
    #[error("instance {} does not exist", 0.0)]
    InstanceDoesNotExist(#[from] ContractInstanceMissing),
    /// Entrypoint does not exist and neither does the fallback entrypoint.
    #[error("entrypoint does not exist")]
    EntrypointDoesNotExist(#[from] EntrypointDoesNotExist),
    /// The invoker account has not been created in the test environment.
    #[error("invoker account {} does not exist", 0.0)]
    InvokerDoesNotExist(#[from] AccountMissing),
    /// The sender does not exist in the test environment.
    #[error("sender {0} does not exist")]
    SenderDoesNotExist(Address),
    /// The account does not have enough funds to pay for the energy.
    #[error("account does not have enough funds to pay for the energy")]
    InsufficientFunds,
}

/// Represents a failed contract interaction, i.e. an initialization, update, or
/// invocation.
#[derive(Debug)]
pub enum FailedContractInteraction {
    /// The contract rejected.
    Reject {
        /// The error code for why it rejected.
        reason:          i32,
        /// The return value.
        return_value:    ReturnValue,
        /// The amount of energy used before rejecting.
        energy_used:     Energy,
        /// The transaction fee to be paid by the invoker for the interaction.
        transaction_fee: Amount,
    },
    /// The contract trapped.
    Trap {
        /// The amount of energy used before rejecting.
        energy_used:     Energy,
        /// The transaction fee to be paid by the invoker for the interaction.
        transaction_fee: Amount,
    },
    /// The contract ran out of energy.
    OutOfEnergy {
        /// The amount of energy used before rejecting.
        energy_used:     Energy,
        /// The transaction fee to be paid by the invoker for the interaction.
        transaction_fee: Amount,
    },
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

/// An error that can occur while deploying a [`ContractModule`].
// TODO: Can we get Eq for this when using io::Error?
// TODO: Should this also have the energy used?
#[derive(Debug, Error)]
pub enum DeployModuleError {
    /// Failed to read the module file.
    #[error("could not read the file due to: {0}")]
    ReadFileError(#[from] std::io::Error),
    /// The module provided is not valid.
    #[error("module is invalid due to: {0}")]
    InvalidModule(#[from] anyhow::Error),
    /// The account does not have sufficient funds to pay for the deployment.
    #[error("account does not have sufficient funds to pay for the energy")]
    InsufficientFunds,
    /// The account deploying the module does not exist.
    #[error("account {} does not exist", 0.0)]
    AccountDoesNotExist(#[from] AccountMissing),
    /// The module version is not supported.
    #[error("wasm version {0} is not supported")]
    UnsupportedModuleVersion(WasmVersion),
    /// The module has already been deployed.
    #[error("module with reference {:?} already exists", 0)]
    DuplicateModule(ModuleReference),
}

/// An event that occurred during a contract update or invocation.
#[derive(Debug)]
pub enum ChainEvent {
    /// A contract was interrupted.
    Interrupted {
        /// The contract interrupted.
        address: ContractAddress,
        /// Logs produced prior to being interrupted.
        logs:    v0::Logs,
    },
    /// A contract was resumed after being interrupted.
    Resumed {
        /// The contract resumed.
        address: ContractAddress,
        /// Whether the action that caused the interrupt succeeded.
        success: bool,
    },
    /// A contract was upgraded.
    Upgraded {
        /// The contract upgraded.
        address: ContractAddress,
        /// The old module reference.
        from:    ModuleReference,
        /// The new module reference.
        to:      ModuleReference,
    },
    /// A contract was updated.
    Updated {
        /// The contract updated.
        address:    ContractAddress,
        /// The name of the contract.
        contract:   OwnedContractName,
        /// The entrypoint called.
        entrypoint: OwnedEntrypointName,
        /// The amount added to the contract.
        amount:     Amount,
    },
    /// A contract transferred an [`Amount`] to an account.
    Transferred {
        /// The sender contract.
        from:   ContractAddress,
        /// The [`Amount`] transferred.
        amount: Amount,
        /// The receiver account.
        to:     AccountAddress,
    },
}

/// Represents a successful contract update (or invocation).
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
    pub return_value:    ReturnValue,
    /// Whether the state was changed.
    pub state_changed:   bool,
    /// The new balance of the smart contract.
    pub new_balance:     Amount,
    /// The logs produced since the last interrupt.
    pub logs:            v0::Logs,
}

/// A transfer from an contract to an account.
#[derive(Debug, PartialEq, Eq)]
pub struct Transfer {
    /// The sender contract.
    pub from:   ContractAddress,
    /// The amount transferred.
    pub amount: Amount,
    /// The receive account.
    pub to:     AccountAddress,
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
}

/// Represents a successful deployment of a [`ContractModule`].
#[derive(Debug, PartialEq, Eq)]
pub struct SuccessfulModuleDeployment {
    /// The reference of the module deployed.
    pub module_reference: ModuleReference,
    /// The energy used for deployment.
    pub energy:           Energy,
    /// Cost of transaction.
    pub transaction_fee:  Amount,
}

/// Represents a successful initialization of a contract.
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
        assert_eq!(
            chain.persistence_account_balance(ACC_0),
            Some(Amount::from_ccd(1))
        );
        assert_eq!(
            chain.persistence_account_balance(ACC_1),
            Some(Amount::from_ccd(2))
        );
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
            chain.persistence_account_balance(ACC_0),
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
                OwnedParameter::from_bytes(vec![0u8]),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");
        assert_eq!(
            chain.persistence_account_balance(ACC_0),
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
                OwnedParameter::from_bytes(vec![99u8]), // Invalid param
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
                chain.persistence_account_balance(ACC_0),
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
                OwnedParameter::from_bytes(vec![0u8]), // Starts as 0
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");

        let res_update = chain
            .contract_update(
                ACC_0,
                Address::Account(ACC_0),
                res_init.contract_address,
                EntrypointName::new_unchecked("set"),
                OwnedParameter::from_bytes(vec![1u8]), // Updated to 1
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Updating valid contract should work");

        let res_invoke_get = chain
            .contract_invoke(
                ACC_0,
                Address::Contract(res_init.contract_address), // Invoke with a contract as sender.
                res_init.contract_address,
                EntrypointName::new_unchecked("get"),
                OwnedParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Invoking get should work");

        // This also asserts that the account wasn't charged for the invoke.
        assert_eq!(
            chain.persistence_account_balance(ACC_0),
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
        assert_eq!(res_invoke_get.return_value, [1u8]);
    }

    /// Test that updates and invocations where the sender is missing fail.
    #[test]
    fn updating_and_invoking_with_missing_sender_fails() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let missing_account = Address::Account(ACC_1);
        let missing_contract = Address::Contract(ContractAddress::new(100, 0));

        let res_deploy = chain
            .module_deploy_v1(ACC_0, "examples/icecream/icecream.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_weather"),
                OwnedParameter::from_bytes(vec![0u8]), // Starts as 0
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");

        let res_update_acc = chain.contract_update(
            ACC_0,
            missing_account,
            res_init.contract_address,
            EntrypointName::new_unchecked("get"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        );

        let res_invoke_acc = chain.contract_invoke(
            ACC_0,
            missing_account,
            res_init.contract_address,
            EntrypointName::new_unchecked("get"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        );

        let res_update_contr = chain.contract_update(
            ACC_0,
            missing_contract,
            res_init.contract_address,
            EntrypointName::new_unchecked("get"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        );

        let res_invoke_contr = chain.contract_invoke(
            ACC_0,
            missing_contract,
            res_init.contract_address,
            EntrypointName::new_unchecked("get"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        );

        assert!(matches!(
            res_update_acc,
            Err(ContractUpdateError::SenderDoesNotExist(addr)) if addr == missing_account));
        assert!(matches!(
            res_invoke_acc,
            Err(ContractUpdateError::SenderDoesNotExist(addr)) if addr == missing_account));
        assert!(matches!(
            res_update_contr,
            Err(ContractUpdateError::SenderDoesNotExist(addr)) if addr == missing_contract));
        assert!(matches!(
            res_invoke_contr,
            Err(ContractUpdateError::SenderDoesNotExist(addr)) if addr == missing_contract));
    }

    /// Tests using the integrate contract defined in
    /// concordium-rust-smart-contract on the 'kb/sc-integration-testing'
    /// branch.
    mod integrate_contract {
        use super::*;

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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("receive"),
                    OwnedParameter::new(&ACC_1),
                    transfer_amount,
                    Energy::from(10000),
                )
                .expect("Updating valid contract should work");

            let res_view = chain
                .contract_invoke(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("view"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Invoking get should work");

            // This also asserts that the account wasn't charged for the invoke.
            assert_eq!(
                chain.persistence_account_balance(ACC_0),
                Some(
                    initial_balance
                        - res_deploy.transaction_fee
                        - res_init.transaction_fee
                        - res_update.transaction_fee
                        - transfer_amount
                )
            );
            assert_eq!(
                chain.persistence_account_balance(ACC_1),
                Some(initial_balance + transfer_amount)
            );
            assert_eq!(res_update.transfers(), [Transfer {
                from:   res_init.contract_address,
                amount: transfer_amount,
                to:     ACC_1,
            }]);
            assert_eq!(chain.contracts.len(), 1);
            assert!(res_update.state_changed);
            assert_eq!(res_update.return_value, [2, 0, 0, 0]);
            // Assert that the updated state is persisted.
            assert_eq!(res_view.return_value, [2, 0, 0, 0]);
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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain.contract_update(
                ACC_0,
                Address::Account(ACC_0),
                res_init.contract_address,
                EntrypointName::new_unchecked("receive"),
                OwnedParameter::new(&ACC_1), // We haven't created ACC_1.
                transfer_amount,
                Energy::from(100000),
            );

            match res_update {
                Err(ContractUpdateError::ExecutionError {
                    failure_kind: InvokeFailure::ContractReject { code, .. },
                    transaction_fee,
                    ..
                }) => {
                    assert_eq!(code, -3); // The custom contract error code for missing account.
                    assert_eq!(
                        chain.persistence_account_balance(ACC_0),
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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("recurse"),
                    OwnedParameter::new(&10u32),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect("Updating valid contract should work");

            let res_view = chain
                .contract_invoke(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("view"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Invoking get should work");

            // This also asserts that the account wasn't charged for the invoke.
            assert_eq!(
                chain.persistence_account_balance(ACC_0),
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
            assert_eq!(res_update.return_value, u32::to_le_bytes(expected_res));
            // Assert that the updated state is persisted.
            assert_eq!(res_view.return_value, u32::to_le_bytes(expected_res));
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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("inc-fail-on-zero"),
                    OwnedParameter::new(&input_param),
                    Amount::zero(),
                    Energy::from(100000000),
                )
                .expect("Updating valid contract should work");

            let res_view = chain
                .contract_invoke(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("view"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Invoking get should work");

            assert_eq!(
                chain.persistence_account_balance(ACC_0),
                Some(
                    initial_balance
                        - res_deploy.transaction_fee
                        - res_init.transaction_fee
                        - res_update.transaction_fee
                )
            );
            assert!(res_update.state_changed);
            let expected_res = 2u32.pow(input_param) - 1;
            assert_eq!(res_update.return_value, u32::to_le_bytes(expected_res));
            // Assert that the updated state is persisted.
            assert_eq!(res_view.return_value, u32::to_le_bytes(expected_res));
        }

        #[test]
        fn rollback_of_account_balances_after_failed_contract_invoke() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(10000);
            let transfer_amount = Amount::from_ccd(2);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));
            chain.create_account(ACC_1, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_v1(ACC_0, "examples/integrate/a.wasm.v1")
                .expect("Deploying valid module should work");

            let res_init_0 = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_integrate"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_init_1 = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_integrate_other"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let param = (res_init_1.contract_address, initial_balance, ACC_1);

            chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init_0.contract_address,
                    EntrypointName::new_unchecked("mutate_and_forward"),
                    OwnedParameter::new(&param),
                    transfer_amount,
                    Energy::from(100000),
                )
                .expect("Update should succeed");
        }
    }
    // TODO: Add tests that check:
    // - Correct account balances after init / update failures (when Amount > 0)

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
                OwnedParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");

        let res_update = chain
            .contract_update(
                ACC_0,
                Address::Account(ACC_0),
                res_init.contract_address,
                EntrypointName::new_unchecked("receive"),
                OwnedParameter::new(&6u64),
                Amount::zero(),
                Energy::from(4000000),
            )
            .expect("Updating valid contract should work");

        let res_view = chain
            .contract_invoke(
                ACC_0,
                Address::Account(ACC_0),
                res_init.contract_address,
                EntrypointName::new_unchecked("view"),
                OwnedParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Invoking get should work");

        // This also asserts that the account wasn't charged for the invoke.
        assert_eq!(
            chain.persistence_account_balance(ACC_0),
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
        assert_eq!(res_update.return_value, expected_res);
        // Assert that the updated state is persisted.
        assert_eq!(res_view.return_value, expected_res);
    }

    #[test]
    fn calculate_cost_will_not_overflow() {
        let chain = Chain::new_with_time_and_rates(
            SlotTime::from_timestamp_millis(0),
            ExchangeRate::new_unchecked(u64::MAX, u64::MAX - 1),
            ExchangeRate::new_unchecked(u64::MAX - 2, u64::MAX - 3),
        );

        let energy = Energy::from(u64::MAX - 4);
        chain.calculate_energy_cost(energy);
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
                    OwnedParameter::empty(),
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
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert_eq!(
                chain.persistence_account_balance(ACC_0),
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
                    OwnedParameter::empty(),
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
                    Address::Account(ACC_1),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
                    update_amount,
                    energy_limit,
                )
                .expect("Updating valid contract should work");

            assert_eq!(
                chain.persistence_account_balance(ACC_0),
                Some(initial_balance - res_deploy.transaction_fee - res_init.transaction_fee)
            );
            assert_eq!(
                chain.persistence_account_balance(ACC_1),
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
                    OwnedParameter::empty(),
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
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Updating valid contract should work");

            assert_eq!(
                chain.persistence_account_balance(ACC_0),
                Some(
                    initial_balance
                        - res_deploy.transaction_fee
                        - res_init.transaction_fee
                        - res_update.transaction_fee
                        - amount_to_send
                )
            );
            assert_eq!(
                chain.persistence_account_balance(ACC_1),
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
                    OwnedParameter::empty(),
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
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert_eq!(
                chain.persistence_account_balance(ACC_0),
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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            // The account to query, which doesn't exist in this test case.
            let input_param = ACC_1;

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert_eq!(
                chain.persistence_account_balance(ACC_0),
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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_init_other = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    init_amount, // Set up another contract with `init_amount` balance
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            // check that the other contract has `self_balance == init_amount`.
            let input_param = (res_init_other.contract_address, init_amount);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
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
                    OwnedParameter::empty(),
                    init_amount,
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            // check that the other contract has `self_balance == init_amount`.
            let input_param = (res_init.contract_address, init_amount + update_amount);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
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
                    OwnedParameter::empty(),
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
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            // Non-existent contract address.
            let input_param = ContractAddress::new(123, 456);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            // Non-existent contract address.
            let input_param = (chain.euro_per_energy, chain.micro_ccd_per_euro);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            // Upgrade the contract to the `upgrading_1` module by calling the `bump`
            // entrypoint.
            let res_update_upgrade = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("bump"),
                    OwnedParameter::new(&res_deploy_1.module_reference),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            // Call the `newfun` entrypoint which only exists in `upgrading_1`.
            let res_update_new = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("newfun"),
                    OwnedParameter::new(&res_deploy_1.module_reference),
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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    OwnedParameter::new(&res_deploy_1.module_reference),
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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    OwnedParameter::empty(),
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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    OwnedParameter::new(&res_deploy_1.module_reference),
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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let input_param = (res_deploy_1.module_reference, res_deploy_2.module_reference);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    OwnedParameter::new(&input_param),
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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let number_of_upgrades: u32 = 82; // TODO: Stack will overflow if larger than 82.
            let input_param = (number_of_upgrades, res_deploy.module_reference);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    OwnedParameter::new(&input_param),
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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update_upgrade = chain.contract_update(
                ACC_0,
                Address::Account(ACC_0),
                res_init.contract_address,
                EntrypointName::new_unchecked("upgrade"),
                OwnedParameter::new(&res_deploy_1.module_reference),
                Amount::zero(),
                Energy::from(1000000),
            );

            let res_update_new_feature = chain.contract_update(
                ACC_0,
                Address::Account(ACC_0),
                res_init.contract_address,
                EntrypointName::new_unchecked("new_feature"),
                OwnedParameter::empty(),
                Amount::zero(),
                Energy::from(1000000),
            );

            // Check the return value manually returned by the contract.
            match res_update_upgrade {
                Err(ContractUpdateError::ExecutionError { failure_kind, .. }) => match failure_kind
                {
                    InvokeFailure::ContractReject { code, .. } if code == -1 => (),
                    _ => panic!("Expected ContractReject with code == -1"),
                },
                _ => panic!("Expected Err(ContractUpdateError::ExecutionError)"),
            }

            // Assert that the new_feature entrypoint doesn't exist since the upgrade
            // failed.
            assert!(matches!(
                res_update_new_feature,
                Err(ContractUpdateError::ExecutionError {
                    failure_kind:    InvokeFailure::NonExistentEntrypoint,
                    energy_used:     _,
                    transaction_fee: _,
                })
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
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update_old_feature_0 = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("old_feature"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect("Updating old_feature on old module should work.");

            let res_update_new_feature_0 = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("new_feature"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect_err("Updating new_feature on old module should _not_ work");

            let res_update_upgrade = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    OwnedParameter::new(&res_deploy_1.module_reference),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect("Upgrading contract should work.");

            let res_update_old_feature_1 = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("old_feature"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect_err("Updating old_feature on _new_ module should _not_ work.");

            let res_update_new_feature_1 = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("new_feature"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect("Updating new_feature on _new_ module should work");

            assert!(matches!(res_update_old_feature_0.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
            assert!(matches!(
                res_update_new_feature_0,
                ContractUpdateError::ExecutionError {
                    failure_kind:    InvokeFailure::NonExistentEntrypoint,
                    energy_used:     _,
                    transaction_fee: _,
                }
            ));
            assert!(matches!(res_update_upgrade.chain_events[..], [
                ChainEvent::Interrupted { .. },
                ChainEvent::Upgraded { .. },
                ChainEvent::Resumed { .. },
                ChainEvent::Updated { .. },
            ]));
            assert!(matches!(
                res_update_old_feature_1,
                ContractUpdateError::ExecutionError {
                    failure_kind:    InvokeFailure::NonExistentEntrypoint,
                    energy_used:     _,
                    transaction_fee: _,
                }
            ));
            assert!(matches!(res_update_new_feature_1.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }
    }

    /// Tests related to checkpoints and rollbacks of the contract state.
    mod checkpointing {
        use super::*;

        /// This test has the following call pattern:
        /// A
        ///  -->  B
        ///         --> A
        ///         <--
        ///       B(trap)
        /// A <--
        /// The state at A should be left unchanged by the changes of the
        /// 'inner' invocation on contract A. A correctly perceives B's
        /// trapping signal. Only V1 contracts are being used.
        #[test]
        fn test_case_1() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(10000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/checkpointing.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_init_a = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_a"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_init_b = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_b"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let forward_parameter = (
                res_init_a.contract_address,
                0u16, // length of empty parameter
                (EntrypointName::new_unchecked("a_modify"), Amount::zero()),
            );
            let forward_parameter_len = to_bytes(&forward_parameter).len();
            let parameter = (
                (
                    res_init_b.contract_address,
                    forward_parameter_len as u16,
                    forward_parameter,
                ),
                EntrypointName::new_unchecked("b_forward_crash"),
                Amount::zero(),
            );

            chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init_a.contract_address,
                    EntrypointName::new_unchecked("a_modify_proxy"),
                    OwnedParameter::new(&parameter),
                    // We supply one microCCD as we expect a trap
                    // (see contract for details).
                    Amount::from_micro_ccd(1),
                    Energy::from(10000),
                )
                .expect("Updating contract should succeed");
        }

        /// This test has the following call pattern:
        /// A
        ///   -->  B
        ///          --> A (no modification, just lookup entry)
        ///          <--
        ///        B
        /// A <--
        ///
        /// The state at A should be left unchanged.
        /// The iterator initialized at the outer A should point to the same
        /// entry as before the call. That is, the iterator should not
        /// be affected by the inner iterator. Only V1 contracts are
        /// being used.
        #[test]
        fn test_case_2() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(10000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/checkpointing.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_init_a = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_a"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_init_b = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_b"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let forward_parameter = (
                res_init_a.contract_address,
                0u16, // length of empty parameter
                (EntrypointName::new_unchecked("a_no_modify"), Amount::zero()),
            );
            let forward_parameter_len = to_bytes(&forward_parameter).len();
            let parameter = (
                (
                    res_init_b.contract_address,
                    forward_parameter_len as u16,
                    forward_parameter,
                ),
                EntrypointName::new_unchecked("b_forward"),
                Amount::zero(),
            );

            chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init_a.contract_address,
                    EntrypointName::new_unchecked("a_modify_proxy"),
                    OwnedParameter::new(&parameter),
                    // We supply zero microCCD as we're instructing the contract to not expect
                    // state modifications. Also, the contract does not expect
                    // errors, i.e., a trap signal from underlying invocations.
                    // The 'inner' call to contract A does not modify the state.
                    // See the contract for details.
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Updating contract should succeed");
        }

        /// This test has the following call pattern:
        /// A
        ///   -->  Transfer
        /// A <--
        ///
        /// The state at A should be left unchanged.
        /// The iterator initialized at A should after the call point to the
        /// same entry as before the call. Only V1 contracts are being
        /// used.
        #[test]
        fn test_case_3() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(10000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));
            chain.create_account(ACC_1, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/checkpointing.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_init_a = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_a"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_b"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init_a.contract_address,
                    EntrypointName::new_unchecked("a_modify_proxy"),
                    OwnedParameter::new(&ACC_1),
                    // We supply three micro CCDs as we're instructing the contract to carry out a
                    // transfer instead of a call. See the contract for
                    // details.
                    Amount::from_micro_ccd(3),
                    Energy::from(10000),
                )
                .expect("Updating contract should succeed");
        }

        /// This test has the following call pattern:
        /// A
        ///   -->  B
        ///          --> A modify
        ///          <--
        ///        B
        /// A <--
        ///
        /// The state at A should have changed according to the 'inner'
        /// invocation on contract A. Only V1 contracts are being used.
        #[test]
        fn test_case_4() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(10000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/checkpointing.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_init_a = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_a"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_init_b = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_b"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let forward_parameter = (
                res_init_a.contract_address,
                0u16, // length of empty parameter
                (EntrypointName::new_unchecked("a_modify"), Amount::zero()),
            );
            let forward_parameter_len = to_bytes(&forward_parameter).len();
            let parameter = (
                (
                    res_init_b.contract_address,
                    forward_parameter_len as u16,
                    forward_parameter,
                ),
                EntrypointName::new_unchecked("b_forward"),
                Amount::zero(),
            );

            chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init_a.contract_address,
                    EntrypointName::new_unchecked("a_modify_proxy"),
                    OwnedParameter::new(&parameter),
                    // We supply four CCDs as we're instructing the contract to expect state
                    // modifications being made from the 'inner' contract A
                    // call to be in effect when returned to the caller (a.a_modify_proxy).
                    // See the contract for details.
                    Amount::from_micro_ccd(4),
                    Energy::from(10000),
                )
                .expect("Updating contract should succeed");
        }
    }

    mod amount_delta {
        use super::*;

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
