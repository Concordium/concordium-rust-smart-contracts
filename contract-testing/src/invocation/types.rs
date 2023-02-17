use crate::types::{Account, ChainEvent, Contract, ContractModule};
use concordium_base::contracts_common::{
    AccountAddress, Amount, ContractAddress, ExchangeRate, ModuleReference, OwnedContractName,
    OwnedEntrypointName, SlotTime,
};
use std::{collections::BTreeMap, sync::Arc};
use wasm_chain_integration::{
    v0,
    v1::{self, trie::MutableState, InvokeResponse},
    InterpreterEnergy,
};

/// The result of invoking an entrypoint.
pub(crate) struct InvokeEntrypointResult {
    /// The result from the invoke.
    pub(crate) invoke_response:  InvokeResponse,
    /// Will be `Some` if and only if `invoke_response` is `Success`.
    pub(crate) logs:             Option<v0::Logs>,
    /// The remaining energy after the invocation.
    pub(crate) remaining_energy: InterpreterEnergy,
}

/// A type that supports invoking a contract entrypoint.
pub(crate) struct EntrypointInvocationHandler {
    pub(super) changeset:          ChangeSet,
    pub(super) accounts:           BTreeMap<AccountAddress, Account>,
    pub(super) modules:            BTreeMap<ModuleReference, Arc<ContractModule>>,
    pub(super) contracts:          BTreeMap<ContractAddress, Contract>,
    pub(super) slot_time:          SlotTime,
    pub(super) euro_per_energy:    ExchangeRate,
    pub(super) micro_ccd_per_euro: ExchangeRate,
}

/// The set of [`Changes`] represented as a stack.
#[derive(Debug, Clone)]
pub(crate) struct ChangeSet {
    /// The stack of changes.
    pub(super) stack: Vec<Changes>,
}

/// Data held for accounts and contracts during the execution of a contract
/// entrypoint.
#[derive(Clone, Debug)]
pub(super) struct Changes {
    /// The contracts which have changes.
    pub(super) contracts: BTreeMap<ContractAddress, ContractChanges>,
    /// The accounts which have changes.
    pub(super) accounts:  BTreeMap<AccountAddress, AccountChanges>,
}

/// Data held for an account during the execution of a contract entrypoint.
#[derive(Clone, Debug)]
pub(super) struct AccountChanges {
    /// Should never be modified.
    pub(super) original_balance: Amount,
    pub(super) balance_delta:    AmountDelta,
}

/// Data held for a contract during the execution of a contract entrypoint.
#[derive(Clone, Debug)]
pub(super) struct ContractChanges {
    /// An index that is used to check whether a caller contract has been
    /// modified after invoking another contract (due to reentrancy).
    pub(super) modification_index:    u32,
    /// Represents how much the contract's self balance has changed.
    pub(super) self_balance_delta:    AmountDelta,
    /// The original contract balance, i.e. the one that is persisted. Should
    /// never be modified.
    pub(super) self_balance_original: Amount,
    /// The potentially modified contract state.
    pub(super) state:                 Option<MutableState>,
    /// The potentially changed module.
    pub(super) module:                Option<ModuleReference>,
}

/// Data needed to recursively process a contract entrypoint to completion.
///
/// In particular, this keeps the data necessary for resuming a contract
/// entrypoint after an interrupt.
///
/// One `InvocationData` is created for each time
/// [`EntrypointInvocationHandler::invoke_entrypoint`] is called.
pub(super) struct InvocationData<'a, 'b> {
    /// The invoker.
    pub(super) invoker: AccountAddress,
    /// The contract being called.
    pub(super) address: ContractAddress,
    /// The name of the contract.
    pub(super) contract_name: OwnedContractName,
    /// The amount sent from the sender to the contract.
    pub(super) amount: Amount,
    /// The CCD amount reserved from the invoker account for the energy. While
    /// the amount is reserved, it is not subtracted in the chain.accounts
    /// map. Used to handle account balance queries for the invoker account.
    /// TODO: We could use a changeset for accounts -> balance, and then look up
    /// the "chain.accounts" values for chain queries.
    pub(super) invoker_amount_reserved_for_nrg: Amount,
    /// The entrypoint to execute.
    pub(super) entrypoint: OwnedEntrypointName,
    /// A reference to the chain.
    pub(super) chain: &'a mut EntrypointInvocationHandler,
    /// The current state.
    pub(super) state: MutableState,
    /// Chain events that have occurred during the execution.
    pub(super) chain_events: Vec<ChainEvent>,
    ///
    pub(super) loader: v1::trie::Loader<&'b [u8]>,
}

/// A positive or negative delta in for an [`Amount`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum AmountDelta {
    /// A posittive delta.
    Positive(Amount),
    /// A negative delta.
    Negative(Amount),
}

/// An underflow occurred.
#[derive(Debug)]
pub(super) struct UnderflowError;

/// The contract ran out of energy during execution of a contract entrypoint.
#[derive(PartialEq, Eq, Debug)]
pub(crate) struct OutOfEnergy;
