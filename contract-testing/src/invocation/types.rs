use crate::types::{Account, ChainEvent, Contract, ContractModule};
use concordium_base::{
    base::Energy,
    contracts_common::{
        AccountAddress, Amount, ContractAddress, ExchangeRate, ModuleReference, OwnedContractName,
        OwnedEntrypointName, SlotTime,
    },
};
use concordium_smart_contract_engine::{
    v0,
    v1::{trie::MutableState, InvokeResponse},
};
use std::collections::BTreeMap;

/// The response from invoking an entrypoint.
pub(crate) struct InvokeEntrypointResponse {
    /// The result from the invoke.
    pub(crate) invoke_response: InvokeResponse,
    /// Logs created during the invocation.
    /// Has entries if and only if `invoke_response` is `Success`.
    pub(crate) logs:            v0::Logs,
}

/// A type that supports invoking a contract entrypoint.
pub(crate) struct EntrypointInvocationHandler<'a> {
    /// The changeset which keeps track of changes to accounts, modules, and
    /// contracts that occur during an invocation.
    pub(super) changeset:          ChangeSet,
    /// The energy remaining for execution.
    pub(super) remaining_energy:   &'a mut Energy,
    /// The accounts of the chain. These are currently clones and only used as a
    /// reference. Any changes are saved to the changeset.
    pub(super) accounts:           BTreeMap<AccountAddress, Account>,
    /// The modules of the chain. These are currently clones and only used as a
    /// reference. Any changes are saved to the changeset.
    pub(super) modules:            BTreeMap<ModuleReference, ContractModule>,
    /// The contracts of the chain. These are currently clones and only used as
    /// a reference. Any changes are saved to the changeset.
    pub(super) contracts:          BTreeMap<ContractAddress, Contract>,
    /// The current block time.
    pub(super) block_time:         SlotTime,
    /// The euro per energy exchange rate.
    pub(super) euro_per_energy:    ExchangeRate,
    /// The mCCD per euro exchange rate.
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
    pub(super) invoker:            AccountAddress,
    /// The contract being called.
    pub(super) address:            ContractAddress,
    /// The name of the contract.
    pub(super) contract_name:      OwnedContractName,
    /// The amount sent from the sender to the contract.
    pub(super) amount:             Amount,
    /// The entrypoint to execute.
    pub(super) entrypoint:         OwnedEntrypointName,
    /// A reference to the [`EntrypointInvocationHandler`], which is used to for
    /// handling interrupts and for querying chain data.
    pub(super) invocation_handler: &'a mut EntrypointInvocationHandler<'b>,
    /// The current state.
    pub(super) state:              MutableState,
    /// Chain events that have occurred during the execution.
    pub(super) chain_events:       Vec<ChainEvent>,
}

/// A positive or negative delta in for an [`Amount`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum AmountDelta {
    /// A positive delta.
    Positive(Amount),
    /// A negative delta.
    Negative(Amount),
}

/// Errors that occur due to the configuration of the test.
#[derive(Debug)]
pub(crate) enum TestConfigurationError {
    /// The method ran out of energy.
    OutOfEnergy,
    /// The balance of an account or contract oveflowed while adding a new
    /// [`Amount`]. On the chain there is roughly 10 billion CCD, which
    /// means that overflows of amounts cannot occur.
    BalanceOverflow,
}
