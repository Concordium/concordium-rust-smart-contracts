use crate::Chain;
use concordium_base::{
    base::{AccountAddressEq, Energy},
    contracts_common::{
        AccountAddress, Address, Amount, ContractAddress, ModuleReference, OwnedContractName,
        OwnedEntrypointName,
    },
    smart_contracts::OwnedParameter,
    transactions::UpdateContractPayload,
};
use concordium_smart_contract_engine::v1::{
    trie::MutableState, InvokeResponse, ReceiveContext, ReceiveInterruptedState,
};
use concordium_wasm::artifact::CompiledFunction;
use std::collections::BTreeMap;

/// A type that supports invoking a contract entrypoint.
pub(crate) struct EntrypointInvocationHandler<'a, 'b> {
    /// Amount reserved for execution. This is used to return the correct
    /// balance of the invoker account.
    pub(crate) reserved_amount: Amount,
    /// Address of the invoker of the transaction. This is used to return the
    /// correct balance of the invoker account.
    pub(crate) invoker: AccountAddress,
    /// The changeset which keeps track of
    /// changes to accounts, modules, and contracts that occur during an
    /// invocation.
    pub(crate) changeset: ChangeSet,
    /// The energy remaining for execution.
    pub(crate) remaining_energy: &'a mut Energy,
    /// The energy reserved for the execution. Used for calculating intermediate
    /// energy usages in contract trace elements.
    pub(crate) energy_reserved: Energy,
    /// An immutable reference to the chain, used for looking up information,
    /// including contracts, modules, and accounts.
    pub(crate) chain: &'b Chain,
    /// The next contract modification index to be given out.
    /// The index is global per transaction, which is why this field is
    /// needed.
    pub(crate) next_contract_modification_index: u32,
}

/// This auxiliary type is used in `invoke_entrypoint` from impls.rs to keep
/// track of the "to do list" in the form of a stack. It stores the necessary
/// information to continue execution until all actions have been processed.
pub(super) enum Next {
    /// The next action is to resume execution after handling the interrupt.
    Resume {
        data:     InvocationData,
        config:   Box<ReceiveInterruptedState<CompiledFunction, ReceiveContext<Vec<u8>>>>,
        /// This is [`None`] if we are going to resume after a call to a
        /// contract. And [`Some`] if we have an immediate handler that
        /// immediately produces a response.
        response: Option<InvokeResponse>,
    },
    /// The next action is to start executing an entrypoint.
    Initial {
        sender:                    Address,
        payload:                   UpdateContractPayload,
        /// If execution of the entrypoint fails then it does not produce any
        /// trace. We store the trace in one "global" (per transaction)
        /// vector. This field is used to determine how far back we need
        /// to roll back (i.e., clean up) the elements in that trace in
        /// case of contract invocation failure.
        trace_elements_checkpoint: usize,
    },
}

/// The set of [`Changes`] represented as a stack.
// For maintainers. It would be better if `Changes` had a form of copy-on-write.
// At the moment we make a full clone of the changes when we need to checkpoint.
// This is OKish, since people generally don't have that complex protocols, but can be made more
// robust, resistant to malicious input.
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
    /// The accounts which have changes. These are indexed by account address
    /// equivalence classes so that account aliases are resolved to the same
    /// account.
    pub(super) accounts:  BTreeMap<AccountAddressEq, AccountChanges>,
}

/// Data held for an account during the execution of a contract entrypoint.
#[derive(Clone, Debug)]
pub(super) struct AccountChanges {
    /// The original balance.
    ///
    /// For the `invoker`, this will be the `original_balance - reserved_amount`
    /// (from [`EntrypointInvocationHandler`]).
    ///
    /// Should never be modified.
    pub(super) original_balance: Amount,
    /// The change in the account balance.
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
#[derive(Debug)]
pub(super) struct InvocationData {
    /// The sender.
    pub(super) sender:                    Address,
    /// The contract being called.
    pub(super) address:                   ContractAddress,
    /// The name of the contract.
    pub(super) contract_name:             OwnedContractName,
    /// The entrypoint to execute.
    pub(super) entrypoint:                OwnedEntrypointName,
    /// The amount sent from the sender to the contract.
    pub(super) amount:                    Amount,
    /// The parameter given to the entrypoint.
    pub(super) parameter:                 OwnedParameter,
    /// The current state.
    pub(super) state:                     MutableState,
    /// A checkpoint in the list of trace elements.
    /// We reset to this size in case of failure of execution.
    pub(super) trace_elements_checkpoint: usize,
    /// A checkpoint on the next modification index.
    /// We reset `next_modification_index` to this value in case of failure of
    /// execution.
    pub(super) next_mod_idx_checkpoint:   u32,
    /// The modification index before making an invocation.
    /// Differs from the `next_mod_idx_checkpoint` in that this value can be
    /// altered during the execution of a single entrypoint.
    pub(super) mod_idx_before_invoke:     u32,
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
