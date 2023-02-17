use std::{collections::BTreeMap, sync::Arc};
use thiserror::Error;

use concordium_base::{
    base::Energy,
    contracts_common::{
        AccountAddress, Address, Amount, ContractAddress, ExchangeRate, ModuleReference,
        OwnedContractName, OwnedEntrypointName, SlotTime,
    },
    smart_contracts::WasmVersion,
};
use wasm_chain_integration::{
    v0,
    v1::{self, trie, ReturnValue},
};
use wasm_transform::artifact;

/// A V1 artifact, with concrete types for the generic parameters.
pub type ContractModule = artifact::Artifact<v1::ProcessedImports, artifact::CompiledFunction>;

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
    pub accounts:            BTreeMap<AccountAddress, Account>,
    /// Smart contract modules.
    pub modules:             BTreeMap<ModuleReference, Arc<ContractModule>>,
    /// Smart contract instances.
    pub contracts:           BTreeMap<ContractAddress, Contract>,
    /// Next contract index to use when creating a new instance.
    pub next_contract_index: u64,
}

/// A smart contract instance.
#[derive(Clone)]
pub struct Contract {
    /// The module which contains this contract.
    pub module_reference: ModuleReference,
    /// The name of the contract.
    pub contract_name:    OwnedContractName,
    /// The contract state.
    pub state:            trie::PersistentState,
    /// The owner of the contract.
    pub owner:            AccountAddress,
    /// The balance of the contract.
    pub self_balance:     Amount,
}

/// Account policies for testing.
pub struct TestPolicies(pub v0::OwnedPolicyBytes);

/// An account.
#[derive(Clone)]
pub struct Account {
    /// The account balance. TODO: Add all three types of balances.
    pub balance:         Amount,
    /// Account policies.
    pub policies:        v0::OwnedPolicyBytes,
    /// The number of signatures. The number of signatures affect the cost of
    /// every transaction for the account.
    pub signature_count: u32,
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
        failure_kind:    v1::InvokeFailure,
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

/// A transfer of [`Amount`]s failed because the sender had insufficient
/// balance.
#[derive(Debug)]
pub(crate) struct InsufficientBalanceError;

/// Errors related to transfers.
#[derive(PartialEq, Eq, Debug, Error)]
pub(crate) enum TransferError {
    /// The receiver does not exist.
    #[error("The receiver does not exist.")]
    ToMissing,
    /// The sender does not have sufficient balance.
    #[error("The sender does not have sufficient balance.")]
    InsufficientBalance,
}

/// The entrypoint does not exist.
#[derive(PartialEq, Eq, Debug, Error)]
#[error("The entrypoint '{0}' does not exist.")]
pub struct EntrypointDoesNotExist(pub OwnedEntrypointName);

/// The contract module does not exist.
#[derive(Debug, Error)]
#[error("Module {:?} does not exist.", 0)]
pub struct ModuleMissing(pub ModuleReference);

/// The contract instance does not exist.
#[derive(Debug, Error)]
#[error("Contract instance {0} does not exist.")]
pub struct ContractInstanceMissing(pub ContractAddress);

/// The account does not exist.
#[derive(Debug, Error)]
#[error("Account {0} does not exist.")]
pub struct AccountMissing(pub AccountAddress);
