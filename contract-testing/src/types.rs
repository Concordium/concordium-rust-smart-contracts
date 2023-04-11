use concordium_base::{
    base::{AccountAddressEq, Energy},
    contracts_common::{
        AccountAddress, AccountBalance, Address, Amount, ContractAddress, ExchangeRate,
        ModuleReference, OwnedContractName, OwnedEntrypointName, OwnedPolicy, SlotTime,
    },
    smart_contracts::{ContractEvent, ContractTraceElement, WasmVersion},
};
use concordium_smart_contract_engine::v1::{self, trie, ReturnValue};
use concordium_wasm::artifact;
use std::{collections::BTreeMap, path::PathBuf, sync::Arc};
use thiserror::Error;

/// A smart contract module.
#[derive(Debug, Clone)]
pub struct ContractModule {
    /// Size of the module in bytes. Used for cost accounting.
    pub(crate) size:     u64,
    /// The runnable module.
    pub(crate) artifact: Arc<artifact::Artifact<v1::ProcessedImports, artifact::CompiledFunction>>,
}

#[derive(Debug)]
pub(crate) struct ChainParameters {
    /// The block time viewable inside the smart contracts.
    /// Defaults to `0`.
    pub block_time:                SlotTime,
    /// MicroCCD per Euro ratio.
    // This is not public because we ensure a reasonable value during the construction of the
    // [`Chain`].
    pub(crate) micro_ccd_per_euro: ExchangeRate,
    /// Euro per Energy ratio.
    // This is not public because we ensure a reasonable value during the construction of the
    // [`Chain`].
    pub(crate) euro_per_energy:    ExchangeRate,
}

/// Represents the blockchain and supports a number of operations, including
/// creating accounts, deploying modules, initializing contract, updating
/// contracts and invoking contracts.
#[derive(Debug)]
pub struct Chain {
    pub(crate) parameters:          ChainParameters,
    /// Accounts and info about them.
    /// This uses [`AccountAddressEq`] to ensure that account aliases are seen
    /// as one account.
    pub(crate) accounts:            BTreeMap<AccountAddressEq, Account>,
    /// Smart contract modules.
    pub(crate) modules:             BTreeMap<ModuleReference, ContractModule>,
    /// Smart contract instances.
    pub(crate) contracts:           BTreeMap<ContractAddress, Contract>,
    /// Next contract index to use when creating a new instance.
    pub(crate) next_contract_index: u64,
}

/// A smart contract instance.
#[derive(Clone, Debug)]
pub struct Contract {
    /// The address of this contract.
    pub address:          ContractAddress,
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

/// An account.
#[derive(Clone, Debug)]
pub struct Account {
    pub address: AccountAddress,
    /// The account balance.
    pub balance: AccountBalance,
    /// Account policy.
    pub policy:  OwnedPolicy,
}

/// A signer with a number of keys, the amount of which affects the cost of
/// transactions.
#[derive(Copy, Clone, Debug)]
pub struct Signer {
    /// The number of keys used for signing.
    pub(crate) num_keys: u32,
}

/// A transfer from a contract to an account.
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
pub struct ModuleDeploySuccess {
    /// The reference of the module deployed.
    pub module_reference: ModuleReference,
    /// The energy used for deployment.
    pub energy_used:      Energy,
    /// Cost of transaction.
    pub transaction_fee:  Amount,
}

/// An error that occured while deploying a [`ContractModule`].
#[derive(Debug)]
pub struct ModuleDeployError {
    /// The energy used for deployment.
    pub energy_used:     Energy,
    /// The transaction fee. This is the amount charged to the `sender`
    /// account.
    pub transaction_fee: Amount,
    /// The specific reason for why the deployment failed.
    pub kind:            ModuleDeployErrorKind,
}

/// The specific kind of error that occured while deploying a
/// [`ContractModule`].
#[derive(Debug, Error)]
pub enum ModuleDeployErrorKind {
    /// The module provided is not valid.
    #[error("Module is invalid due to: {0}")]
    InvalidModule(#[from] ModuleInvalidError),
    /// The sender account does not have sufficient funds to pay for the
    /// deployment.
    #[error("Sender does not have sufficient funds to pay for the energy")]
    InsufficientFunds,
    /// The sender account deploying the module does not exist.
    #[error("Sender account {} does not exist", 0.0)]
    SenderDoesNotExist(#[from] AccountDoesNotExist),
    /// The module has already been deployed.
    #[error("Module with reference {0} already exists")]
    DuplicateModule(ModuleReference),
    /// The module version is not supported.
    #[error("Wasm version {0} is not supported")]
    UnsupportedModuleVersion(WasmVersion),
}

/// An error that can occur while loading a smart contract module.
#[derive(Debug, Error)]
#[error("Could not load the module file '{path}' due to: {kind}")]
pub struct ModuleLoadError {
    /// The module file.
    pub path: PathBuf,
    /// The reason why loading the module failed.
    pub kind: ModuleLoadErrorKind,
}

/// The specific reason why loading a module failed.
#[derive(Debug, Error)]
pub enum ModuleLoadErrorKind {
    /// Failed to open the module file for reading.
    #[error("Could not open the file for reading to: {0}")]
    OpenFile(#[from] std::io::Error),
    /// Failed to read the module from the file.
    #[error("Could not read the module due to: {0}")]
    ReadModule(#[from] ModuleReadError),
    /// The module version is not supported.
    #[error("The module has wasm version {0}, which is not supported")]
    UnsupportedModuleVersion(WasmVersion),
}

/// The error produced when trying to read a smart contract
/// module from a file.
#[derive(Debug, Error)]
#[error("The module could not be read due to: {0}")]
pub struct ModuleReadError(#[from] pub(crate) anyhow::Error);

/// The error produced when trying to parse a smart contract module.
#[derive(Debug, Error)]
#[error("The module is invalid to: {0}")]
pub struct ModuleInvalidError(#[from] pub(crate) anyhow::Error);

/// Represents a successful initialization of a contract.
#[derive(Debug)]
pub struct ContractInitSuccess {
    /// The address of the new instance.
    pub contract_address: ContractAddress,
    /// Contract events (logs) produced during initialization.
    pub events:           Vec<ContractEvent>,
    /// Energy used.
    pub energy_used:      Energy,
    /// Cost of transaction.
    pub transaction_fee:  Amount,
}

/// An error that occured in [`Chain::contract_init`].
#[derive(Debug)]
pub struct ContractInitError {
    /// Energy used.
    pub energy_used:     Energy,
    /// The transaction fee. This is the amount charged to the `sender`
    /// account.
    pub transaction_fee: Amount,
    /// The specific reason for why the initialization failed.
    pub kind:            ContractInitErrorKind,
}

/// Types of errors that can occur in [`Chain::contract_init`].
#[derive(Debug, Error)]
pub enum ContractInitErrorKind {
    /// Initialization during execution.
    #[error("Failed with an execution error: {error:?}")]
    ExecutionError {
        /// The reason for why the contract initialization failed.
        error: InitExecutionError,
    },
    /// Ran out of energy.
    #[error("Ran out of energy")]
    OutOfEnergy,
    /// Module has not been deployed in the test environment.
    #[error("{0}")]
    ModuleDoesNotExist(#[from] ModuleDoesNotExist),
    /// The specified contract does not exist in the module.
    #[error("The contract (init name) '{name}' does not exist in the module")]
    ContractNotPresentInModule {
        /// The name of the contract (init method) which is not present.
        name: OwnedContractName,
    },
    /// The sender account has not been created in test environment.
    #[error("Sender missing: {0}")]
    SenderDoesNotExist(#[from] AccountDoesNotExist),
    /// The invoker account does not have enough funds to pay for the energy
    /// reserved.
    #[error("Invoker does not have enough funds to pay for the energy")]
    InsufficientFunds,
    /// The invoker account does not have enough funds to pay for the amount.
    /// However it does it have enough funds for the energy reserved.
    #[error("Invoker does not have enough funds to pay for the amount")]
    AmountTooLarge,
    /// The parameter is too large.
    #[error("The provided parameter exceeds the maximum size allowed")]
    ParameterTooLarge,
}

/// The reason for why a contract initialization failed during execution.
#[derive(Debug)]
pub enum InitExecutionError {
    /// The contract rejected.
    Reject {
        /// The error code for why it rejected.
        reason:       i32,
        /// The return value.
        return_value: ReturnValue,
    },
    /// The contract trapped.
    Trap { error: ExecutionError },
    /// The contract ran out of energy.
    OutOfEnergy,
}

/// An error that occured while executing a contract init or receive function.
#[derive(Debug, Error)]
#[error("The contract execution halted due to: {0}")]
pub struct ExecutionError(#[from] pub(crate) anyhow::Error);

/// Represents a successful contract update (or invocation).
#[derive(Debug)]
pub struct ContractInvokeSuccess {
    /// Host events that occured. This includes interrupts, resumes, and
    /// upgrades.
    pub trace_elements:  Vec<ContractTraceElement>,
    /// Energy used.
    pub energy_used:     Energy,
    /// Cost of transaction.
    pub transaction_fee: Amount,
    /// The returned value.
    pub return_value:    ReturnValue,
    /// Whether the state of the invoked contract was changed.
    pub state_changed:   bool,
    /// The new balance of the smart contract.
    pub new_balance:     Amount,
    /// The contract events (logs) produced since the last interrupt.
    pub events:          Vec<ContractEvent>,
}

/// An error that occured during a [`Chain::contract_update`] or
/// [`Chain::contract_invoke`].
#[derive(Debug)]
pub struct ContractInvokeError {
    /// The energy used.
    pub energy_used:     Energy,
    /// The transaction fee. For [`Chain::contract_update`], this is the amount
    /// charged to the `invoker` account.
    pub transaction_fee: Amount,
    /// The specific reason for why the invocation failed.
    pub kind:            ContractInvokeErrorKind,
}

/// The error kinds that can occur during [`Chain::contract_update`] or
/// [`Chain::contract_invoke`].
#[derive(Debug, Error)]
pub enum ContractInvokeErrorKind {
    /// Invocation failed during execution.
    #[error("Failed during execution: {failure_kind:?}")]
    ExecutionError { failure_kind: v1::InvokeFailure },
    /// Ran out of energy.
    #[error("Ran out of energy")]
    OutOfEnergy,
    /// The balance of an account or contract overflowed.
    /// If you are seeing this error, lower the [`Amount`]s used in your tests.
    #[error("The balance of an account or contract overflowed")]
    BalanceOverflow,
    /// Module has not been deployed in test environment.
    #[error("{0}")]
    ModuleDoesNotExist(#[from] ModuleDoesNotExist),
    /// Contract instance has not been initialized in the test environment.
    #[error("{0}")]
    ContractDoesNotExist(#[from] ContractDoesNotExist),
    /// Entrypoint does not exist and neither does the fallback entrypoint.
    #[error("{0}")]
    EntrypointDoesNotExist(#[from] EntrypointDoesNotExist),
    /// The invoker account has not been created in the test environment.
    #[error("Invoker missing: {0}")]
    InvokerDoesNotExist(#[from] AccountDoesNotExist),
    /// The sender does not exist in the test environment.
    #[error("Sender missing: the object with address '{0}' does not exist")]
    SenderDoesNotExist(Address),
    /// The invoker account does not have enough funds to pay for the energy
    /// reserved.
    #[error("Invoker does not have enough funds to pay for the energy")]
    InsufficientFunds,
    /// The invoker account does not have enough funds to pay for the amount.
    /// However it does it have enough funds for the energy reserved.
    #[error("Invoker does not have enough funds to pay for the amount")]
    AmountTooLarge,
    /// The parameter is too large.
    #[error("The provided parameter exceeds the maximum size allowed")]
    ParameterTooLarge,
}

/// A balance error which can occur when transferring [`Amount`]s.
#[derive(Debug, PartialEq, Eq, Error)]
pub(crate) enum BalanceError {
    /// The sender had insufficient balance.
    #[error("The sender had insufficient balance.")]
    Insufficient,
    /// The balance change resulted in an overflow.
    ///
    /// This is a configuration error in the tests, where unrealistic balances
    /// have been set, and should thus be *unrecoverable*.
    ///
    /// On the chain there is roughly 10 billion CCD, so an overflow wil never
    /// occur when adding CCDs.
    #[error("An overflow on CCD amounts occurred.")]
    Overflow,
}

/// Errors related to transfers.
#[derive(Debug, PartialEq, Eq, Error)]
pub(crate) enum TransferError {
    /// The receiver does not exist.
    #[error("The receiver does not exist.")]
    ToMissing,
    /// A balance error occurred.
    #[error("A balance error occurred: {error:?}")]
    BalanceError {
        #[from]
        error: BalanceError,
    },
}

/// The entrypoint does not exist.
#[derive(PartialEq, Eq, Debug, Error)]
#[error("Entrypoint '{entrypoint}' does not exist.")]
pub struct EntrypointDoesNotExist {
    /// The missing entrypoint.
    pub entrypoint: OwnedEntrypointName,
}

/// The contract module does not exist.
#[derive(Debug, Error)]
#[error("Module '{module_reference}' does not exist.")]
pub struct ModuleDoesNotExist {
    /// The reference of the missing module.
    pub module_reference: ModuleReference,
}

/// The contract instance does not exist.
#[derive(Debug, Error)]
#[error("Contract instance '{address}' does not exist.")]
pub struct ContractDoesNotExist {
    /// The address of the missing contract.
    pub address: ContractAddress,
}

/// The account does not exist.
#[derive(Debug, Error)]
#[error("Account '{address}' does not exist.")]
pub struct AccountDoesNotExist {
    /// The address of the missing account.
    pub address: AccountAddress,
}

/// The provided exchange rates are not valid.
/// Meaning that they do not correspond to one energy costing less than
/// `u64::MAX / ` [`concordium_base::constants::MAX_ALLOWED_INVOKE_ENERGY`]`.
#[derive(Debug, Error)]
#[error("An exchange rate was too high.")]
pub struct ExchangeRateError;

/// A [`Signer`] cannot be created with `0` keys.
#[derive(Debug, Error)]
#[error("Any signer must have at least one key.")]
pub struct ZeroKeysError;
