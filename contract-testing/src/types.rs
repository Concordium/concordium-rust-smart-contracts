use concordium_base::{
    base::{AccountAddressEq, Energy},
    contracts_common::{
        AccountAddress, AccountBalance, Address, Amount, ContractAddress, ExchangeRate,
        ModuleReference, OwnedContractName, OwnedEntrypointName, OwnedPolicy, SlotTime, Timestamp,
    },
    hashes::BlockHash,
    smart_contracts::{ContractEvent, ContractTraceElement, InstanceUpdatedEvent, WasmVersion},
};
use concordium_rust_sdk as sdk;
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

/// The chain parameters.
#[derive(Debug)]
pub(crate) struct ChainParameters {
    /// The block time viewable inside the smart contracts.
    /// Defaults to `0`.
    pub(crate) block_time:         SlotTime,
    /// MicroCCD per Euro ratio.
    // This is not public because we ensure a reasonable value during the construction of the
    // [`Chain`].
    pub(crate) micro_ccd_per_euro: ExchangeRate,
    /// Euro per Energy ratio.
    // This is not public because we ensure a reasonable value during the construction of the
    // [`Chain`].
    pub(crate) euro_per_energy: ExchangeRate,
}

/// The connection and runtime needed for communicating with an external node.
#[derive(Debug)]
pub(crate) struct ExternalNodeConnection {
    /// An instantiated v2 Client from the Rust SDK. Used for communicating with
    /// a node.
    pub(crate) client:      concordium_rust_sdk::v2::Client,
    /// A Tokio runtime used to execute the async methods of the `client`.
    pub(crate) runtime:     tokio::runtime::Runtime,
    /// The block used for queries.
    pub(crate) query_block: BlockHash,
}

/// Represents the blockchain and supports a number of operations, including
/// creating accounts, deploying modules, initializing contract, updating
/// contracts and invoking contracts.
#[derive(Debug)]
pub struct Chain {
    pub(crate) parameters:               ChainParameters,
    /// Accounts and info about them.
    /// This uses [`AccountAddressEq`] to ensure that account aliases are seen
    /// as one account.
    pub(crate) accounts:                 BTreeMap<AccountAddressEq, Account>,
    /// Smart contract modules.
    pub(crate) modules:                  BTreeMap<ModuleReference, ContractModule>,
    /// Smart contract instances.
    pub(crate) contracts:                BTreeMap<ContractAddress, Contract>,
    /// Next contract index to use when creating a new instance.
    pub(crate) next_contract_index:      u64,
    /// An optional connection to an external node.
    pub(crate) external_node_connection: Option<ExternalNodeConnection>,
}

/// A builder for the [`Chain`].
#[derive(Debug)]
pub struct ChainBuilder {
    /// The configured endpoint for an external node connection.
    pub(crate) external_node_endpoint: Option<sdk::v2::Endpoint>,
    /// The block hash to be used for external queries. If this is not set, then
    /// the last final block hash is used instead.
    pub(crate) external_query_block: Option<BlockHash>,
    /// The configured exchange rate between microCCD and euro.
    pub(crate) micro_ccd_per_euro: Option<ExchangeRate>,
    /// Whether the microCCD/euro exchange rate should be set via the external
    /// node.
    pub(crate) micro_ccd_per_euro_from_external: bool,
    /// The configured exchange rate between euro and energy.
    pub(crate) euro_per_energy: Option<ExchangeRate>,
    /// Whether the euro/energy exchange rate should be set via the external
    /// node.
    pub(crate) euro_per_energy_from_external: bool,
    /// The configured block time.
    pub(crate) block_time: Option<Timestamp>,
    /// Whether the block time should be set via the external node.
    pub(crate) block_time_from_external: bool,
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

/// An error that occurred while deploying a [`ContractModule`].
#[derive(Debug, Error)]
#[error(
    "Module deployment failed after consuming {energy_used}NRG ({transaction_fee} microCCD) with \
     error {kind}."
)]
pub struct ModuleDeployError {
    /// The energy used for deployment.
    pub energy_used:     Energy,
    /// The transaction fee. This is the amount charged to the `sender`
    /// account.
    pub transaction_fee: Amount,
    /// The specific reason for why the deployment failed.
    pub kind:            ModuleDeployErrorKind,
}

/// The specific kind of error that occurred while deploying a
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

/// An error that occurred in [`Chain::contract_init`].
#[derive(Debug, Error)]
#[error(
    "Contract initialization failed after consuming {energy_used}NRG ({transaction_fee} microCCD) \
     with error {kind}."
)]
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

/// An error that occurred while executing a contract init or receive function.
#[derive(Debug, Error)]
#[error("The contract execution halted due to: {0}")]
pub struct ExecutionError(#[from] pub(crate) anyhow::Error);

/// Represents a successful contract update (or invocation).
#[derive(Debug)]
pub struct ContractInvokeSuccess {
    /// Host events that occurred. This includes interrupts, resumes, and
    /// upgrades.
    pub trace_elements:  Vec<DebugTraceElement>,
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
}

impl ContractInvokeSuccess {
    /// Extract all the events logged by all the contracts in the invocation.
    /// The events are returned in the order that they are emitted, and are
    /// paired with the address of the contract that emitted it.
    ///
    /// Only events from effective trace elements are included. See
    /// [`Self::effective_trace_elements`] for more details.
    pub fn events(&self) -> impl Iterator<Item = (ContractAddress, &[ContractEvent])> {
        self.effective_trace_elements().flat_map(|cte| {
            if let ContractTraceElement::Updated { data } = cte {
                Some((data.address, data.events.as_slice()))
            } else {
                None
            }
        })
    }

    /// Extract the transfers **to accounts** that occurred during
    /// invocation. The return value is an iterator over triples `(from, amount,
    /// to)` where `from` is the sender contract, and `to` is the receiver
    /// account. The transfers are returned in the order that they occurred.
    ///
    /// Only tranfers from effective trace elements are included. See
    /// [`Self::effective_trace_elements`] for more details.
    pub fn account_transfers(
        &self,
    ) -> impl Iterator<Item = (ContractAddress, Amount, AccountAddress)> + '_ {
        self.effective_trace_elements().flat_map(|cte| {
            if let ContractTraceElement::Transferred { from, amount, to } = cte {
                Some((*from, *amount, *to))
            } else {
                None
            }
        })
    }

    /// Get an iterator over references of all the [`ContractTraceElement`]s
    /// that have *not* been rolled back.
    ///
    /// The trace elements returned here corresponds to the ones returned by the
    /// node.
    ///
    /// See also [`Self::effective_trace_elements_cloned`] for a version with
    /// clones.
    pub fn effective_trace_elements(&self) -> impl Iterator<Item = &ContractTraceElement> {
        self.trace_elements.iter().filter_map(|cte| match cte {
            DebugTraceElement::Regular { trace_element, .. } => Some(trace_element),
            DebugTraceElement::WithFailures { .. } => None,
        })
    }

    /// Get an iterator over clones of all the [`ContractTraceElement`]s that
    /// have *not* been rolled back.
    ///
    /// The trace elements returned here corresponds to the ones returned by the
    /// node.
    ///
    /// See also [`Self::effective_trace_elements`] for a version with
    /// references.
    pub fn effective_trace_elements_cloned(&self) -> Vec<ContractTraceElement> {
        self.trace_elements
            .iter()
            .filter_map(|cte| match cte {
                DebugTraceElement::Regular { trace_element, .. } => Some(trace_element.clone()),
                DebugTraceElement::WithFailures { .. } => None,
            })
            .collect()
    }

    /// Get the successful trace elements grouped by which contract they
    /// originated from.
    pub fn trace_elements(&self) -> BTreeMap<ContractAddress, Vec<ContractTraceElement>> {
        let mut map: BTreeMap<ContractAddress, Vec<ContractTraceElement>> = BTreeMap::new();
        for event in self.effective_trace_elements() {
            map.entry(Self::extract_contract_address(event))
                .and_modify(|v| v.push(event.clone()))
                .or_insert_with(|| vec![event.clone()]);
        }
        map
    }

    /// Get the contract address that this event relates to.
    /// This means the `address` field for all variant except `Transferred`,
    /// where it returns the `from`.
    fn extract_contract_address(element: &ContractTraceElement) -> ContractAddress {
        match element {
            ContractTraceElement::Interrupted { address, .. } => *address,
            ContractTraceElement::Resumed { address, .. } => *address,
            ContractTraceElement::Upgraded { address, .. } => *address,
            ContractTraceElement::Updated {
                data: InstanceUpdatedEvent { address, .. },
            } => *address,
            ContractTraceElement::Transferred { from, .. } => *from,
        }
    }

    /// Get the successful contract updates that happened in the transaction.
    /// The order is the order of returns. Concretely, if A calls B (and no
    /// other calls are made) then first there will be "B updated" event,
    /// followed by "A updated", assuming the invocation of both succeeded.
    pub fn updates(&self) -> impl Iterator<Item = &InstanceUpdatedEvent> {
        self.effective_trace_elements().filter_map(|e| {
            if let ContractTraceElement::Updated { data } = e {
                Some(data)
            } else {
                None
            }
        })
    }

    /// Check whether any rollbacks occurred.
    ///
    /// That is, whether any contract calls failed which lead to state and
    /// balances being rolled back.
    ///
    /// If `true` is returned, the relevant traces can be seen in the
    /// `self.trace_elements` vector.
    pub fn rollbacks_occurred(&self) -> bool {
        self.trace_elements
            .iter()
            .any(|element| matches!(element, DebugTraceElement::WithFailures { .. }))
    }
}

/// A wrapper for [`ContractTraceElement`], which provides additional
/// information for testing and debugging. Most notably, it contains trace
/// elements for failures, which are normally discarded by the node.
#[derive(Debug)]
pub enum DebugTraceElement {
    /// A regular trace element with some additional data, e.g., energy usage
    /// and the entrypoint.
    /// This variant may be included included in the `WithFailures` list of
    /// trace elements.
    Regular {
        /// The entrypoint.
        entrypoint:    OwnedEntrypointName,
        /// The trace element.
        trace_element: ContractTraceElement,
        /// The energy used so far.
        energy_used:   Energy,
    },
    /// One or multiple trace elements that fail. Useful for debugging.
    /// This variant also contains additional information, such as the error,
    /// entrypoint, and energy usage.
    WithFailures {
        /// The address of the contract which failed.
        /// This will always match the address in the last element in
        /// `trace_elements` if the vector isn't empty.
        contract_address: ContractAddress,
        /// The entrypoint which failed.
        /// This will always match the address in the last element in
        /// `trace_elements` if the vector isn't empty.
        entrypoint:       OwnedEntrypointName,
        /// The error returned.
        error:            InvokeExecutionError,
        /// Intermediate [`DebugTraceElement`]s which occurred prior to failing.
        /// These are the elements which are normally discared by the node.
        trace_elements:   Vec<DebugTraceElement>,
        /// The energy used so far.
        energy_used:      Energy,
    },
}

/// The reason for why a contract invocation failed during execution.
#[derive(Debug)]
pub enum InvokeExecutionError {
    /// The contract rejected.
    Reject {
        /// The error code for why it rejected.
        reason:       i32,
        /// The return value.
        return_value: ReturnValue,
    },
    /// The contract trapped.
    Trap { error: ExecutionError },
}

/// An error that occurred during a [`Chain::contract_update`] or
/// [`Chain::contract_invoke`].
#[derive(Debug, Error)]
#[error(
    "Contract invocation failed after using {energy_used}NRG ({transaction_fee} microCCD) with \
     error {kind}."
)]
pub struct ContractInvokeError {
    /// The energy used.
    pub energy_used:     Energy,
    /// The transaction fee. For [`Chain::contract_update`], this is the amount
    /// charged to the `invoker` account.
    pub transaction_fee: Amount,
    /// Trace elements that occurred before the contract failed.
    pub trace_elements:  Vec<DebugTraceElement>,
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

/// Errors that occur while setting up the connection to an external node.
#[derive(Debug, thiserror::Error)]
pub enum SetupExternalNodeError {
    /// It was not possible to connect to a node on the provided endpoint.
    #[error("Could not connect to the provided endpoint due to: {error}")]
    CannotConnect {
        /// The inner error.
        #[from]
        error: sdk::endpoints::Error,
    },
    /// Request timed out.
    #[error("The request timed out.")]
    Timeout,
    /// The specified external query block does not exist.
    #[error("The specified external query block {query_block} does not exist.")]
    QueryBlockDoesNotExist { query_block: BlockHash },
    /// Could not check the existence of the specified query block or the last
    /// final block.
    #[error(
        "Could not check the existence of the specified query block or the last final block due \
         to: {error}"
    )]
    CannotCheckQueryBlockExistence {
        /// The inner error.
        error: sdk::v2::RPCError,
    },
}

/// Errors that occur while trying to communicate with an external node.
#[derive(Debug, Error)]
pub enum ExternalNodeError {
    /// An external node has not been configured.
    #[error("An external node has not been configured.")]
    NotConfigured,
    /// The query could not be performed.
    #[error("Could not perform the query: {error}")]
    QueryError {
        #[from]
        error: sdk::endpoints::QueryError,
    },
    /// Request timed out.
    #[error("The request timed out.")]
    Timeout,
}

/// The error returned when an external node has not been configured prior to
/// using it.
#[derive(Debug, Error, PartialEq, Eq)]
#[error("An external node has not been configured.")]
pub struct ExternalNodeNotConfigured;

#[derive(Debug, Error)]
pub enum ChainBuilderError {
    /// The provided exchange rates are not valid.
    /// Meaning that they do not correspond to one energy costing less than
    /// `u64::MAX / `
    /// [`concordium_base::constants::MAX_ALLOWED_INVOKE_ENERGY`]`.
    #[error("An exchange rate was too high.")]
    ExchangeRateError,
    /// An error occurred while setting up the connection to an external node.
    #[error("Error occurred while setting up the connection to an external node: {error}")]
    SetupExternalNodeError {
        #[from]
        error: SetupExternalNodeError,
    },
    /// Error occurred while using the external node for querying chain
    /// parameters such as the block time or exchange rates.
    #[error("Error occurred while using the external node for querying chain parameters: {error}")]
    ExternalNodeError {
        #[from]
        error: ExternalNodeError,
    },
    /// Could not configure the block time because both the
    /// [`ChainBuilder::block_time`] and
    /// [`ChainBuilder::block_time_from_external`] was provided, which is not
    /// allowed.
    #[error(
        "Conflicting block time configuration: `block_time` and `block_time_from_external` cannot \
         both be used."
    )]
    ConflictingBlockTime,
    /// Could not configure the microCCD/euro exchange rate because both the
    /// [`ChainBuilder::micro_ccd_per_euro`] and
    /// [`ChainBuilder::micro_ccd_per_euro_from_external`] was provided, which
    /// is not allowed.
    #[error(
        "Conflicting microCCD per euro configuration: `micro_ccd_per_euro` and \
         `micro_ccd_per_euro_from_external` cannot both be used."
    )]
    ConflictingMicroCCDPerEuro,
    /// Could not configure the euro/energy exchange rate because both the
    /// [`ChainBuilder::euro_per_energy`] and
    /// [`ChainBuilder::euro_per_energy_from_external`] was provided, which is
    /// not allowed.
    #[error(
        "Conflicting euro per energy configuration: `euro_per_energy` and \
         `euro_per_energy_from_external` cannot both be used."
    )]
    ConflictingEuroPerEnergy,
    /// A configuration option that requires an external node connection was
    /// used without [`ChainBuilder::external_node_connection`].
    #[error(
        "A configuration method that requires an external node connection was called without \
         `ChainBuilder::external_node_connection`."
    )]
    MissingExternalConnection,
}

/// The block time overflowed during a call to `Chain::tick_block_time`.
#[derive(Debug, Error, PartialEq, Eq)]
#[error("The block time overflowed during a call to `Chain::tick_block_time`.")]
pub struct BlockTimeOverflow;
