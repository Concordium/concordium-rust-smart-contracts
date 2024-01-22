use concordium_rust_sdk as sdk;
use concordium_rust_sdk::{
    base::{
        base::{AccountAddressEq, Energy},
        common::types::{CredentialIndex, KeyIndex, Signature},
        constants::ED25519_SIGNATURE_LENGTH,
        contracts_common::{
            self, AccountAddress, AccountBalance, Address, Amount, ContractAddress, Deserial,
            EntrypointName, ExchangeRate, ModuleReference, OwnedContractName, OwnedEntrypointName,
            OwnedPolicy, ParseResult, SlotTime, Timestamp,
        },
        hashes::BlockHash,
        id::types::SchemeId,
        smart_contracts::{
            ContractEvent, ContractTraceElement, InstanceUpdatedEvent, OwnedParameter,
            OwnedReceiveName, WasmVersion,
        },
        transactions::AccountAccessStructure,
    },
    smart_contracts::engine::{
        v1::{
            self, trie, DebugTracker, EmittedDebugStatement, HostCall, HostFunctionV1, ReturnValue,
        },
        wasm::artifact,
        InterpreterEnergy,
    },
};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
    sync::Arc,
};
use thiserror::Error;

/// A smart contract module.
#[derive(Debug, Clone)]
pub struct ContractModule {
    /// Size of the module in bytes. Used for cost accounting.
    pub size:     u64,
    /// The runnable module.
    pub artifact: Arc<artifact::Artifact<v1::ProcessedImports, artifact::CompiledFunction>>,
}

/// The chain parameters.
#[derive(Debug)]
pub(crate) struct ChainParameters {
    /// The block time viewable inside the smart contracts.
    /// Defaults to `0`.
    pub(crate) block_time:         SlotTime,
    /// MicroCCD per Euro ratio.
    pub(crate) micro_ccd_per_euro: ExchangeRate,
    /// Euro per Energy ratio.
    pub(crate) euro_per_energy:    ExchangeRate,
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
    /// External accounts that are verified to exist in the `query_block`.
    pub(crate) accounts:    BTreeSet<ExternalAccountAddress>,
    /// External contracts that are verified to exist in the `query_block`.
    pub(crate) contracts:   BTreeSet<ExternalContractAddress>,
}

/// Represents the blockchain and supports a number of operations, including
/// creating accounts, deploying modules, initializing contract, updating
/// contracts and invoking contracts.
#[derive(Debug)]
pub struct Chain {
    pub(crate) parameters: ChainParameters,
    /// Accounts and info about them.
    /// This uses [`AccountAddressEq`] to ensure that account aliases are seen
    /// as one account.
    pub accounts: BTreeMap<AccountAddressEq, Account>,
    /// Smart contract modules.
    pub modules: BTreeMap<ModuleReference, ContractModule>,
    /// Smart contract instances.
    pub contracts: BTreeMap<ContractAddress, Contract>,
    /// Next contract index to use when creating a new instance.
    pub(crate) next_contract_index: u64,
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
    /// Account's public keys.
    pub keys:    AccountAccessStructure,
}

/// A signature with account's keys.
#[derive(Debug, Clone)]
pub struct AccountSignatures {
    /// It is assumed that the inner `Signature` will always be for ed25519
    /// scheme, so will have length 64 bytes.
    pub(crate) sigs: BTreeMap<CredentialIndex, BTreeMap<KeyIndex, Signature>>,
}

impl From<AccountSignatures> for BTreeMap<CredentialIndex, BTreeMap<KeyIndex, Signature>> {
    fn from(value: AccountSignatures) -> Self { value.sigs }
}

impl From<BTreeMap<CredentialIndex, BTreeMap<KeyIndex, Signature>>> for AccountSignatures {
    fn from(sigs: BTreeMap<CredentialIndex, BTreeMap<KeyIndex, Signature>>) -> Self {
        Self {
            sigs,
        }
    }
}

impl AccountSignatures {
    /// Return the number of signatures contained in the structure.
    pub fn num_signatures(&self) -> u32 { self.sigs.values().map(|v| v.len() as u32).sum() }
}

impl contracts_common::Serial for AccountSignatures {
    fn serial<W: contracts_common::Write>(&self, out: &mut W) -> Result<(), W::Err> {
        (self.sigs.len() as u8).serial(out)?;
        for (k, v) in self.sigs.iter() {
            k.serial(out)?;
            (v.len() as u8).serial(out)?;
            for (ki, sig) in v.iter() {
                ki.serial(out)?;
                // ed25519 scheme tag.
                0u8.serial(out)?;
                out.write_all(&sig.sig)?;
            }
        }
        Ok(())
    }
}

impl contracts_common::Deserial for AccountSignatures {
    fn deserial<R: contracts_common::Read>(source: &mut R) -> contracts_common::ParseResult<Self> {
        // We essentially unroll the definitions of `deserial_map_no_length` here since
        // the inner type, the Signature, does not have exactly the right
        // serialization instance that we need.
        use contracts_common::Get;
        let outer_len = u8::deserial(source)?;
        let mut last = None;
        let mut sigs = BTreeMap::new();
        for _ in 0..outer_len {
            let idx = source.get()?;
            if last >= Some(idx) {
                return Err(contracts_common::ParseError {});
            }
            last = Some(idx);
            let inner_len: u8 = source.get()?;
            let mut inner_map = BTreeMap::new();
            let mut last_inner = None;
            for _ in 0..inner_len {
                let k = source.get()?;
                let sig = match source.get()? {
                    SchemeId::Ed25519 => {
                        let mut sig = vec![0u8; ED25519_SIGNATURE_LENGTH];
                        source.read_exact(&mut sig)?;
                        Signature {
                            sig,
                        }
                    }
                };

                if let Some((old_k, old_v)) = last_inner.take() {
                    if k <= old_k {
                        return Err(contracts_common::ParseError {});
                    }
                    inner_map.insert(old_k, old_v);
                }
                last_inner = Some((k, sig));
            }
            if let Some((k, v)) = last_inner {
                inner_map.insert(k, v);
            }
            sigs.insert(idx, inner_map);
        }
        Ok(Self {
            sigs,
        })
    }
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
    /// Debug information emitted by the initialization method.
    pub debug_trace:      DebugTracker,
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
        error:       InitExecutionError,
        /// Trace of the execution until the error.
        debug_trace: DebugTracker,
    },
    /// Ran out of energy.
    #[error("Ran out of energy: {debug_trace:?}")]
    OutOfEnergy {
        debug_trace: DebugTracker,
    },
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
    Trap {
        error: ExecutionError,
    },
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

/// Represents a successful external contract invocation.
#[derive(Debug)]
pub struct ContractInvokeExternalSuccess {
    /// Host events that occurred. This includes interrupts, resumes, and
    /// upgrades.
    pub trace_elements: Vec<ContractTraceElement>,
    /// The energy used.
    pub energy_used:    Energy,
    /// The returned value.
    pub return_value:   ReturnValue,
}

/// Information about the collected debug output. This is the item returned
/// by the `debug_events` iterator. It corresponds to a section of execution
/// between interrupts.
pub struct DebugItem<'a> {
    /// The address of the instance that generated the event.
    pub address:     ContractAddress,
    /// The name of the entrypoint that generated the event.
    pub entrypoint:  EntrypointName<'a>,
    /// The debug trace generated since the previous debug item.
    pub debug_trace: &'a DebugTracker,
    /// `true` if this output is in the part of execution that has been rolled
    /// back.
    pub rolled_back: bool,
}

/// Information about an emitted host function call. This is the item returned
/// by the `host_calls` iterator.
pub struct HostCallInfo<'a> {
    /// The address of the instance that generated the event.
    pub address:       ContractAddress,
    /// The name of the entrypoint that generated the event.
    pub entrypoint:    contracts_common::EntrypointName<'a>,
    /// The host function that was called.
    pub host_function: HostFunctionV1,
    /// Energy used by the call.
    pub energy_used:   InterpreterEnergy,
    /// `true` if this host call occurred in the part of execution that is
    /// rolled back.
    pub rolled_back:   bool,
}

impl ContractInvokeSuccess {
    /// Extract all the events logged by all the contracts in the invocation.
    /// The events are returned in the order that they are emitted, and are
    /// paired with the address of the contract that emitted it.
    ///
    /// Only events from effective trace elements are included. See
    /// [`Self::effective_trace_elements`] for more details.
    pub fn events(&self) -> impl Iterator<Item = (ContractAddress, &[ContractEvent])> {
        self.effective_trace_elements().flat_map(|cte| match cte {
            ContractTraceElement::Updated {
                data,
            } => Some((data.address, data.events.as_slice())),
            ContractTraceElement::Interrupted {
                address,
                events,
            } => Some((*address, events.as_slice())),
            _ => None,
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
            if let ContractTraceElement::Transferred {
                from,
                amount,
                to,
            } = cte
            {
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
            DebugTraceElement::Regular {
                trace_element,
                ..
            } => Some(trace_element),
            DebugTraceElement::WithFailures {
                ..
            } => None,
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
                DebugTraceElement::Regular {
                    trace_element,
                    ..
                } => Some(trace_element.clone()),
                DebugTraceElement::WithFailures {
                    ..
                } => None,
            })
            .collect()
    }

    /// Get the successful trace elements grouped by which contract they
    /// originated from.
    pub fn trace_elements(&self) -> BTreeMap<ContractAddress, Vec<ContractTraceElement>> {
        let mut map: BTreeMap<ContractAddress, Vec<ContractTraceElement>> = BTreeMap::new();
        for event in self.effective_trace_elements() {
            map.entry(event.affected_address())
                .and_modify(|v| v.push(event.clone()))
                .or_insert_with(|| vec![event.clone()]);
        }
        map
    }

    /// Get the successful contract updates that happened in the transaction.
    /// The order is the order of returns. Concretely, if A calls B (and no
    /// other calls are made) then first there will be "B updated" event,
    /// followed by "A updated", assuming the invocation of both succeeded.
    pub fn updates(&self) -> impl Iterator<Item = &InstanceUpdatedEvent> {
        self.effective_trace_elements().filter_map(|e| {
            if let ContractTraceElement::Updated {
                data,
            } = e
            {
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

    /// Try to parse the return value into a type that implements [`Deserial`].
    ///
    /// Ensures that all bytes of the return value are read.
    pub fn parse_return_value<T: Deserial>(&self) -> ParseResult<T> {
        use contracts_common::{Cursor, Get, ParseError};
        let mut cursor = Cursor::new(&self.return_value);
        let res = cursor.get()?;
        // Check that all bytes have been read, as leftover bytes usually indicate
        // errors.
        if cursor.offset != self.return_value.len() {
            return Err(ParseError::default());
        }
        Ok(res)
    }
}

/// The different types of debug output that can be printed by the
/// [`print_debug`](DebugInfoExt::print_debug) method.
pub enum DebugOutputKind {
    /// Output everything, all host calls and emitted events.
    Full,
    /// Only output emitted events.
    EmittedEvents,
    /// Output all host calls in the order they were emitted.
    HostCalls,
    /// Output host call summary grouped per instance that was affected.
    HostCallsSummary,
    /// Output host call summary grouped per instance that was affected and
    /// entrypoint.
    HostCallsSummaryPerEntrypoint,
}

/// A trait implemented by types which can extract debug information from
/// contract receive entrypoint executions.
//
// Note for maintainers. The return types of many methods here are Box<dyn
// Iterator ...> where they would ideally be `impl Iterator` to both be simpler,
// and to avoid a needless memory allocation. The reason for this is that `impl
// Trait` is only supported in trait methods since Rust 1.74 and at the time of
// writing that is the latest version, and we wish to support older versions for
// the time being.
pub trait DebugInfoExt: Sized {
    /// Print the desired level of debug information that was recorded.
    /// This function is meant to be used in a method-chaining style.
    fn print_debug(self, level: DebugOutputKind) -> Self {
        match level {
            DebugOutputKind::Full => {
                for DebugItem {
                    address,
                    entrypoint,
                    debug_trace,
                    rolled_back,
                } in self.debug_events()
                {
                    eprintln!(
                        "{entrypoint} of instance at {address}{}",
                        if rolled_back {
                            " (rolled back)"
                        } else {
                            ""
                        }
                    );
                    eprintln!("{debug_trace}");
                }
            }
            DebugOutputKind::EmittedEvents => {
                for DebugItem {
                    address,
                    entrypoint,
                    debug_trace,
                    rolled_back,
                } in self.debug_events()
                {
                    eprintln!(
                        "{entrypoint} of instance at {address}{}",
                        if rolled_back {
                            " (rolled back)"
                        } else {
                            ""
                        }
                    );
                    for (_, event) in debug_trace.emitted_events.iter() {
                        eprintln!("{event}");
                    }
                }
            }
            DebugOutputKind::HostCalls => {
                for (addr, emitted_event) in self.emitted_debug_prints() {
                    eprintln!("{addr}:{emitted_event}");
                }
            }
            DebugOutputKind::HostCallsSummary => {
                for (addr, addr_summary) in self.host_calls_summary() {
                    eprintln!("Instance at {addr} host call summary.");
                    for (host_fn, (times, total_nrg)) in addr_summary {
                        eprintln!(
                            "- {host_fn} called {times} times totalling {total_nrg} interpreter \
                             energy spent."
                        )
                    }
                }
            }
            DebugOutputKind::HostCallsSummaryPerEntrypoint => {
                for ((addr, ep), addr_summary) in self.host_calls_summary_per_entrypoint() {
                    eprintln!("Entrypoint {ep} of instance at {addr} host call summary.");
                    for (host_fn, (times, total_nrg)) in addr_summary {
                        eprintln!(
                            "- {host_fn} called {times} times totalling {total_nrg} interpreter \
                             energy spent."
                        )
                    }
                }
            }
        }
        self
    }

    /// Print (to stderr) all the events generated by `concordium_dbg!`
    /// statements.
    fn print_emitted_events(self) -> Self { self.print_debug(DebugOutputKind::EmittedEvents) }

    /// Get an iterator over all the debug traces emitted by the execution.
    fn debug_events(&self) -> Box<dyn Iterator<Item = DebugItem<'_>> + '_>;

    /// Get an iterator over all host calls that have occurred, both in the
    /// remaining trace and in the rolled back part.
    fn host_calls(&self) -> Box<dyn Iterator<Item = HostCallInfo<'_>> + '_> {
        Box::new(self.debug_events().flat_map(|de| {
            de.debug_trace.host_call_trace.iter().map(
                move |(
                    _,
                    HostCall {
                        host_function,
                        energy_used,
                    },
                )| {
                    HostCallInfo {
                        address:       de.address,
                        entrypoint:    de.entrypoint,
                        host_function: *host_function,
                        energy_used:   *energy_used,
                        rolled_back:   de.rolled_back,
                    }
                },
            )
        }))
    }

    /// Get an iterator over all the emitted `concordium_dbg!` events.
    fn emitted_debug_prints(
        &self,
    ) -> Box<dyn Iterator<Item = (ContractAddress, &EmittedDebugStatement)> + '_> {
        Box::new(self.debug_events().flat_map(|de| {
            de.debug_trace.emitted_events.iter().map(move |(_, statement)| (de.address, statement))
        }))
    }

    /// Get  host function calls grouped by contract address that
    /// generated them. The value at each address and host function is the
    /// pair of the number of times the host function was called, and the total
    /// amount of interpreter energy that was used by all the calls.
    fn host_calls_summary(
        &self,
    ) -> BTreeMap<ContractAddress, BTreeMap<HostFunctionV1, (usize, InterpreterEnergy)>> {
        let mut out = BTreeMap::new();
        for HostCallInfo {
            address,
            host_function,
            energy_used,
            ..
        } in self.host_calls()
        {
            let at_addr: &mut BTreeMap<HostFunctionV1, (usize, InterpreterEnergy)> =
                out.entry(address).or_default();
            let entry = at_addr.entry(host_function).or_insert((0, InterpreterEnergy::new(0)));
            entry.1.energy += energy_used.energy;
            entry.0 += 1;
        }
        out
    }

    /// Get  host function calls grouped by contract address and entrypoint that
    /// generated them. The value at each address and host function is the
    /// pair of the number of times the host function was called, and the total
    /// amount of interpreter energy that was used by all the calls.
    fn host_calls_summary_per_entrypoint(
        &self,
    ) -> BTreeMap<
        (ContractAddress, EntrypointName<'_>),
        BTreeMap<HostFunctionV1, (usize, InterpreterEnergy)>,
    > {
        let mut out = BTreeMap::new();
        for HostCallInfo {
            address,
            host_function,
            energy_used,
            entrypoint,
            ..
        } in self.host_calls()
        {
            let at_addr: &mut BTreeMap<HostFunctionV1, (usize, InterpreterEnergy)> =
                out.entry((address, entrypoint)).or_default();
            let entry = at_addr.entry(host_function).or_insert((0, InterpreterEnergy::new(0)));
            entry.1.energy += energy_used.energy;
            entry.0 += 1;
        }
        out
    }
}

impl DebugInfoExt for ContractInvokeSuccess {
    fn debug_events(&self) -> Box<dyn Iterator<Item = DebugItem<'_>> + '_> {
        Box::new(debug_events_worker(false, &self.trace_elements))
    }
}

impl DebugInfoExt for ContractInvokeError {
    fn debug_events(&self) -> Box<dyn Iterator<Item = DebugItem<'_>> + '_> {
        Box::new(debug_events_worker(true, &self.trace_elements))
    }
}

impl DebugInfoExt for Result<ContractInvokeSuccess, ContractInvokeError> {
    fn debug_events(&self) -> Box<dyn Iterator<Item = DebugItem<'_>> + '_> {
        match self {
            Ok(v) => v.debug_events(),
            Err(v) => v.debug_events(),
        }
    }
}

/// Get an iterator over all the debug traces emitted by the execution.
fn debug_events_worker(
    rolled_back: bool,
    initial_events: &[DebugTraceElement],
) -> impl Iterator<Item = DebugItem<'_>> {
    enum Next<'a> {
        Remaining((bool, &'a [DebugTraceElement])),
        Emit(DebugItem<'a>),
    }
    struct DebugTraceElementsIter<'a> {
        stack: Vec<Next<'a>>,
    }

    impl<'a> Iterator for DebugTraceElementsIter<'a> {
        type Item = DebugItem<'a>;

        fn next(&mut self) -> Option<Self::Item> {
            loop {
                let top = self.stack.pop()?;
                let top = match top {
                    Next::Remaining(top) => top,
                    Next::Emit(v) => return Some(v),
                };
                let (first, rest) = top.1.split_first()?;
                if !rest.is_empty() {
                    self.stack.push(Next::Remaining((top.0, rest)));
                }
                match first {
                    DebugTraceElement::Regular {
                        entrypoint,
                        trace_element,
                        energy_used: _,
                        debug_trace,
                    } => {
                        return Some(DebugItem {
                            address: trace_element.affected_address(),
                            entrypoint: entrypoint.as_entrypoint_name(),
                            debug_trace,
                            rolled_back: false,
                        });
                    }
                    DebugTraceElement::WithFailures {
                        contract_address,
                        entrypoint,
                        error: _,
                        trace_elements,
                        energy_used: _,
                        debug_trace,
                    } => {
                        self.stack.push(Next::Emit(DebugItem {
                            address: *contract_address,
                            entrypoint: entrypoint.as_entrypoint_name(),
                            debug_trace,
                            rolled_back: true,
                        }));
                        if !trace_elements.is_empty() {
                            self.stack.push(Next::Remaining((true, trace_elements)));
                        }
                    }
                }
            }
        }
    }
    DebugTraceElementsIter {
        stack: vec![Next::Remaining((rolled_back, initial_events))],
    }
}

/// A wrapper for [`ContractTraceElement`], which provides additional
/// information for testing and debugging. Most notably, it contains trace
/// elements for failures, which are normally discarded by the node.
#[derive(Debug)]
pub enum DebugTraceElement {
    /// A regular trace element with some additional data, e.g., energy usage
    /// and the entrypoint.
    /// This variant may be included in the `WithFailures` list of
    /// trace elements.
    Regular {
        /// The entrypoint.
        entrypoint:    OwnedEntrypointName,
        /// The trace element.
        trace_element: ContractTraceElement,
        /// The energy used so far.
        energy_used:   Energy,
        debug_trace:   DebugTracker,
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
        /// Detailed breakdown of debug output and host calls produced so far.
        debug_trace:      DebugTracker,
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
    Trap {
        error: ExecutionError,
    },
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
    ExecutionError {
        failure_kind: v1::InvokeFailure,
    },
    /// Ran out of energy.
    #[error("Ran out of energy")]
    OutOfEnergy {
        debug_trace: DebugTracker,
    },
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

/// The error returned when external contract invocations fail.
#[derive(Debug, Error)]
pub enum ContractInvokeExternalError {
    /// The external contract invocation was executed, but resulted in a
    /// failure.
    #[error(
        "External contract invocation was executed, but failed after using {energy_used}NRG with \
         error {reason:?}."
    )]
    Failure {
        /// The reason why the invoke failed.
        reason:       sdk::types::RejectReason,
        /// The energy used before failure.
        energy_used:  Energy,
        /// The value returned.
        return_value: ReturnValue,
    },
    /// The external contract invocation failed due to an external node error.
    #[error("External contract invocation failed due to an external node error: {error}")]
    ExternalNodeError {
        #[from]
        /// The external node error.
        error: ExternalNodeError,
    },
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
/// `u64::MAX / 100_000_000_000`.
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
    /// The attempt to connect to an external node timed out.
    #[error("The attempt to connect to an external node timed out.")]
    ConnectTimeout,
    /// The query to check the `external_query_block` timed out.
    #[error("The query to check the `external_query_block` timed out.")]
    CheckQueryBlockTimeout,
    /// The specified external query block does not exist.
    #[error("The specified external query block {query_block} does not exist.")]
    QueryBlockDoesNotExist {
        query_block: BlockHash,
    },
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
    /// The query timed out.
    #[error("The query timed out.")]
    QueryTimeout,
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
    /// `u64::MAX / 100_000_000_000`.
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
    /// [`ChainBuilder::block_time_from_external`] were provided, which is not
    /// allowed.
    #[error(
        "Conflicting block time configuration: `block_time` and `block_time_from_external` cannot \
         both be used."
    )]
    ConflictingBlockTime,
    /// Could not configure the microCCD/euro exchange rate because both the
    /// [`ChainBuilder::micro_ccd_per_euro`] and
    /// [`ChainBuilder::micro_ccd_per_euro_from_external`] were provided, which
    /// is not allowed.
    #[error(
        "Conflicting microCCD per euro configuration: `micro_ccd_per_euro` and \
         `micro_ccd_per_euro_from_external` cannot both be used."
    )]
    ConflictingMicroCCDPerEuro,
    /// Could not configure the euro/energy exchange rate because both the
    /// [`ChainBuilder::euro_per_energy`] and
    /// [`ChainBuilder::euro_per_energy_from_external`] were provided, which is
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

/// The contract address of an contract on an external node.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExternalContractAddress {
    /// The contract address.
    pub(crate) address: ContractAddress,
}

/// The address of an account on an external node.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExternalAccountAddress {
    /// The account address.
    pub(crate) address: AccountAddress,
}

/// Either an external contract address or an external account address.
///
/// External means that it is an entity that exists on an external node.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExternalAddress {
    Account(ExternalAccountAddress),
    Contract(ExternalContractAddress),
}

impl ExternalAddress {
    /// Convert to an [`Address`].
    ///
    /// This is an internal method instead of a [`From`] implementation, as it
    /// should be difficult to conflate external and regular addresses.
    pub(crate) fn to_address(self) -> Address {
        match self {
            ExternalAddress::Account(ExternalAccountAddress {
                address,
            }) => Address::Account(address),
            ExternalAddress::Contract(ExternalContractAddress {
                address,
            }) => Address::Contract(address),
        }
    }
}

/// Data needed to invoke an external smart contract instance.
///
/// This is nearly identical to
/// [`UpdateContractPayload`](concordium_rust_sdk::base::transactions::UpdateContractPayload)
/// except that it uses an [`ExternalContractAddress`] instead of an
/// [`ContractAddress`].
#[derive(Debug, Clone)]
pub struct InvokeExternalContractPayload {
    /// Send the given amount of CCD together with the message to the
    /// contract instance.
    pub amount:       Amount,
    /// Address of the external contract instance to invoke.
    pub address:      ExternalContractAddress,
    /// Name of the method to invoke on the contract.
    pub receive_name: OwnedReceiveName,
    /// Message to send to the contract instance.
    pub message:      OwnedParameter,
}

impl From<ExternalAccountAddress> for ExternalAddress {
    fn from(addr: ExternalAccountAddress) -> Self { Self::Account(addr) }
}

impl From<ExternalContractAddress> for ExternalAddress {
    fn from(addr: ExternalContractAddress) -> Self { Self::Contract(addr) }
}
