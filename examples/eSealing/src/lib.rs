//! A contract implementing an eSealing service.
//!
//! If you seal a file, you can prove that it was in your possession at the time
//! of sealing. The dApp flow will be:
//! - Upload a file from the computer at the front-end => register its file hash
//!   in the smart contract
//! - Upload a file from the computer at the front-end => retrieve the timestamp
//!   and witness (sender_account) from the smart contract to prove that the
//!   witness (sender_account) was in possession of that file at that time.
//!
//! Only accounts can register a file hash. During the registration, the
//! timestamp is recorded together with the witness (sender_account) that
//! registered the file hash. Each file hash can only be registered once.
//! This is because we want to record the first time when the witness
//! (sender_account) had access to that file. Re-registering a file hash (by a
//! different witness) would not prove that the second witness is also in
//! possession of that file because the second witness could have read the
//! file hash during the initial registration transaction from the blockchain.
#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;

/// The different errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
pub enum ContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Failed logging: Log is full.
    LogFull,
    /// Failed logging: Log is malformed.
    LogMalformed,
    /// Only accounts can register a file hash.
    OnlyAccount,
    /// Each file hash can only be registered once.
    AlreadyRegistered,
}

/// Mapping the logging errors to ContractError.
impl From<LogError> for ContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

/// The state tracked for each file.
#[derive(Serialize, Clone, Copy, SchemaType, PartialEq, Eq, Debug)]
pub struct FileState {
    /// The timestamp when this file hash was registered.
    pub timestamp: Timestamp,
    /// The witness (sender_account) that registered this file hash.
    pub witness:   AccountAddress,
}

/// The contract state.
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S = StateApi> {
    files: StateMap<HashSha2256, FileState, S>,
}

impl State {
    /// Create a new state with no files registered.
    fn new(state_builder: &mut StateBuilder) -> Self {
        State {
            files: state_builder.new_map(),
        }
    }

    /// Check if a file exists.
    fn file_exists(&self, file_hash: &HashSha2256) -> bool {
        let file = self.files.get(file_hash);

        file.is_some()
    }

    /// Get recorded FileState (timestamp and witness) from a specific file
    /// hash.
    fn get_file_state(&self, file_hash: HashSha2256) -> Option<FileState> {
        self.files.get(&file_hash).map(|v| *v)
    }

    /// Add a new file hash (replaces existing file if present).
    fn add_file(&mut self, file_hash: HashSha2256, timestamp: Timestamp, witness: AccountAddress) {
        self.files.insert(file_hash, FileState {
            timestamp,
            witness,
        });
    }
}

/// Tagged events to be serialized for the event log.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub enum Event {
    Registration(RegistrationEvent),
}

/// The RegistrationEvent is logged when a new file hash is registered.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct RegistrationEvent {
    /// Hash of the file to be registered by the witness (sender_account).
    pub file_hash: HashSha2256,
    /// Witness (sender_account) that registered the above file hash.
    pub witness:   AccountAddress,
    /// Timestamp when this file hash was registered in the smart contract.
    pub timestamp: Timestamp,
}

/// Init function that creates this eSealing smart contract.
#[init(contract = "eSealing", event = "Event")]
fn contract_init(_ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<State> {
    Ok(State::new(state_builder))
}

/// Register a new file.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - If the file hash has already been registered.
/// - If a smart contract tries to register the file hash.
#[receive(
    contract = "eSealing",
    name = "registerFile",
    parameter = "HashSha2256",
    error = "ContractError",
    mutable,
    enable_logger
)]
fn register_file(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    // Ensure that only accounts can register a file.
    let sender_account = match ctx.sender() {
        Address::Contract(_) => bail!(ContractError::OnlyAccount),
        Address::Account(account_address) => account_address,
    };

    let file_hash: HashSha2256 = ctx.parameter_cursor().get()?;

    // Ensure that the file hash hasn't been registered so far.
    ensure!(!host.state().file_exists(&file_hash), ContractError::AlreadyRegistered);

    let timestamp = ctx.metadata().slot_time();

    // Register the file hash.
    host.state_mut().add_file(file_hash, timestamp, sender_account);

    // Log the event.
    logger.log(&Event::Registration(RegistrationEvent {
        file_hash,
        witness: sender_account,
        timestamp,
    }))?;

    Ok(())
}

/// Get the `FileState` (timestamp and witness) of a registered file hash.
/// If the file hash has not been registered, this query returns `None`.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "eSealing",
    name = "getFile",
    parameter = "HashSha2256",
    error = "ContractError",
    return_value = "Option<FileState>"
)]
fn get_file(ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<Option<FileState>> {
    let file_hash: HashSha2256 = ctx.parameter_cursor().get()?;
    Ok(host.state().get_file_state(file_hash))
}
