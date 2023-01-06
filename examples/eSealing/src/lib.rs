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
//! possession of that file or that it just observed the file hash during the
//! initial registration hence a file hash can only be registered once.
use concordium_std::*;

/// The different errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
enum ContractError {
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
#[derive(Serial, Deserial)]
struct FileState {
    /// The timestamp when this file hash was registered.
    timestamp: Timestamp,
    /// The witness (sender_account) that registered this file hash.
    witness:   AccountAddress,
}

/// FileHash type is a fixed-length byte array.
type FileHash = [u8; 32];

/// The contract state.
#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S> {
    files: StateMap<FileHash, FileState, S>,
}

impl<S: HasStateApi> State<S> {
    /// Create a new state with no files registered.
    fn new(state_builder: &mut StateBuilder<S>) -> Self {
        State {
            files: state_builder.new_map(),
        }
    }

    /// Check if a file exists.
    fn file_exists(&self, file_hash: &FileHash) -> bool {
        let file = self.files.get(file_hash);

        file.is_some()
    }

    /// Get recorded timestamp and witness from a specific file hash.
    fn get_timestamp_and_witness(
        &self,
        file_hash: FileHash,
    ) -> ReceiveResult<(Timestamp, AccountAddress)> {
        let record = self.files.get(&file_hash);

        match record {
            // File exists.
            Some(entry) => Result::Ok((entry.timestamp, entry.witness)),
            // File does not exist.
            None => Result::Ok((Timestamp::from_timestamp_millis(0), AccountAddress([0u8; 32]))),
        }
    }

    /// Add a new file hash.
    fn add_file(&mut self, file_hash: FileHash, timestamp: Timestamp, witness: AccountAddress) {
        self.files.insert(file_hash, FileState {
            timestamp,
            witness,
        });
    }
}

/// Tagged events to be serialized for the event log.
#[derive(Debug, Serial, SchemaType)]
enum Event {
    Registration(RegistrationEvent),
}

/// The RegistrationEvent is logged when a new file hash is registered.
#[derive(Debug, Serialize, SchemaType)]
pub struct RegistrationEvent {
    /// Hash of the file to be registered by the witness (sender_account).
    file_hash: FileHash,
    /// Witness (sender_account) that registered the above file hash.
    witness:   AccountAddress,
    /// Timestamp when this file hash was registered in the smart contract.
    timestamp: Timestamp,
}

/// Init function that creates this eSealing smart contract.
#[init(contract = "eSealing", event = "Event")]
fn contract_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    Ok(State::new(state_builder))
}

/// Register a new file.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - If file hash has already been registered.
/// - If a smart contract tries to register the file hash.
#[receive(
    contract = "eSealing",
    name = "registerFile",
    parameter = "FileHash",
    error = "ContractError",
    mutable,
    enable_logger
)]
fn register_file<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    // Ensure that only accounts can register a file.
    let sender_account = match ctx.sender() {
        Address::Contract(_) => bail!(ContractError::OnlyAccount),
        Address::Account(account_address) => account_address,
    };

    let file_hash: FileHash = ctx.parameter_cursor().get()?;

    let (state, _) = host.state_and_builder();

    // Ensure that the file hash hasn't been registered so far.
    ensure!(!state.file_exists(&file_hash), ContractError::AlreadyRegistered);

    let slot_time = ctx.metadata().slot_time();

    // Register the file hash.
    state.add_file(file_hash, slot_time, sender_account);

    // Log the event.
    logger.log(&Event::Registration(RegistrationEvent {
        file_hash,
        witness: sender_account,
        timestamp: slot_time,
    }))?;

    Result::Ok(())
}

/// Get the timestamp and witness of a registered file hash.
/// If the file hash has not been registered, this query returns
/// (Timestamp::from_timestamp_millis(0), AccountAddress([0u8; 32])).
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "eSealing",
    name = "getFile",
    parameter = "FileHash",
    error = "ContractError",
    return_value = "(Timestamp, AccountAddress)"
)]
fn get_file<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<(Timestamp, AccountAddress)> {
    let file_hash: FileHash = ctx.parameter_cursor().get()?;
    host.state().get_timestamp_and_witness(file_hash)
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    const ACCOUNT_0: AccountAddress = AccountAddress([1u8; 32]);
    const ADDRESS_0: Address = Address::Account(ACCOUNT_0);
    const DEFAULT_ACCOUNT: AccountAddress = AccountAddress([0u8; 32]);
    const FILE_HASH: FileHash = [2u8; 32];
    const TIME: u64 = 1;

    /// Test initializing contract.
    #[concordium_test]
    fn test_init() {
        // Set up the context.
        let ctx = TestInitContext::empty();
        let mut builder = TestStateBuilder::new();

        // Initialize the contract.
        let init_result = contract_init(&ctx, &mut builder);

        // Check the state.
        let state = init_result.expect_report("Contract Initialization failed");
        claim_eq!(state.files.iter().count(), 0, "No files present after initialization");
    }

    /// Test registering file hash.
    #[concordium_test]
    fn test_register_file() {
        // Set up the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(TIME));

        // Set up the parameter.
        let param_bytes = to_bytes(&FILE_HASH);
        ctx.set_parameter(&param_bytes);

        // Set up the state and host.
        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::new(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Register the file hash
        let result = register_file(&ctx, &mut host, &mut logger);
        claim!(result.is_ok(), "results in rejection");

        // Check the event.
        let event = Event::Registration(RegistrationEvent {
            file_hash: FILE_HASH,
            witness:   ACCOUNT_0,
            timestamp: Timestamp::from_timestamp_millis(TIME),
        });
        claim!(logger.logs.contains(&to_bytes(&event)), "should contain event");
    }

    /// Test can not register a file hash twice.
    #[concordium_test]
    fn test_can_not_register_file_twice() {
        // Set up the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(TIME));

        // Set up the parameter.
        let param_bytes = to_bytes(&FILE_HASH);
        ctx.set_parameter(param_bytes.as_slice());

        // Set up the state and host.
        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::new(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Register the file hash.
        let result = register_file(&ctx, &mut host, &mut logger);
        claim!(result.is_ok(), "results in rejection");

        // Check the event.
        let event = Event::Registration(RegistrationEvent {
            file_hash: FILE_HASH,
            witness:   ACCOUNT_0,
            timestamp: Timestamp::from_timestamp_millis(TIME),
        });
        claim!(logger.logs.contains(&to_bytes(&event)), "should contain event");

        // Try to register the file hash a second time.
        let result = register_file(&ctx, &mut host, &mut logger);

        // Check that invoke failed.
        claim_eq!(
            result,
            Err(ContractError::AlreadyRegistered),
            "invoke should fail because file hash is already registered"
        );
    }

    /// Test getting file record from state.
    #[concordium_test]
    fn test_get_file() {
        // Set up the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(TIME));

        // Set up the parameter.
        let param_bytes = to_bytes(&FILE_HASH);
        ctx.set_parameter(param_bytes.as_slice());

        // Set up the state and host.
        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::new(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Check that there are no records about the file before it has been registered.
        let record_result = get_file(&ctx, &host);
        claim!(record_result.is_ok(), "could not get record");

        // Check the returned values.
        let record = record_result.unwrap();
        claim_eq!(record.0, Timestamp::from_timestamp_millis(0), "timestamp should not be set");
        claim_eq!(record.1, DEFAULT_ACCOUNT, "witness account should not be set");

        // Register the file hash.
        let result = register_file(&ctx, &mut host, &mut logger);
        claim!(result.is_ok(), "file was not registered");

        // Get the record about this file.
        let record_result = get_file(&ctx, &host);
        claim!(record_result.is_ok(), "could not get record");

        // Check the returned values.
        let record = record_result.unwrap();
        claim_eq!(record.0, Timestamp::from_timestamp_millis(TIME), "timestamp should match");
        claim_eq!(record.1, ACCOUNT_0, "witness account should match");
    }
}
