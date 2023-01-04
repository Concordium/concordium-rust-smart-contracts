//! A contract implementing an eSealing service.
//!
//! Only accounts can register a file hash. During the registration, the
//! timestamp is recorded together with the witness (sender_account) that
//! registered the file hash.
//!
//! Every account can only register each file hash
//! once. This is because we want to record the time when the witness
//! (sender_account) first had access to that file. Re-registering a file hash
//! by the same account would not give us any additional information.
//!
//! But: A second account can register a file hash that was already previously
//! registered. This second account will be added as another witness together
//! with the timestamp when the second account called the `register_file`
//! function. We know that the second account is most likely now also in
//! possession of the file if it has used this eSealing service via the
//! front-end. But this is not guaranteed since the second account could
//! register a random file hash it found in the events by interacting with the
//! smart contract directly (without using the front-end).
use concordium_std::*;
use std::ops::Deref;

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
    /// Every account can only register each file hash once.
    AlreadyRecorded,
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
#[derive(Serial, DeserialWithState, Deletable, StateClone)]
#[concordium(state_parameter = "S")]
struct FileState<S> {
    /// The timestamps when this file hash was recorded.
    timestamps:    Vec<Timestamp>,
    /// The witnesses (sender_accounts) that recorded this file hash.
    witnesses:     Vec<AccountAddress>,
    /// The witnesses (sender_accounts) stored in a set. This
    /// set enables us to check that a witness has not been recorded
    /// without iterating through the above array which
    /// saves execution time in the `register_file` function.
    witnesses_set: StateSet<AccountAddress, S>,
}

/// The contract state.
#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S> {
    files: StateMap<String, FileState<S>, S>,
}

impl<S: HasStateApi> State<S> {
    /// Creates a new state with no files recorded.
    fn new(state_builder: &mut StateBuilder<S>) -> Self {
        State {
            files: state_builder.new_map(),
        }
    }

    /// Check if a file exists.
    fn file_exists(&self, file_hash: &str) -> bool {
        let record = self.files.get(&file_hash.to_string());

        match record {
            Some(_entry) => true,
            None => false,
        }
    }

    /// Check if a witness exists.
    fn witness_exists(&self, file_hash: &str, witness: AccountAddress) -> bool {
        let records = self.files.get(&file_hash.to_string());

        match records {
            Some(entry) => entry.witnesses_set.contains(&witness),
            None => false,
        }
    }

    /// Get all records from a specific file hash.
    fn get_records(&self, file_hash: &str) -> ReceiveResult<(Vec<AccountAddress>, Vec<Timestamp>)> {
        let records = self.files.get(&file_hash.to_string());

        match records {
            Some(entry) => {
                // File exists
                Result::Ok((
                    entry.witnesses.iter().map(|x| *x.deref()).collect(),
                    entry.timestamps.iter().map(|x| *x.deref()).collect(),
                ))
            }
            None => Result::Ok(([].to_vec(), [].to_vec())),
        }
    }

    /// Add a new records to a specific file hash.
    fn add_record(&mut self, file_hash: &str, witness: AccountAddress, time: Timestamp) {
        self.files.get_mut(&file_hash.to_string()).unwrap().timestamps.push(time);
        self.files.get_mut(&file_hash.to_string()).unwrap().witnesses.push(witness);
        self.files.get_mut(&file_hash.to_string()).unwrap().witnesses_set.insert(witness);
    }

    /// Add a new file.
    fn add_file(&mut self, file_hash: &str, state_builder: &mut StateBuilder<S>) {
        self.files.insert(file_hash.to_string(), FileState {
            timestamps:    Vec::new(),
            witnesses:     Vec::new(),
            witnesses_set: state_builder.new_set(),
        });
    }
}

/// Tagged events to be serialized for the event log.
#[derive(Debug, Serial, SchemaType)]
enum Event {
    WitnessAdded(WitnessAddedEvent),
    FileAdded(FileAddedEvent),
}

/// The WitnessAddedEvent is logged when a new witness is added.
#[derive(Debug, Serialize, SchemaType)]
pub struct WitnessAddedEvent {
    /// Hash of the file to be registered by the witness (sender_account).
    file_hash: String,
    /// Witness (sender_account) that registered above file_hash.
    witness:   AccountAddress,
    /// Timestamp when this record was added to this smart contract.
    timestamp: Timestamp,
}

/// The FileAddedEvent is logged when a new file is added.
#[derive(Debug, Serialize, SchemaType)]
pub struct FileAddedEvent {
    /// Hash of the file to be registered.
    file_hash: String,
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
/// - If file hash has already been registered by the same witness
///   (sender_account).
/// - If a smart contract tries to register the file hash.
#[receive(
    contract = "eSealing",
    name = "registerFile",
    parameter = "String",
    error = "ContractError",
    mutable,
    enable_logger
)]
fn register_file<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    // Ensure that only accounts can register a file
    let sender_account = match ctx.sender() {
        Address::Contract(_) => bail!(ContractError::OnlyAccount),
        Address::Account(account_address) => account_address,
    };

    let file_hash: String = ctx.parameter_cursor().get()?;

    let (state, builder) = host.state_and_builder();

    // Ensure that every account can only register each file hash once.
    ensure!(!state.witness_exists(&file_hash, sender_account), ContractError::AlreadyRecorded);

    let slot_time = ctx.metadata().slot_time();

    let exists = state.file_exists(&file_hash);

    match exists {
        true => {
            // File exists => Add record
            state.add_record(&file_hash, sender_account, slot_time);
            logger.log(&Event::WitnessAdded(WitnessAddedEvent {
                file_hash,
                witness: sender_account,
                timestamp: slot_time,
            }))?;
        }
        false => {
            // File does not exist => Add file and add record
            state.add_file(&file_hash, builder);
            logger.log(&Event::FileAdded(FileAddedEvent {
                file_hash: file_hash.clone(),
            }))?;

            state.add_record(&file_hash, sender_account, slot_time);
            logger.log(&Event::WitnessAdded(WitnessAddedEvent {
                file_hash,
                witness: sender_account,
                timestamp: slot_time,
            }))?;
        }
    }

    Result::Ok(())
}

/// Get all records about a specific file hash.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "eSealing",
    name = "getFile",
    parameter = "String",
    error = "ContractError",
    return_value = "(Vec<AccountAddress>, Vec<Timestamp>)"
)]
fn get_file<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<(Vec<AccountAddress>, Vec<Timestamp>)> {
    let file_hash: String = ctx.parameter_cursor().get()?;
    let state = host.state();
    let exists = state.file_exists(&file_hash);

    match exists {
        true => state.get_records(&file_hash),
        false => Result::Ok(([].to_vec(), [].to_vec())),
    }
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    const ACCOUNT_0: AccountAddress = AccountAddress([1u8; 32]);
    const ADDRESS_0: Address = Address::Account(ACCOUNT_0);
    const ACCOUNT_1: AccountAddress = AccountAddress([2u8; 32]);
    const ADDRESS_1: Address = Address::Account(ACCOUNT_1);
    const FILE_HASH_0: &str = "14fe0aed941aa0a0be1118d7b7dd70bfca475310c531f1b5a179b336c075db65";
    const TIME: u64 = 1;

    /// Test initializing contract
    #[concordium_test]
    fn test_init() {
        // Set up the context
        let ctx = TestInitContext::empty();
        let mut builder = TestStateBuilder::new();

        // Initialize the contract.
        let init_result = contract_init(&ctx, &mut builder);

        // Check the state.
        let state = init_result.expect_report("Contract Initialization failed");
        claim_eq!(state.files.iter().count(), 0, "No files present after initialization");
    }

    /// Test registering file hash
    #[concordium_test]
    fn test_register_file() {
        // Set up the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(TIME));

        // Set up the parameter.
        let param_string = FILE_HASH_0.to_string();
        let param_bytes = to_bytes(&param_string);
        ctx.set_parameter(&param_bytes);

        // Set up the state and host.
        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::new(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Register the file hash
        let result = register_file(&ctx, &mut host, &mut logger);
        claim!(result.is_ok(), "results in rejection");

        // Check the events.
        claim_eq!(logger.logs.len(), 2, "exactly 2 event should be logger");
        let file_added_event = Event::FileAdded(FileAddedEvent {
            file_hash: FILE_HASH_0.to_string(),
        });
        claim!(
            logger.logs.contains(&to_bytes(&file_added_event)),
            "should contain file added event"
        );

        let witness_added_event = Event::WitnessAdded(WitnessAddedEvent {
            file_hash: FILE_HASH_0.to_string(),
            witness:   ACCOUNT_0,
            timestamp: Timestamp::from_timestamp_millis(TIME),
        });
        claim!(
            logger.logs.contains(&to_bytes(&witness_added_event)),
            "should contain witness added event"
        );
    }

    /// Test registering file hash twice
    #[concordium_test]
    fn test_register_file_twice() {
        // Set up the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(TIME));

        // Set up the parameter.
        let param_string = FILE_HASH_0.to_string();
        let param_bytes = to_bytes(&param_string);
        ctx.set_parameter(param_bytes.as_slice());

        // Set up the state and host.
        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::new(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Register the file hash
        let result = register_file(&ctx, &mut host, &mut logger);
        claim!(result.is_ok(), "results in rejection");

        // Check the events.
        claim_eq!(logger.logs.len(), 2, "exactly 2 event should be logger");
        let file_added_event = Event::FileAdded(FileAddedEvent {
            file_hash: FILE_HASH_0.to_string(),
        });
        claim!(
            logger.logs.contains(&to_bytes(&file_added_event)),
            "should contain file added event"
        );

        let witness_added_event = Event::WitnessAdded(WitnessAddedEvent {
            file_hash: FILE_HASH_0.to_string(),
            witness:   ACCOUNT_0,
            timestamp: Timestamp::from_timestamp_millis(TIME),
        });
        claim!(
            logger.logs.contains(&to_bytes(&witness_added_event)),
            "should contain witness added event"
        );

        // Register second time from different account
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_1);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(TIME));

        // Set up the parameter.
        let param_string = FILE_HASH_0.to_string();
        let param_bytes = to_bytes(&param_string);
        ctx.set_parameter(param_bytes.as_slice());

        // Register the file hash
        let result = register_file(&ctx, &mut host, &mut logger);
        claim!(result.is_ok(), "results in rejection");

        // Check the events.
        let witness_added_event = Event::WitnessAdded(WitnessAddedEvent {
            file_hash: FILE_HASH_0.to_string(),
            witness:   ACCOUNT_1,
            timestamp: Timestamp::from_timestamp_millis(TIME),
        });
        claim!(
            logger.logs.contains(&to_bytes(&witness_added_event)),
            "should contain witness added event"
        );
    }

    /// Test getting all records from state.
    #[concordium_test]
    fn test_get_file() {
        // Set up the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(TIME));

        // Set up the parameter.
        let param_string = FILE_HASH_0.to_string();
        let param_bytes = to_bytes(&param_string);
        ctx.set_parameter(param_bytes.as_slice());

        // Set up the state and host.
        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::new(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Register the file hash
        let result = register_file(&ctx, &mut host, &mut logger);
        claim!(result.is_ok(), "file was not registered");

        // Register second time from different account
        ctx.set_sender(ADDRESS_1);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(TIME + 1));

        // Register the file hash
        let result = register_file(&ctx, &mut host, &mut logger);
        claim!(result.is_ok(), "file was not registered");

        // Get all records about this file.
        let records_results = get_file(&ctx, &host);
        claim!(records_results.is_ok(), "could not get records");

        // Check the returned values.
        let records = records_results.unwrap();
        claim_eq!(records.0.len(), 2, "there should be 2 records");
        claim_eq!(records.0[0], ACCOUNT_0, "witness account 1 should match");
        claim_eq!(records.1[0], Timestamp::from_timestamp_millis(TIME), "timestamp 1 should match");
        claim_eq!(records.0[1], ACCOUNT_1, "witness account 2 should match");
        claim_eq!(
            records.1[1],
            Timestamp::from_timestamp_millis(TIME + 1),
            "timestamp 2should match"
        );
    }
}
