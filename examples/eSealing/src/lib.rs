//! A contract implementing an eSealing service.
use base58check::ToBase58Check;
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
    /// Only account.
    OnlyAccount,
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

/// The state tracked for each address.
#[derive(Serial, DeserialWithState, Deletable, StateClone)]
#[concordium(state_parameter = "S")]
struct AddressState<S> {
    /// The number of tokens owned by this address.
    timestamps: StateSet<Timestamp, S>,
    /// The address which are currently enabled as operators for this token and
    /// this address.
    witnesses:  StateSet<AccountAddress, S>,
}

#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S> {
    files: StateMap<String, AddressState<S>, S>,
}

impl<S: HasStateApi> State<S> {
    fn new(state_builder: &mut StateBuilder<S>) -> Self {
        State {
            files: state_builder.new_map(),
        }
    }

    fn find_file(&self, file_hash: &str) -> bool {
        let record = self.files.get(&file_hash.to_string());

        match record {
            Some(_entry) => {
                // file exists
                true
            }
            None => false,
        }
    }

    fn get_witnesses(&self, file_hash: &str) -> ReceiveResult<Vec<AccountAddress>> {
        let record = self.files.get(&file_hash.to_string());

        match record {
            Some(entry) => {
                // file exists
                Result::Ok(entry.witnesses.iter().map(|x| *x.deref()).collect())
            }
            None => Result::Ok([].to_vec()),
        }
    }

    fn add_witness(&mut self, file_hash: &str, witness: AccountAddress) {
        self.files.get_mut(&file_hash.to_string()).unwrap().witnesses.insert(witness);
    }

    fn add_file(&mut self, file_hash: &str, state_builder: &mut StateBuilder<S>) {
        self.files.insert(file_hash.to_string(), AddressState {
            timestamps: state_builder.new_set(),
            witnesses:  state_builder.new_set(),
        });
    }
}

#[derive(Debug, Serial, SchemaType)]
enum Event {
    WitnessAdded(WitnessAddedEvent),
    FileAdded(FileAddedEvent),
}

/// The event is logged when a new witness is added.
#[derive(Debug, Serialize, SchemaType)]
pub struct WitnessAddedEvent {
    ///
    file_hash: String,
    ///
    witness:   String,
}

/// The event is logged when a new file is added.
#[derive(Debug, Serialize, SchemaType)]
pub struct FileAddedEvent {
    ///
    file_hash: String,
}

#[init(contract = "eSealing", event = "Event")]
fn contract_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    Ok(State::new(state_builder))
}

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
    let sender_address = match ctx.sender() {
        Address::Contract(_) => bail!(ContractError::OnlyAccount),
        Address::Account(account_address) => account_address,
    };

    let file_hash: String = ctx.parameter_cursor().get()?;

    let witness_string = sender_address.0.to_base58check(1);

    let (state, builder) = host.state_and_builder();
    let record = state.find_file(&file_hash);

    match record {
        true => {
            // file exists
            state.add_witness(&file_hash, sender_address);
            logger.log(&Event::WitnessAdded(WitnessAddedEvent {
                file_hash,
                witness: witness_string,
            }))?;
        }
        false => {
            // file does not exist. Add file, Add Witness
            state.add_file(&file_hash, builder);
            logger.log(&Event::FileAdded(FileAddedEvent {
                file_hash: file_hash.clone(),
            }))?;

            state.add_witness(&file_hash, sender_address);
            logger.log(&Event::WitnessAdded(WitnessAddedEvent {
                file_hash,
                witness: witness_string,
            }))?;
        }
    }

    Result::Ok(())
}

#[receive(contract = "eSealing", name = "getfile", parameter = "String")]
fn get_file<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<Vec<AccountAddress>> {
    let file_hash: String = ctx.parameter_cursor().get()?;
    let state = host.state();
    let record = state.find_file(&file_hash);

    match record {
        true => {
            // file exists
            state.get_witnesses(&file_hash)
        }
        false => Result::Ok([].to_vec()),
    }
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use base58check::ToBase58Check;
    use test_infrastructure::*;

    const ACCOUNT_0: AccountAddress = AccountAddress([1u8; 32]);
    const ADDRESS_0: Address = Address::Account(ACCOUNT_0);
    const ACCOUNT_1: AccountAddress = AccountAddress([2u8; 32]);
    const ADDRESS_1: Address = Address::Account(ACCOUNT_1);
    const FILE_HASH_0: &str = "14fe0aed941aa0a0be1118d7b7dd70bfca475310c531f1b5a179b336c075db65";

    #[concordium_test]
    fn test_init() {
        let ctx = TestInitContext::empty();
        let mut builder = TestStateBuilder::new();
        let init_result = contract_init(&ctx, &mut builder);

        let state = init_result.expect_report("Contract Initialization failed");
        claim_eq!(state.files.iter().count(), 0, "No files present after initialization");
    }

    #[concordium_test]
    fn test_register_file() {
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);

        let param_string = FILE_HASH_0.to_string();
        let param_bytes = to_bytes(&param_string);
        ctx.set_parameter(&param_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::new(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        let result = register_file(&ctx, &mut host, &mut logger);
        claim!(result.is_ok(), "Results in rejection");
        claim_eq!(logger.logs.len(), 2, "Exactly 2 event should be logger");

        let file_added_event = Event::FileAdded(FileAddedEvent {
            file_hash: FILE_HASH_0.to_string(),
        });
        claim!(
            logger.logs.contains(&to_bytes(&file_added_event)),
            "Should contain file added event"
        );

        let witness_added_event = Event::WitnessAdded(WitnessAddedEvent {
            file_hash: FILE_HASH_0.to_string(),
            witness:   ACCOUNT_0.0.to_base58check(1),
        });
        claim!(
            logger.logs.contains(&to_bytes(&witness_added_event)),
            "Should contain witness added event"
        );
    }

    #[concordium_test]
    fn test_register_file_twice() {
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);

        let param_string = FILE_HASH_0.to_string();
        let param_bytes = to_bytes(&param_string);
        ctx.set_parameter(param_bytes.as_slice());

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::new(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        let result = register_file(&ctx, &mut host, &mut logger);
        claim!(result.is_ok(), "Results in rejection");
        claim_eq!(logger.logs.len(), 2, "Exactly 2 event should be logger");

        let file_added_event = Event::FileAdded(FileAddedEvent {
            file_hash: FILE_HASH_0.to_string(),
        });
        claim!(
            logger.logs.contains(&to_bytes(&file_added_event)),
            "Should contain file added event"
        );

        let witness_added_event = Event::WitnessAdded(WitnessAddedEvent {
            file_hash: FILE_HASH_0.to_string(),
            witness:   ACCOUNT_0.0.to_base58check(1),
        });
        claim!(
            logger.logs.contains(&to_bytes(&witness_added_event)),
            "Should contain witness added event"
        );

        // register second
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_1);

        let param_string = FILE_HASH_0.to_string();
        let param_bytes = to_bytes(&param_string);
        ctx.set_parameter(param_bytes.as_slice());

        let mut logger = TestLogger::init();

        let result = register_file(&ctx, &mut host, &mut logger);
        claim!(result.is_ok(), "Results in rejection");
        claim_eq!(logger.logs.len(), 1, "Exactly 1 event should be logger");

        let witness_added_event = Event::WitnessAdded(WitnessAddedEvent {
            file_hash: FILE_HASH_0.to_string(),
            witness:   ACCOUNT_1.0.to_base58check(1),
        });
        claim!(
            logger.logs.contains(&to_bytes(&witness_added_event)),
            "Should contain witness added event"
        );
    }

    #[concordium_test]
    fn test_get_file() {
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);

        let param_string = FILE_HASH_0.to_string();
        let param_bytes = to_bytes(&param_string);
        ctx.set_parameter(param_bytes.as_slice());

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::new(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        let result = register_file(&ctx, &mut host, &mut logger);
        claim!(result.is_ok(), "file was not registered");

        let witnesses_result = get_file(&ctx, &host);
        claim!(witnesses_result.is_ok(), "could not get witnesses");

        let witnesses = witnesses_result.unwrap();
        claim_eq!(witnesses.len(), 1, "there should be 1 witness");
        claim_eq!(witnesses[0], ACCOUNT_0, "witness account address should match");
    }
}
