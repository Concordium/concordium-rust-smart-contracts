//! A voting smart contract example.
//!
//! # Description
//! A contract that allows for conducting an election with several voting
//! options. An `end_time` is set when the election is initialized. Only
//! accounts are eligible to vote. Each account can change its
//! selected voting option as often as it desires until the `end_time` is
//! reached. No voting will be possible after the `end_time`.
//!
//! # Operations
//! The contract allows for
//!  - `initializing` the election;
//!  - `vote` for one of the voting options;
//!  - `getNumberOfVotes` for a requested voting option;
//!  - `view` general information about the election.
//!
//! Note: Vec<VotingOption> (among other variables) is an input parameter to the
//! `init` function. Since there is a limit to the parameter size (65535 Bytes),
//! the size of the Vec<VotingOption> is limited.
//! https://developer.concordium.software/en/mainnet/smart-contracts/general/contract-instances.html#limits
#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;

/// The human-readable description of a voting option.
type VotingOption = String;
/// The voting options are stored in a vector. The vector index is used to refer
/// to a specific voting option.
type VoteIndex = u32;
/// Number of votes.
type VoteCount = u32;

/// The parameter type for the contract function `vote`.
/// Takes a `vote_index` that the account wants to vote for.
#[derive(Deserial, SchemaType)]
struct VoteParameter {
    /// Voting option index to vote for.
    vote_index: VoteIndex,
}

/// The parameter type for the contract function `init`.
/// Takes a description, the voting options, and the `end_time` to start the
/// election.
#[derive(Deserial, SchemaType)]
struct InitParameter {
    /// The description of the election.
    description: String,
    /// A vector of all voting options.
    options:     Vec<VotingOption>,
    /// The last timestamp that an account can vote.
    /// The election is open from the point in time that this smart contract is
    /// initialized until the `end_time`.
    end_time:    Timestamp,
}

/// The `return_value` type of the contract function `view`.
/// Returns a description, the `end_time`, the voting options as a vector, and
/// the number of voting options of the current election.
#[derive(Serial, Deserial, SchemaType)]
struct VotingView {
    /// The description of the election.
    description: String,
    /// The last timestamp that an account can vote.
    /// The election is open from the point in time that this smart contract is
    /// initialized until the `end_time`.
    end_time:    Timestamp,
    /// A vector of all voting options.
    options:     Vec<VotingOption>,
    /// The number of voting options.
    num_options: u32,
}

/// The contract state
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S: HasStateApi> {
    /// The description of the election.
    /// `StateBox` allows for lazy loading data. This is helpful
    /// in the situations when one wants to do a partial update not touching
    /// this field, which can be large.
    description: StateBox<String, S>,
    /// The map connects a voter to the index of the voted-for voting option.
    ballots:     StateMap<AccountAddress, VoteIndex, S>,
    /// The map connects the index of a voting option to the number of votes
    /// it received so far.
    tally:       StateMap<VoteIndex, VoteCount, S>,
    /// The last timestamp that an account can vote.
    /// The election is open from the point in time that this smart contract is
    /// initialized until the `end_time`.
    end_time:    Timestamp,
    /// A vector of all voting options.
    /// `StateBox` allows for lazy loading data. This is helpful
    /// in the situations when one wants to do a partial update not touching
    /// this field, which can be large.
    options:     StateBox<Vec<VotingOption>, S>,
    /// The number of voting options.
    num_options: u32,
}

/// The different errors that the `vote` function can produce.
#[derive(Reject, Serial, PartialEq, Eq, Debug, SchemaType)]
enum VotingError {
    /// Raised when parsing the parameter failed.
    #[from(ParseError)]
    ParsingFailed,
    /// Raised when the log is full.
    LogFull,
    /// Raised when the log is malformed.
    LogMalformed,
    /// Raised when the vote is placed after the election has ended.
    VotingFinished,
    /// Raised when voting for a voting index that does not exist.
    InvalidVoteIndex,
    /// Raised when a smart contract tries to participate in the election. Only
    /// accounts are allowed to vote.
    ContractVoter,
}

/// Mapping the logging errors to VotingError.
impl From<LogError> for VotingError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

/// A custom alias type for the `Result` type with the error type fixed to
/// `VotingError`.
type VotingResult<T> = Result<T, VotingError>;

/// The event is logged when a new (or replacement) vote is cast by an account.
#[derive(Debug, Serialize, SchemaType)]
pub struct VoteEvent {
    /// The account that casts the vote.
    voter:      AccountAddress,
    /// The index of the voting option that the account is voting for.
    vote_index: VoteIndex,
}

/// The event logged by this smart contract.
#[derive(Debug, Serial, SchemaType)]
pub enum Event {
    /// The event is logged when a new (or replacement) vote is cast by an
    /// account.
    Vote(VoteEvent),
}

// Contract functions

/// Initialize the contract instance and start the election.
/// A description, the vector of all voting options, and an `end_time`
/// have to be provided.
#[init(contract = "voting", parameter = "InitParameter", event = "Event")]
fn init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    // Parse the parameter.
    let param: InitParameter = ctx.parameter_cursor().get()?;
    // Calculate the number of voting options.
    let num_options = param.options.len() as u32;

    // Set the state.
    Ok(State {
        description: state_builder.new_box(param.description),
        ballots: state_builder.new_map(),
        tally: state_builder.new_map(),
        end_time: param.end_time,
        options: state_builder.new_box(param.options),
        num_options,
    })
}

/// Enables accounts to vote for a specific voting option. Each account can
/// change its selected voting option with this function as often as it desires
/// until the `end_time` is reached.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - A contract tries to vote.
/// - It is past the `end_time`.
#[receive(
    contract = "voting",
    name = "vote",
    mutable,
    enable_logger,
    parameter = "VoteParameter",
    error = "VotingError"
)]
fn vote<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> VotingResult<()> {
    // Check that the election hasn't finished yet.
    ensure!(ctx.metadata().slot_time() <= host.state().end_time, VotingError::VotingFinished);

    // Ensure that the sender is an account.
    let acc = match ctx.sender() {
        Address::Account(acc) => acc,
        Address::Contract(_) => return Err(VotingError::ContractVoter),
    };

    // Parse the parameter.
    let param: VoteParameter = ctx.parameter_cursor().get()?;

    let new_vote_index = param.vote_index;

    // Check that vote is in range
    ensure!(new_vote_index < host.state().num_options, VotingError::InvalidVoteIndex);

    if let Some(old_vote_index) = host.state().ballots.get(&acc) {
        let old_vote_index = *old_vote_index;
        // Update the tally for the `old_vote_index` by reducing one vote.
        *host.state_mut().tally.entry(old_vote_index).or_insert(1) -= 1;
    };

    // Insert or replace the vote for the account.
    host.state_mut()
        .ballots
        .entry(acc)
        .and_modify(|old_vote_index| *old_vote_index = new_vote_index)
        .or_insert(new_vote_index);

    // Update the tally for the `new_vote_index` with one additional vote.
    *host.state_mut().tally.entry(new_vote_index).or_insert(0) += 1;

    // Log event for the vote.
    logger.log(&Event::Vote(VoteEvent {
        voter:      acc,
        vote_index: new_vote_index,
    }))?;

    Ok(())
}

/// Get the number of votes for a specific voting option.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "voting",
    name = "getNumberOfVotes",
    parameter = "VoteParameter",
    return_value = "VoteCount"
)]
fn get_votes<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<VoteCount> {
    // Parse the parameter.
    let param: VoteIndex = ctx.parameter_cursor().get()?;

    // Get the number of votes from the tally.
    let result = match host.state().tally.get(&param) {
        Some(votes) => *votes,
        None => 0,
    };

    Ok(result)
}

/// Get the election information.
#[receive(contract = "voting", name = "view", return_value = "VotingView")]
fn view<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<VotingView> {
    // Get information from the state.
    let description = host.state().description.clone();
    let end_time = host.state().end_time;
    let num_options = host.state().num_options;
    let options = host.state().options.clone();

    // Return the election information.
    Ok(VotingView {
        description,
        end_time,
        options,
        num_options,
    })
}

// Tests

#[concordium_cfg_test]
mod tests {
    use super::*;
    use concordium_std::test_infrastructure::*;

    // Test accounts/addresses.
    const ACC_0: AccountAddress = AccountAddress([0; 32]);
    const ACC_1: AccountAddress = AccountAddress([1; 32]);
    const ADDR_ACC_0: Address = Address::Account(ACC_0);
    const ADDR_ACC_1: Address = Address::Account(ACC_1);

    // Set up the test host.
    fn make_test_host(options: Vec<String>, end_time: Timestamp) -> TestHost<State<TestStateApi>> {
        let mut state_builder = TestStateBuilder::new();
        let num_options = options.len() as u32;

        let state = State {
            description: state_builder.new_box("Test description".into()),
            ballots: state_builder.new_map(),
            tally: state_builder.new_map(),
            end_time,
            options: state_builder.new_box(options),
            num_options,
        };
        TestHost::new(state, state_builder)
    }

    /// Test that an account cannot vote if it is past the `end_time` of the
    /// election.
    #[concordium_test]
    fn test_vote_after_finish_time() {
        // Set up the context.
        let end_time = Timestamp::from_timestamp_millis(100);
        let current_time = Timestamp::from_timestamp_millis(200);
        let mut ctx = TestReceiveContext::empty();
        ctx.set_metadata_slot_time(current_time);

        // Set up logger.
        let mut logger = TestLogger::init();

        // Set up the test host.
        let mut host = make_test_host(Vec::new(), end_time);

        // Call the contract function.
        let res = vote(&ctx, &mut host, &mut logger);

        // Check that error is thrown because the election is finished already.
        claim_eq!(
            res,
            Err(VotingError::VotingFinished),
            "Should throw error because voting is finished"
        );
    }

    /// Test that voting fails if the voting index is out of range.
    #[concordium_test]
    fn test_vote_with_invalid_index() {
        // Set up the context.
        let end_time = Timestamp::from_timestamp_millis(100);
        let current_time = Timestamp::from_timestamp_millis(0);
        let mut ctx = TestReceiveContext::empty();
        ctx.set_metadata_slot_time(current_time);
        ctx.set_sender(ADDR_ACC_0);

        // Set up the parameter.
        let vote_parameter = to_bytes(&2);
        ctx.set_parameter(&vote_parameter);

        // Set up logger.
        let mut logger = TestLogger::init();

        // Set up the test host.
        let mut host = make_test_host(vec!["A".into(), "B".into()], end_time);

        // Call the contract function.
        let res = vote(&ctx, &mut host, &mut logger);

        // Check that error is thrown because the voting index is out of range.
        claim_eq!(
            res,
            Err(VotingError::InvalidVoteIndex),
            "Should throw error because voting index is invalid"
        );
    }

    #[concordium_test]
    fn test_vote_with_valid_index() {
        // Set up the context.
        let end_time = Timestamp::from_timestamp_millis(100);
        let current_time = Timestamp::from_timestamp_millis(0);
        let mut ctx = TestReceiveContext::empty();
        ctx.set_metadata_slot_time(current_time);

        // Set up logger.
        let mut logger = TestLogger::init();

        // Vote once.

        // Set up the parameter.
        let vote_parameter = to_bytes(&0);
        ctx.set_parameter(&vote_parameter);
        // Set up the sender.
        ctx.set_sender(ADDR_ACC_0);
        // Set up the test host.
        let mut host = make_test_host(vec!["A".into(), "B".into()], end_time);
        // Call the contract function.
        let result = vote(&ctx, &mut host, &mut logger);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");
        // Check the ballots (ACCOUNT_0 voted for voting option index 0).
        let ballots = host.state().ballots.iter().map(|(a, b)| (*a, *b)).collect::<Vec<_>>();
        let votes_count_0 = host.state().tally.get(&0).unwrap();
        let votes_count_1 = host.state().tally.get(&1);
        claim_eq!(*votes_count_0, 1, "Expect: one vote for option 0");
        claim!(votes_count_1.is_none(), "Expect: no votes for option 1");
        claim_eq!(vec![(ACC_0, 0)], ballots, "Expect: ACCOUNT_0 voted for voting option index 0");

        // Change vote.

        // Set up the parameter.
        let vote_parameter = to_bytes(&1);
        ctx.set_parameter(&vote_parameter);
        // Call the contract function.
        let result = vote(&ctx, &mut host, &mut logger);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");
        // Check the ballots (ACCOUNT_0 changed its voting option index to 1).
        let ballots = host.state().ballots.iter().map(|(a, b)| (*a, *b)).collect::<Vec<_>>();
        let votes_count_0 = host.state().tally.get(&0).unwrap();
        let votes_count_1 = host.state().tally.get(&1).unwrap();
        claim_eq!(*votes_count_0, 0, "Expect: no votes for option 0");
        claim_eq!(*votes_count_1, 1, "Expect: one vote for option 1");
        claim_eq!(
            vec![(ACC_0, 1)],
            ballots,
            "Expect: ACCOUNT_0 changed its voting option index to 1"
        );

        // Another vote, by another account.

        // Set up the parameter.
        let vote_parameter = to_bytes(&0);
        ctx.set_parameter(&vote_parameter);
        // Set up the sender.
        ctx.set_sender(ADDR_ACC_1);
        // Call the contract function.
        let result = vote(&ctx, &mut host, &mut logger);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");
        // Check the ballots (ACCOUNT_0 voted for voting option index 1 and ACCOUNT_1
        // voted for voting option index 0).
        let ballots = host.state().ballots.iter().map(|(a, b)| (*a, *b)).collect::<Vec<_>>();
        let votes_count_0 = host.state().tally.get(&0).unwrap();
        let votes_count_1 = host.state().tally.get(&1).unwrap();
        claim_eq!(*votes_count_0, 1, "Expect: one vote for option 0");
        claim_eq!(*votes_count_1, 1, "Expect: one vote for option 1");
        claim_eq!(
            vec![(ACC_0, 1), (ACC_1, 0)],
            ballots,
            "Expect: ACCOUNT_0 voted for voting option index 1 and ACCOUNT_1 voted for voting \
             option index 0"
        );

        // Vote again, using the same index as before.

        // Set up the parameter.
        let vote_parameter = to_bytes(&1);
        ctx.set_parameter(&vote_parameter);
        ctx.set_sender(ADDR_ACC_0);
        // Call the contract function.
        let result = vote(&ctx, &mut host, &mut logger);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");
        // Check the ballots (ACCOUNT_0 still voted for voting option index 1 and
        // ACCOUNT_1 still voted for voting option index 0).
        let ballots = host.state().ballots.iter().map(|(a, b)| (*a, *b)).collect::<Vec<_>>();
        let votes_count_0 = host.state().tally.get(&0).unwrap();
        let votes_count_1 = host.state().tally.get(&1).unwrap();
        claim_eq!(*votes_count_0, 1, "Expect: one vote for option 0");
        claim_eq!(*votes_count_1, 1, "Expect: one vote for option 1");
        claim_eq!(
            vec![(ACC_0, 1), (ACC_1, 0)],
            ballots,
            "ACCOUNT_0 still voted for voting option index 1 and ACCOUNT_1 still voted for voting \
             option index 0"
        );
    }
}
