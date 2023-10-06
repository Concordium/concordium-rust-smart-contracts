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
pub type VotingOption = String;
/// The voting options are stored in a vector. The vector index is used to refer
/// to a specific voting option.
pub type VoteIndex = u32;
/// Number of votes.
pub type VoteCount = u32;

/// The parameter type for the contract function `vote`.
/// Takes a `vote_index` that the account wants to vote for.
#[derive(Serialize, SchemaType, Debug, PartialEq, Eq)]
pub struct VoteParameter {
    /// Voting option index to vote for.
    pub vote_index: VoteIndex,
}

/// The parameter type for the contract function `init`.
/// Takes a description, the voting options, and the `end_time` to start the
/// election.
#[derive(Serialize, SchemaType, Debug, PartialEq, Eq)]
pub struct InitParameter {
    /// The description of the election.
    pub description: String,
    /// A vector of all voting options.
    pub options:     Vec<VotingOption>,
    /// The last timestamp that an account can vote.
    /// The election is open from the point in time that this smart contract is
    /// initialized until the `end_time`.
    pub end_time:    Timestamp,
}

/// The `return_value` type of the contract function `view`.
/// Returns a description, the `end_time`, the voting options as a vector, and
/// the number of voting options of the current election.
#[derive(Serialize, SchemaType, Debug, PartialEq, Eq)]
pub struct VotingView {
    /// The description of the election.
    pub description: String,
    /// The last timestamp that an account can vote.
    /// The election is open from the point in time that this smart contract is
    /// initialized until the `end_time`.
    pub end_time:    Timestamp,
    /// A vector of all voting options.
    pub options:     Vec<VotingOption>,
    /// The number of voting options.
    pub num_options: u32,
}

/// The contract state
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S: HasStateApi = StateApi> {
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
#[derive(Reject, Serialize, PartialEq, Eq, Debug, SchemaType)]
pub enum VotingError {
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
pub type VotingResult<T> = Result<T, VotingError>;

/// The event is logged when a new (or replacement) vote is cast by an account.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct VoteEvent {
    /// The account that casts the vote.
    pub voter:      AccountAddress,
    /// The index of the voting option that the account is voting for.
    pub vote_index: VoteIndex,
}

/// The event logged by this smart contract.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
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
fn init(ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<State> {
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
/// A valid vote produces an `Event::Vote` event.
/// This is also the case if the account recasts its vote for another, or even
/// the same, option. By tracking the events produced, one can reconstruct the
/// current state of the election.
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
fn vote(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
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
fn get_votes(ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<VoteCount> {
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
fn view(_ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<VotingView> {
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
