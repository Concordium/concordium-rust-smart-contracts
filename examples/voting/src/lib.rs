//! A voting smart contract example.
//!
//! # Description
//! A contract that allows for conducting an election with several voting
//! options. A deadline is set when the election is initialized. Only
//! accounts are eligible to vote. Each account can change its
//! selected voting option as often as it desires until the deadline is
//! reached. No voting will be possible after the deadline.
//!
//! # Operations
//! The contract allows for
//!  - Initializing the election (`init` function).
//!  - Viewing general information about the election (`view` function).
//!  - Voting for one of the voting options (`vote` function).
//!  - Tallying votes for a requested voting option (`getNumberOfVotes`
//!    function).

#![cfg_attr(not(feature = "std"), no_std)]

use concordium_std::*;

/// Configuration for a single election.
#[derive(Serialize, SchemaType, Debug, PartialEq, Eq)]
pub struct ElectionConfig {
    /// The description of the election.
    pub description: String,
    /// All the voting options.
    pub options: Vec<String>,
    /// The last timestamp at which an account can vote.
    /// An election is open from the point in time that the smart contract is
    /// initialized until the deadline.
    pub deadline: Timestamp,
}

/// The smart contract state.
#[derive(Serialize, SchemaType)]
struct State {
    /// The configuration of the election.
    config: ElectionConfig,
    /// A map from voters to options, specifying who has voted for what.
    ballots: HashMap<AccountAddress, String>,
    /// A map from vote options to a vote count, specifying how many votes each
    /// option has.
    ///
    /// Note the data duplication here! The tally can of course always be
    /// determined by examining the ballots field. This requires looping
    /// over all ballots, counting how many votes exist for a specific option.
    /// However, such a loop would be practically unbounded, as it is only
    /// limited by the number of votes. Such a loop could exhaust the energy
    /// budget of the smart contract functions, potentially making the smart
    /// contract unusable and vulnerable to a kind of DDoS attack.
    ///
    /// Thus, we favor duplicating the data in another hashmap, where the vote
    /// count can be retrieved and updated in constant time.
    tally: HashMap<String, u32>,
}

/// The different errors that the `vote` function can produce.
#[derive(Reject, Serialize, PartialEq, Eq, Debug, SchemaType)]
pub enum VotingError {
    /// Raised when parsing the input parameter failed.
    #[from(ParseError)]
    ParsingFailed,
    /// Raised when the log is full.
    LogFull,
    /// Raised when the log is malformed.
    LogMalformed,
    /// Raised when the vote is placed after the election has ended.
    VotingFinished,
    /// Raised when voting for an option that does not exist.
    InvalidVote,
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

/// A vote event. The event is logged when a new (or replacement) vote is cast
/// by an account.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct VoteEvent {
    /// The account that casts the vote.
    pub voter: AccountAddress,
    /// The voting option that the account is voting for.
    pub option: String,
}

// Contract functions

/// Initialize the contract instance and start the election.
/// A description, the vector of all voting options, and a `deadline`
/// have to be provided.
///
/// Note: There is a limit to the size of the function input parameter (65535
/// Bytes), thus the number of voting options and the length of voting options
/// has a limit. Read more here: <https://developer.concordium.software/en/mainnet/smart-contracts/general/contract-instances.html#limits>
#[init(contract = "voting", parameter = "ElectionConfig", event = "VoteEvent")]
fn init(ctx: &InitContext, _state_builder: &mut StateBuilder) -> InitResult<State> {
    // Parse the parameter.
    let config: ElectionConfig = ctx.parameter_cursor().get()?;

    // Set the state.
    Ok(State {
        config,
        ballots: HashMap::default(),
        tally: HashMap::default(),
    })
}

/// Enables accounts to vote for a specific voting option. Each account can
/// change its selected voting option with this function as often as it desires
/// until the `deadline` is reached.
///
/// A valid vote produces an `VoteEvent` event.
/// This is also the case if the account recasts its vote for another, or even
/// the same, option. By tracking the events produced, one can reconstruct the
/// current state of the election.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - A contract tries to vote.
/// - It is past the `deadline`.
#[receive(
    contract = "voting",
    name = "vote",
    mutable,
    enable_logger,
    parameter = "String",
    error = "VotingError"
)]
fn vote(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> Result<(), VotingError> {
    // Check that the election hasn't finished yet.
    ensure!(
        ctx.metadata().slot_time() <= host.state().config.deadline,
        VotingError::VotingFinished
    );

    // Ensure that the sender is an account.
    let acc = match ctx.sender() {
        Address::Account(acc) => acc,
        Address::Contract(_) => return Err(VotingError::ContractVoter),
    };

    // Parse the option.
    let vote_option: String = ctx.parameter_cursor().get()?;

    // Check that the vote option is valid (exists).
    ensure!(
        host.state().config.options.contains(&vote_option),
        VotingError::InvalidVote
    );

    let state_mut = host.state_mut();

    // Insert or replace the vote for the account.
    state_mut
        .ballots
        .entry(acc)
        .and_modify(|old_vote_option| {
            // The account has already voted previously - we should subtract one vote from
            // the tally for that option. See doc comment on the tally field for
            // why it is done this way.
            *state_mut.tally.get_mut(old_vote_option).unwrap() -= 1;

            old_vote_option.clone_from(&vote_option);
        })
        .or_insert(vote_option.clone());

    // Now that the account has voted, we should increment the vote count for their
    // new vote choice. See doc comment on the tally field for why it is done
    // this way.
    *state_mut.tally.entry(vote_option.clone()).or_default() += 1;

    // Log event for the vote.
    logger.log(&VoteEvent {
        voter: acc,
        option: vote_option,
    })?;

    Ok(())
}

/// Get the number of votes for a specific voting option.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "voting",
    name = "getNumberOfVotes",
    parameter = "String",
    return_value = "u32"
)]
fn get_votes(ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<u32> {
    // Parse the vote option.
    let vote_option: String = ctx.parameter_cursor().get()?;

    // Get the number of votes for this option from the tally map.
    // See doc comment on the tally field for why it is done this way.
    Ok(host
        .state()
        .tally
        .get(&vote_option)
        .copied()
        .unwrap_or_default())
}

/// Get the election information.
#[receive(contract = "voting", name = "view", return_value = "ElectionConfig")]
fn view(_ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<ElectionConfig> {
    // Get information from the state.
    let description = host.state().config.description.clone();
    let options = host.state().config.options.clone();
    let deadline = host.state().config.deadline;

    // Return the election information.
    Ok(ElectionConfig {
        description,
        deadline,
        options,
    })
}
