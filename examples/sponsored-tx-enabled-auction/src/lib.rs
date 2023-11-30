//! # Implementation of an auction smart contract
//!
//! The contract is initialized with a cis2 token contract.
//! Any `token_id` from this cis2 token contract can be used as a payment
//! token when auctioning an item within this contract.
//!
//! To initiate a new auction, any account can call the `addItem` entry point.
//! The account initiating the auction (referred to as the creator) is required
//! to specify the start time, end time, minimum bid, and the `token_id`
//! associated with the item. At this stage, the item/auction is assigned the
//! next consecutive index for future reference.
//!
//! Any account can bid for an item.
//! The `bid` entry point in this contract is not meant to be invoked directly
//! but rather through the `onCIS2Receive` hook mechanism in the cis2 token
//! contract. The `bid` entry point can be invoked via a sponsored transaction
//! mechanism (`permit` entry point) in case it is implemented in the cis2 token
//! contract. The bidding flow starts with an account invoking either the
//! `transfer` or the `permit` entry point in the cis2 token contract and
//! including the `item_index` in the `additionalData` section of the input
//! parameter. The `transfer` or the `permit` entry point will send some token
//! amounts to this contract from the bidder. If the token amount exceeds the
//! current highest bid, the bid is accepted and the previous highest bidder is
//! refunded its token investment.
//!
//! The smart contract keeps track of the current highest bidder as well as
//! the token amount of the highest bid. The token balances of the smart
//! contract represent the sums of all highest bids from the items (that haven't
//! been finalized). When a new highest bid is accepted by the smart
//! contract, the smart contract refunds the old highest bidder.
//!
//! Bids have to be placed before the auction ends. The participant with the
//! highest bid (the last accepted bidder) wins the auction.
//!
//! After the auction ends for a specific item, any account can finalize the
//! auction. The creator of that auction receives the highest bid when the
//! auction is finalized and the item is marked as sold to the highest bidder.
//! This can be done only once.
#![cfg_attr(not(feature = "std"), no_std)]

use concordium_cis2::{Cis2Client, *};
use concordium_std::*;

/// Contract token ID type. It has to be the `ContractTokenId` from the cis2
/// token contract.
pub type ContractTokenId = TokenIdU8;

/// Contract token amount. It has to be the `ContractTokenAmount` from the cis2
/// token contract.
pub type ContractTokenAmount = TokenAmountU64;

/// TransferParameter type that has a specific `ContractTokenId` and
/// `ContractTokenAmount` set.
pub type TransferParameter = TransferParams<ContractTokenId, ContractTokenAmount>;

/// The state of the auction.
#[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd, Clone)]
pub enum AuctionState {
    /// The auction is either
    /// - still accepting bids or
    /// - not accepting bids because it's past the auction end, but nobody has
    ///   finalized the auction yet.
    NotSoldYet,
    /// The auction has been finalized and the item has been sold to the
    /// winning `AccountAddress`.
    Sold(AccountAddress),
}

/// The state of an item up for auction.
/// This state can be viewed by querying the node with the command
/// `concordium-client contract invoke` using the `view_item_state` function as
/// entry point.
#[derive(Debug, Serialize, SchemaType, Clone, PartialEq, Eq)]
pub struct ItemState {
    /// State of the auction.
    pub auction_state:  AuctionState,
    /// The highest bidder so far. The variant `None` represents
    /// that no bidder has taken part in the auction yet.
    pub highest_bidder: Option<AccountAddress>,
    /// The item name to be sold.
    pub name:           String,
    /// The time when the auction ends.
    pub end:            Timestamp,
    /// The time when the auction starts.
    pub start:          Timestamp,
    /// In case `highest_bidder==None`, the minimum bid as set by the creator.
    /// In case `highest_bidder==Some(AccountAddress)`, the highest bid that a
    /// bidder has bid so far.
    pub highest_bid:    TokenAmountU64,
    /// The `token_id` from the cis2 token contract used as payment token.
    pub token_id:       TokenIdU8,
    /// The account address that created the auction for this item.
    pub creator:        AccountAddress,
}

/// The state of the smart contract.
/// This state can be viewed by querying the node with the command
/// `concordium-client contract invoke` using the `view` function as entry
/// point.
#[derive(Serial, DeserialWithState, Debug)]
#[concordium(state_parameter = "S")]
pub struct State<S = StateApi> {
    /// A mapping including all items that have been added to this contract.
    items:         StateMap<u16, ItemState, S>,
    /// The cis2 token contract. Its tokens can be used to bid for items in this
    /// contract.
    cis2_contract: ContractAddress,
    /// A counter that is sequentially increased whenever a new item is added to
    /// the contract.
    counter:       u16,
}

/// The return_value for the entry point `view` which returns the contract
/// state.
#[derive(Serialize, SchemaType, Debug, Eq, PartialEq)]
pub struct ReturnParamView {
    /// A vector including all items that have been added to this contract.
    pub item_states:   Vec<(u16, ItemState)>,
    /// The cis2 token contract. Its tokens can be used to bid for items in this
    /// contract.
    pub cis2_contract: ContractAddress,
    /// A counter that is sequentially increased whenever a new item is added to
    /// the contract.
    pub counter:       u16,
}

/// The parameter for the entry point `addItem` that adds a new item to this
/// contract.
#[derive(Serialize, SchemaType)]
pub struct AddItemParameter {
    /// The item name to be sold.
    pub name:        String,
    /// The time when the auction ends.
    pub end:         Timestamp,
    /// The time when the auction starts.
    pub start:       Timestamp,
    // The minimum bid that the first bidder has to overbid.
    pub minimum_bid: TokenAmountU64,
    // The `token_id` from the cis2 token contract that the item should be sold for.
    pub token_id:    TokenIdU8,
}

/// The `additionData` that has to be passed to the `bid` entry point.
#[derive(Debug, Deserial, Serial, Clone, SchemaType)]
#[concordium(transparent)]
pub struct AdditionalDataIndex {
    /// The index of the item.
    pub item_index: u16,
}

/// Errors of this contract.
#[derive(Debug, PartialEq, Eq, Clone, Reject, Serialize, SchemaType)]
pub enum Error {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams, //-1
    // Raised when adding an item; The start time needs to be strictly smaller than the end time.
    StartEndTimeError, //-2
    // Raised when adding an item; The end time needs to be in the future.
    EndTimeError, //-3
    /// Raised when a contract tries to bid; Only accounts
    /// are allowed to bid.
    OnlyAccount, //-4
    /// Raised when the new bid amount is not greater than the current highest
    /// bid.
    BidNotGreaterCurrentBid, //-5
    /// Raised when the bid is placed after the auction end time passed.
    BidTooLate, //-6
    /// Raised when the bid is placed after the auction has been finalized.
    AuctionAlreadyFinalized, //-7
    /// Raised when the item index cannot be found in the contract.
    NoItem, //-8
    /// Raised when finalizing an auction before the auction end time passed.
    AuctionStillActive, //-9
    /// Raised when someone else than the cis2 token contract invokes the `bid`
    /// entry point.
    NotTokenContract, //-10
    /// Raised when payment is attempted with a different `token_id` than
    /// specified for an item.
    WrongTokenID, //-11
    /// Raised when the invocation of the cis2 token contract fails.
    InvokeContractError, //-12
    /// Raised when the parsing of the result from the cis2 token contract
    /// fails.
    ParseResult, //-13
    /// Raised when the response of the cis2 token contract is invalid.
    InvalidResponse, //-14
    /// Raised when the amount of cis2 tokens that was to be transferred is not
    /// available to the sender.
    AmountTooLarge, //-15
    /// Raised when the owner account of the cis 2 token contract that is being
    /// invoked does not exist. This variant should in principle not happen,
    /// but is here for completeness.
    MissingAccount, //-16
    /// Raised when the cis2 token contract that is to be invoked does not
    /// exist.
    MissingContract, //-17
    /// Raised when the cis2 token contract to be invoked exists, but the entry
    /// point that was named does not.
    MissingEntrypoint, //-18
    // Raised when the sending of a message to the V0 contract failed.
    MessageFailed, //-19
    // Raised when the cis2 token contract called rejected with the given reason.
    LogicReject, //-20
    // Raised when the cis2 token contract execution triggered a runtime error.
    Trap, //-21
}

pub type ContractResult<A> = Result<A, Error>;

/// Mapping CallContractError<ExternCallResponse> to Error
impl From<CallContractError<ExternCallResponse>> for Error {
    fn from(e: CallContractError<ExternCallResponse>) -> Self {
        match e {
            CallContractError::AmountTooLarge => Self::AmountTooLarge,
            CallContractError::MissingAccount => Self::MissingAccount,
            CallContractError::MissingContract => Self::MissingContract,
            CallContractError::MissingEntrypoint => Self::MissingEntrypoint,
            CallContractError::MessageFailed => Self::MessageFailed,
            CallContractError::LogicReject {
                reason: _,
                return_value: _,
            } => Self::LogicReject,
            CallContractError::Trap => Self::Trap,
        }
    }
}

/// Mapping Cis2ClientError<Error> to Error
impl From<Cis2ClientError<Error>> for Error {
    fn from(e: Cis2ClientError<Error>) -> Self {
        match e {
            Cis2ClientError::InvokeContractError(_) => Self::InvokeContractError,
            Cis2ClientError::ParseResult => Self::ParseResult,
            Cis2ClientError::InvalidResponse => Self::InvalidResponse,
        }
    }
}

/// Init entry point that creates a new auction contract.
#[init(contract = "sponsored_tx_enabled_auction", parameter = "ContractAddress")]
fn auction_init(ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<State> {
    // Getting input parameters.
    let contract: ContractAddress = ctx.parameter_cursor().get()?;
    // Creating `State`.
    let state = State {
        items:         state_builder.new_map(),
        cis2_contract: contract,
        counter:       0,
    };
    Ok(state)
}

/// AddItem entry point to add an item to this contract. To initiate a new
/// auction, any account can call this entry point. The account initiating the
/// auction (referred to as the creator) is required to specify the start time,
/// end time, minimum bid, and the `token_id` associated with the item. At this
/// stage, the item/auction is assigned the next consecutive index for future
/// reference.
#[receive(
    contract = "sponsored_tx_enabled_auction",
    name = "addItem",
    parameter = "AddItemParameter",
    mutable
)]
fn add_item(ctx: &ReceiveContext, host: &mut Host<State>) -> ContractResult<()> {
    // Ensure that only accounts can add an item.
    let sender_address = match ctx.sender() {
        Address::Contract(_) => bail!(Error::OnlyAccount),
        Address::Account(account_address) => account_address,
    };

    // Getting input parameters.
    let item: AddItemParameter = ctx.parameter_cursor().get()?;

    // Ensure start < end.
    ensure!(item.start < item.end, Error::StartEndTimeError);

    let block_time = ctx.metadata().block_time();
    // Ensure the auction can run.
    ensure!(block_time <= item.end, Error::EndTimeError);

    // Assign an index to the item/auction.
    let counter = host.state_mut().counter;
    host.state_mut().counter = counter + 1;

    // Insert the item into the state.
    host.state_mut().items.insert(counter, ItemState {
        auction_state:  AuctionState::NotSoldYet,
        highest_bidder: None,
        name:           item.name,
        end:            item.end,
        start:          item.start,
        highest_bid:    item.minimum_bid,
        creator:        sender_address,
        token_id:       item.token_id,
    });

    Ok(())
}

/// The `bid` entry point in this contract is not meant to be invoked directly
/// but rather through the `onCIS2Receive` hook mechanism in the cis2 token
/// contract. Any account can bid for an item. The `bid` entry point can be
/// invoked via a sponsored transaction mechanism (`permit` entry point) in case
/// it is implemented in the cis2 token contract. The bidding flow starts with
/// an account invoking either the `transfer` or the `permit` entry point in the
/// cis2 token contract and including the `item_index` in the `additionalData`
/// section of the input parameter. The `transfer` or the `permit` entry point
/// will send some token amounts to this contract from the bidder. If the token
/// amount exceeds the current highest bid, the bid is accepted and the previous
/// highest bidder is refunded its token investment.
#[receive(
    contract = "sponsored_tx_enabled_auction",
    name = "bid",
    mutable,
    parameter = "OnReceivingCis2DataParams<ContractTokenId, ContractTokenAmount, \
                 AdditionalDataIndex>",
    error = "Error"
)]
fn auction_bid(ctx: &ReceiveContext, host: &mut Host<State>) -> ContractResult<()> {
    // Ensure the sender is the cis2 token contract.
    if !ctx.sender().matches_contract(&host.state().cis2_contract) {
        bail!(Error::NotTokenContract);
    }

    let contract = host.state().cis2_contract;

    // Getting input parameters.
    let params: OnReceivingCis2DataParams<
        ContractTokenId,
        ContractTokenAmount,
        AdditionalDataIndex,
    > = ctx.parameter_cursor().get()?;

    // Ensure that only accounts can bid for an item.
    let bidder_address = match params.from {
        Address::Contract(_) => bail!(Error::OnlyAccount),
        Address::Account(account_address) => account_address,
    };

    let mut item =
        host.state_mut().items.entry(params.data.item_index).occupied_or(Error::NoItem)?;

    // Ensure the token_id matches.
    ensure_eq!(item.token_id, params.token_id, Error::WrongTokenID);

    // Ensure the auction has not been finalized yet.
    ensure_eq!(item.auction_state, AuctionState::NotSoldYet, Error::AuctionAlreadyFinalized);

    let block_time = ctx.metadata().block_time();
    // Ensure the auction has not ended yet.
    ensure!(block_time <= item.end, Error::BidTooLate);

    // Ensure that the new bid exceeds the highest bid so far.
    let old_highest_bid = item.highest_bid;
    ensure!(params.amount > old_highest_bid, Error::BidNotGreaterCurrentBid);

    // Set the new highest_bid.
    item.highest_bid = params.amount;

    if let Some(account_address) = item.highest_bidder.replace(bidder_address) {
        let client = Cis2Client::new(contract);

        let read_item = item.clone();

        drop(item);

        // Refunding old highest bidder.
        // This transfer (given enough NRG of course) always succeeds because
        // the `account_address` exists since it was recorded when it
        // placed a bid. If an `account_address` exists, and the
        // contract has the funds then the transfer will always succeed.
        // Please consider using a pull-over-push pattern when expanding this
        // smart contract to allow smart contract instances to
        // participate in the auction as well. https://consensys.github.io/smart-contract-best-practices/attacks/denial-of-service/
        client.transfer::<State, ContractTokenId, ContractTokenAmount, Error>(host, Transfer {
            amount:   old_highest_bid,
            from:     concordium_std::Address::Contract(ctx.self_address()),
            to:       concordium_cis2::Receiver::Account(account_address),
            token_id: read_item.token_id,
            data:     AdditionalData::empty(),
        })?;
    }

    Ok(())
}

/// The `finalize` entry point can be called by anyone. It sends the highest bid
/// in tokens to the creator of the auction if the item is past its auction end
/// time.
#[receive(
    contract = "sponsored_tx_enabled_auction",
    name = "finalize",
    parameter = "u16",
    mutable,
    error = "Error"
)]
fn auction_finalize(ctx: &ReceiveContext, host: &mut Host<State>) -> ContractResult<()> {
    // Getting input parameter.
    let item_index: u16 = ctx.parameter_cursor().get()?;

    let contract = host.state().cis2_contract;

    // Get the item from state.
    let mut item = host.state_mut().items.entry(item_index).occupied_or(Error::NoItem)?;

    // Ensure the auction has not been finalized yet.
    ensure_eq!(item.auction_state, AuctionState::NotSoldYet, Error::AuctionAlreadyFinalized);

    let block_time = ctx.metadata().block_time();
    // Ensure the auction has ended already.
    ensure!(block_time > item.end, Error::AuctionStillActive);

    if let Some(account_address) = item.highest_bidder {
        // Marking the highest bidder (the last accepted bidder) as winner of the
        // auction.
        item.auction_state = AuctionState::Sold(account_address);

        let client = Cis2Client::new(contract);

        let read_item = item.clone();

        drop(item);

        // Sending the highest bid in tokens to the creator of the auction.
        // This transfer (given enough NRG of course) always succeeds because
        // the `creator` exists since it was recorded when it
        // added the item. If an `account_address` exists, and the
        // contract has the funds then the transfer will always succeed.
        // Please consider using a pull-over-push pattern when expanding this
        // smart contract to allow smart contract instances to
        // participate in the auction as well. https://consensys.github.io/smart-contract-best-practices/attacks/denial-of-service/
        client.transfer::<State, ContractTokenId, ContractTokenAmount, Error>(host, Transfer {
            amount:   read_item.highest_bid,
            from:     concordium_std::Address::Contract(ctx.self_address()),
            to:       concordium_cis2::Receiver::Account(read_item.creator),
            token_id: read_item.token_id,
            data:     AdditionalData::empty(),
        })?;
    }

    Ok(())
}

/// View function that returns the content of the state.
#[receive(
    contract = "sponsored_tx_enabled_auction",
    name = "view",
    return_value = "ReturnParamView"
)]
fn view(_ctx: &ReceiveContext, host: &Host<State>) -> ContractResult<ReturnParamView> {
    let state = host.state();

    let inner_state = state.items.iter().map(|x| (*x.0, x.1.clone())).collect();

    Ok(ReturnParamView {
        item_states:   inner_state,
        cis2_contract: host.state().cis2_contract,
        counter:       host.state().counter,
    })
}

/// ViewItemState function that returns the state of a specific item.
#[receive(
    contract = "sponsored_tx_enabled_auction",
    name = "viewItemState",
    return_value = "ItemState",
    parameter = "u16"
)]
fn view_item_state(ctx: &ReceiveContext, host: &Host<State>) -> ContractResult<ItemState> {
    // Getting input parameter.
    let item_index: u16 = ctx.parameter_cursor().get()?;
    let item = host.state().items.get(&item_index).map(|x| x.to_owned()).ok_or(Error::NoItem)?;
    Ok(item)
}
