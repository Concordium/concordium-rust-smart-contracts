//! # Implementation of an auction smart contract
//!
//! Accounts can invoke the bid function to participate in the auction.
//! An account has to send some CCD when invoking the bid function.
//! This CCD amount has to exceed the current highest bid by a minimum raise
//! to be accepted by the smart contract.
//!
//! The minimum raise is set when initializing and is defined in Euro cent.
//! The contract uses the current exchange rate used by the chain by the time of
//! the bid, to convert the bid into EUR.
//!
//! The smart contract keeps track of the current highest bidder as well as
//! the CCD amount of the highest bid. The CCD balance of the smart contract
//! represents the highest bid. When a new highest bid is accepted by the smart
//! contract, the smart contract refunds the old highest bidder.
//!
//! Bids have to be placed before the auction ends. The participant with the
//! highest bid (the last bidder) wins the auction.
//!
//! After the auction ends, any account can finalize the auction. The owner of
//! the smart contract instance receives the highest bid (the balance of this
//! contract) when the auction is finalized. This can be done only once.
//!
//! Terminology: `Accounts` are derived from a public/private key pair.
//! `Contract` instances are created by deploying a smart contract
//! module and initializing it.

#![cfg_attr(not(feature = "std"), no_std)]

use concordium_cis2::*;
use concordium_std::*;

/// Contract token ID type.
/// To save bytes we use a token ID type limited to a `u32`.
pub type ContractTokenId = TokenIdU32;

/// Contract token amount.
/// Since the tokens are non-fungible the total supply of any token will be at
/// most 1 and it is fine to use a small type for representing token amounts.
pub type ContractTokenAmount = TokenAmountU64;

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

/// The state of the smart contract.
/// This state can be viewed by querying the node with the command
/// `concordium-client contract invoke` using the `view` function as entrypoint.
#[derive(Debug, Serialize, SchemaType, Clone, PartialEq, Eq)]
pub struct ItemState {
    /// State of the auction
    pub auction_state:  AuctionState,
    /// The highest bidder so far; The variant `None` represents
    /// that no bidder has taken part in the auction yet.
    pub highest_bidder: Option<AccountAddress>,
    /// The item to be sold (to be displayed by the front-end)
    pub name:           String,
    /// Time when auction ends (to be displayed by the front-end)
    pub end:            Timestamp,
    pub start:          Timestamp,
    pub highest_bid:    TokenAmountU64,
    pub token_id:       TokenIdU32,
    pub creator:        AccountAddress,
}

/// The state of the smart contract.
/// This state can be viewed by querying the node with the command
/// `concordium-client contract invoke` using the `view` function as entrypoint.
// #[derive(Debug, Serialize, SchemaType, Clone)]
#[derive(Serial, DeserialWithState, Debug)]
#[concordium(state_parameter = "S")]
pub struct State<S = StateApi> {
    items:         StateMap<u16, ItemState, S>,
    cis2_contract: ContractAddress,
    counter:       u16,
}

#[derive(Serialize, SchemaType, Debug, Eq, PartialEq)]

pub struct ReturnParamView {
    pub item_states:   Vec<(u16, ItemState)>,
    pub cis2_contract: ContractAddress,
    pub counter:       u16,
}

/// Type of the parameter to the `init` function
#[derive(Serialize, SchemaType)]
pub struct AddItemParameter {
    /// The item to be sold (to be displayed by the front-end)
    pub name:        String,
    /// Time when auction ends (to be displayed by the front-end)
    pub end:         Timestamp,
    pub start:       Timestamp,
    pub minimum_bid: TokenAmountU64,
    pub token_id:    TokenIdU32,
}

/// `bid` function errors
#[derive(Debug, PartialEq, Eq, Clone, Reject, Serialize, SchemaType)]
pub enum Error {
    /// Raised when a contract tries to bid; Only accounts
    /// are allowed to bid.
    OnlyAccount, //-1
    /// Raised when new bid amount is lower than current highest bid.
    BidBelowCurrentBid, //-2
    /// Raised when bid is placed after auction end time passed.
    BidTooLate, //-3
    /// Raised when bid is placed after auction has been finalized.
    AuctionAlreadyFinalized, //-4
    ///
    NoItem, //-5
    /// Raised when finalizing an auction before auction end time passed
    AuctionStillActive, //-6
    ///
    NotTokenContract, //-7
    WrongTokenID, //-8
}

/// Init function that creates a new auction
#[init(contract = "sponsored_tx_enabled_auction", parameter = "ContractAddress")]
fn auction_init(ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<State> {
    // Getting input parameters
    let contract: ContractAddress = ctx.parameter_cursor().get()?;
    // Creating `State`
    let state = State {
        items:         state_builder.new_map(),
        cis2_contract: contract,
        counter:       0,
    };
    Ok(state)
}

/// ViewHighestBid function that returns the highest bid which is the balance of
/// the contract
#[receive(
    contract = "sponsored_tx_enabled_auction",
    name = "addItem",
    parameter = "AddItemParameter",
    mutable
)]
fn add_item(ctx: &ReceiveContext, host: &mut Host<State>) -> ReceiveResult<()> {
    // Getting input parameters
    let item: AddItemParameter = ctx.parameter_cursor().get()?;

    let counter = host.state_mut().counter;
    host.state_mut().counter = counter + 1;

    // Ensure that only accounts can add an item.
    let sender_address = match ctx.sender() {
        Address::Contract(_) => bail!(Error::OnlyAccount.into()),
        Address::Account(account_address) => account_address,
    };

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

/// View function that returns the content of the state
#[receive(
    contract = "sponsored_tx_enabled_auction",
    name = "view",
    return_value = "ReturnParamView"
)]
fn view(_ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<ReturnParamView> {
    let state = host.state();

    let mut inner_state = Vec::new();
    for (index, item_state) in state.items.iter() {
        inner_state.push((*index, item_state.clone()));
    }

    Ok(ReturnParamView {
        item_states:   inner_state,
        cis2_contract: host.state().cis2_contract,
        counter:       host.state().counter,
    })
}

/// ViewHighestBid function that returns the highest bid which is the balance of
/// the contract
#[receive(
    contract = "sponsored_tx_enabled_auction",
    name = "viewItemState",
    return_value = "ItemState",
    parameter = "u16"
)]
fn view_item_state(ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<ItemState> {
    // Getting input parameters
    let item_index: u16 = ctx.parameter_cursor().get()?;
    let item = host.state().items.get(&item_index).map(|x| x.clone()).ok_or(Error::NoItem)?;
    Ok(item)
}

#[derive(Debug, Serialize, SchemaType)]
pub struct TestOnReceivingCis2Params<T, A> {
    /// The ID of the token received.
    pub token_id: T,
    /// The amount of tokens received.
    pub amount:   A,
    /// The previous owner of the tokens.
    pub from:     Address,
    /// Some extra information which where sent as part of the transfer.
    pub data:     AdditionalDataItem,
}

/// Additional information to include with a transfer.
#[derive(Debug, Serialize, Clone, SchemaType)]
#[concordium(transparent)]
pub struct AdditionalDataItem(#[concordium(size_length = 2)] Vec<u8>);

#[derive(Debug, Deserial, Serial, Clone, SchemaType)]
pub struct AdditionalDataIndex {
    pub item_index: u16,
}

/// Receive function for accounts to place a bid in the auction
#[receive(
    contract = "sponsored_tx_enabled_auction",
    name = "bid",
    mutable,
    parameter = "TestOnReceivingCis2Params<ContractTokenId, ContractTokenAmount>",
    error = "Error"
)]
fn auction_bid(ctx: &ReceiveContext, host: &mut Host<State>) -> ReceiveResult<()> {
    // Parse the parameter.
    let params: TestOnReceivingCis2Params<ContractTokenId, ContractTokenAmount> =
        ctx.parameter_cursor().get()?;

    // Ensure the sender is the cis2_token_contract.
    if let Address::Contract(contract) = ctx.sender() {
        ensure_eq!(contract, host.state().cis2_contract, Error::NotTokenContract.into());
    } else {
        bail!(Error::NotTokenContract.into())
    };

    let additional_data_index: AdditionalDataIndex = from_bytes(&params.data.0)?;

    let cis2_contract = host.state().cis2_contract;

    let item =
        host.state_mut().items.get(&additional_data_index.item_index).ok_or(Error::NoItem)?;

    ensure_eq!(item.token_id, params.token_id, Error::WrongTokenID.into());

    // Ensure that only accounts can bid for an item.
    let bidder_address = match params.from {
        Address::Contract(_) => bail!(Error::OnlyAccount.into()),
        Address::Account(account_address) => account_address,
    };

    // Ensure the auction has not been finalized yet
    ensure_eq!(item.auction_state, AuctionState::NotSoldYet, Error::AuctionAlreadyFinalized.into());

    let slot_time = ctx.metadata().slot_time();
    // Ensure the auction has not ended yet
    ensure!(slot_time <= item.end, Error::BidTooLate.into());

    // Ensure that the new bid exceeds the highest bid so far
    ensure!(params.amount > item.highest_bid, Error::BidBelowCurrentBid.into());

    if let Some(account_address) = item.highest_bidder {
        // Refunding old highest bidder;
        // This transfer (given enough NRG of course) always succeeds because
        // the `account_address` exists since it was recorded when it
        // placed a bid. If an `account_address` exists, and the
        // contract has the funds then the transfer will always succeed.
        // Please consider using a pull-over-push pattern when expanding this
        // smart contract to allow smart contract instances to
        // participate in the auction as well. https://consensys.github.io/smart-contract-best-practices/attacks/denial-of-service/
        let parameter = TransferParameter {
            0: vec![Transfer {
                token_id: item.token_id,
                amount:   item.highest_bid,
                from:     concordium_std::Address::Contract(ctx.self_address()),
                to:       concordium_cis2::Receiver::Account(account_address),
                data:     AdditionalData::empty(),
            }],
        };

        host.invoke_contract(
            &cis2_contract,
            &parameter,
            EntrypointName::new_unchecked("transfer"),
            Amount::zero(),
        )?;
    }

    let mut item = host
        .state_mut()
        .items
        .entry(additional_data_index.item_index)
        .occupied_or(Error::NoItem)?;
    item.highest_bidder = Some(bidder_address);
    item.highest_bid = params.amount;

    Ok(())
}

/// Receive function used to finalize the auction. It sends the highest bid (the
/// current balance of this smart contract) to the owner of the smart contract
/// instance.
#[receive(
    contract = "sponsored_tx_enabled_auction",
    name = "finalize",
    parameter = "u16",
    mutable,
    error = "Error"
)]
fn auction_finalize(ctx: &ReceiveContext, host: &mut Host<State>) -> ReceiveResult<()> {
    // Getting input parameters
    let item_index: u16 = ctx.parameter_cursor().get()?;
    let cis2_contract = host.state().cis2_contract;

    let item = host.state_mut().items.get(&item_index).ok_or(Error::NoItem)?;

    // Ensure the auction has not been finalized yet
    ensure_eq!(item.auction_state, AuctionState::NotSoldYet, Error::AuctionAlreadyFinalized.into());

    let slot_time = ctx.metadata().slot_time();
    // Ensure the auction has ended already
    ensure!(slot_time > item.end, Error::AuctionStillActive.into());

    if let Some(account_address) = item.highest_bidder {
        // Marking the highest bid (the last bidder) as winner of the auction
        // item.auction_state = AuctionState::Sold(account_address);
        // let owner = ctx.owner();
        // let balance = host.self_balance();
        // // Sending the highest bid (the balance of this contract) to the owner of the
        // // smart contract instance;
        // // This transfer (given enough NRG of course) always succeeds because the
        // // If an account exists, and the contract has the funds then the
        // // transfer will always succeed.
        // host.invoke_transfer(&owner, balance).unwrap_abort();

        let parameter = TransferParameter {
            0: vec![Transfer {
                token_id: item.token_id,
                amount:   item.highest_bid,
                from:     concordium_std::Address::Contract(ctx.self_address()),
                to:       concordium_cis2::Receiver::Account(item.creator),
                data:     AdditionalData::empty(),
            }],
        };

        host.invoke_contract(
            &cis2_contract,
            &parameter,
            EntrypointName::new_unchecked("transfer"),
            Amount::zero(),
        )?;

        let mut item = host.state_mut().items.entry(item_index).occupied_or(Error::NoItem)?;
        item.auction_state = AuctionState::Sold(account_address);
    }

    Ok(())
}
