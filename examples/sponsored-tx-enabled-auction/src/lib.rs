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

use concordium_std::*;

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
    pub highest_bid:    u64,
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
    pub minimum_bid: u64,
}

/// `bid` function errors
#[derive(Debug, PartialEq, Eq, Clone, Reject, Serialize, SchemaType)]
pub enum Error {
    /// Raised when a contract tries to bid; Only accounts
    /// are allowed to bid.
    OnlyAccount,
    /// Raised when new bid amount is lower than current highest bid.
    BidBelowCurrentBid,
    /// Raised when bid is placed after auction end time passed.
    BidTooLate,
    /// Raised when bid is placed after auction has been finalized.
    AuctionAlreadyFinalized,
    ///
    NoItem,
    /// Raised when finalizing an auction before auction end time passed
    AuctionStillActive,
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

    host.state_mut().items.insert(counter, ItemState {
        auction_state:  AuctionState::NotSoldYet,
        highest_bidder: None,

        name:        item.name,
        end:         item.end,
        start:       item.start,
        highest_bid: item.minimum_bid,
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

// /// Receive function for accounts to place a bid in the auction
// #[receive(
//     contract = "sponsored_tx_enabled_auction",
//     name = "bid",
//     payable,
//     mutable,
//     error = "BidError"
// )]
// fn auction_bid(
//     ctx: &ReceiveContext,ItemState
//     host: &mut Host<State>,
//     amount: Amount,
// ) -> Result<(), BidError> {
//     let state = host.state();
//     // Ensure the auction has not been finalized yet
//     ensure_eq!(state.auction_state, AuctionState::NotSoldYet,
// BidError::AuctionAlreadyFinalized);

//     let slot_time = ctx.metadata().slot_time();
//     // Ensure the auction has not ended yet
//     ensure!(slot_time <= state.end, BidError::BidTooLate);

//     // Ensure that only accounts can place a bid
//     let sender_address = match ctx.sender() {
//         Address::Contract(_) => bail!(BidError::OnlyAccount),
//         Address::Account(account_address) => account_address,
//     };

//     // Balance of the contract
//     let balance = host.self_balance();

//     // Balance of the contract before the call
//     let previous_balance = balance - amount;

//     // Ensure that the new bid exceeds the highest bid so far
//     ensure!(amount > previous_balance, BidError::BidBelowCurrentBid);

//     // Calculate the difference between the previous bid and the new bid in
// CCD.     let amount_difference = amount - previous_balance;
//     // Get the current exchange rate used by the chain
//     let exchange_rates = host.exchange_rates();
//     // Convert the CCD difference to EUR
//     let euro_cent_difference =
// exchange_rates.convert_amount_to_euro_cent(amount_difference);     // Ensure
// that the bid is at least the `minimum_raise` more than the previous     // bid
//     ensure!(euro_cent_difference >= state.minimum_raise,
// BidError::BidBelowMinimumRaise);

//     if let Some(account_address) =
// host.state_mut().highest_bidder.replace(sender_address) {         //
// Refunding old highest bidder;         // This transfer (given enough NRG of
// course) always succeeds because the         // `account_address` exists since
// it was recorded when it placed a bid.         // If an `account_address`
// exists, and the contract has the funds then the         // transfer will
// always succeed.         // Please consider using a pull-over-push pattern
// when expanding this smart         // contract to allow smart contract
// instances to participate in the auction as         // well. https://consensys.github.io/smart-contract-best-practices/attacks/denial-of-service/
//         host.invoke_transfer(&account_address,
// previous_balance).unwrap_abort();     }
//     Ok(())
// }

// /// Receive function used to finalize the auction. It sends the highest bid
// (the /// current balance of this smart contract) to the owner of the smart
// contract /// instance.
// #[receive(
//     contract = "sponsored_tx_enabled_auction",
//     name = "finalize",
//     mutable,
//     error = "FinalizeError"
// )]
// fn auction_finalize(ctx: &ReceiveContext, host: &mut Host<State>) ->
// Result<(), FinalizeError> {     let state = host.state();
//     // Ensure the auction has not been finalized yet
//     ensure_eq!(
//         state.auction_state,
//         AuctionState::NotSoldYet,
//         FinalizeError::AuctionAlreadyFinalized
//     );

//     let slot_time = ctx.metadata().slot_time();
//     // Ensure the auction has ended already
//     ensure!(slot_time > state.end, FinalizeError::AuctionStillActive);

//     if let Some(account_address) = state.highest_bidder {
//         // Marking the highest bid (the last bidder) as winner of the auction
//         host.state_mut().auction_state = AuctionState::Sold(account_address);
//         let owner = ctx.owner();
//         let balance = host.self_balance();
//         // Sending the highest bid (the balance of this contract) to the
// owner of the         // smart contract instance;
//         // This transfer (given enough NRG of course) always succeeds because
// the         // `owner` exists since it deployed the smart contract instance.
//         // If an account exists, and the contract has the funds then the
//         // transfer will always succeed.
//         host.invoke_transfer(&owner, balance).unwrap_abort();
//     }
//     Ok(())
// }
