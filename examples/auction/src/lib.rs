use concordium_std::{collections::BTreeMap, *};
use core::fmt::Debug;

/// # Implementation of an auction smart contract
///
/// To bid, participants send GTU using the bid function.
/// The participant with the highest bid wins the auction.
/// Bids are to be placed before the auction end. After that, bids are refused.
/// Only bids that exceed the highest bid are accepted.
/// Bids are placed incrementally, i.e., an account's bid is considered
/// to be the **sum** of all bids.
///
/// Example: if Alice first bid 1 GTU and then bid 2 GTU, her total
/// bid is 3 GTU. The bidding will only go through if 3 GTU is higher than
/// the currently highest bid.
///
/// After the auction end, any account can finalize the auction.
/// The auction can be finalized only once.
/// When the auction is finalized, every participant except the
/// winner gets their money back.

/// The state in which an auction can be.
#[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd)]
pub enum AuctionState {
    /// The auction is either
    /// - still accepting bids or
    /// - not accepting bids because it's past the auction end, but nobody has
    ///   finalized the auction yet.
    NotSoldYet,
    /// The auction is over and the item has been sold to the indicated address.
    Sold(AccountAddress), // winning account's address
}

/// The state of the smart contract.
/// This is the state that will be shown when the contract is queried using
/// `concordium-client contract show`.
#[contract_state(contract = "auction")]
#[derive(Debug, Serialize, SchemaType, Eq, PartialEq)]
pub struct State {
    /// Has the item been sold?
    auction_state: AuctionState,
    /// The highest bid so far (stored explicitly so that bidders can quickly
    /// see it)
    highest_bid: Amount,
    /// The sold item (to be displayed to the auction participants), encoded in
    /// ASCII
    item: Vec<u8>,
    /// Expiration time of the auction at which bids will be closed (to be
    /// displayed to the auction participants)
    expiry: Timestamp,
    /// Keeping track of which account bid how much money
    #[concordium(map_size_length = 2)]
    bids: BTreeMap<AccountAddress, Amount>,
}

/// A helper function to create a state for a new auction.
fn fresh_state(itm: Vec<u8>, exp: Timestamp) -> State {
    State {
        auction_state: AuctionState::NotSoldYet,
        highest_bid:   Amount::zero(),
        item:          itm,
        expiry:        exp,
        bids:          BTreeMap::new(),
    }
}

/// Type of the parameter to the `init` function.
#[derive(Serialize, SchemaType)]
struct InitParameter {
    /// The item to be sold, as a sequence of ASCII codes.
    item: Vec<u8>,
    /// Time of the auction end in the RFC 3339 format (https://tools.ietf.org/html/rfc3339)
    expiry: Timestamp,
}

/// For errors in which the `bid` function can result
#[derive(Debug, PartialEq, Eq, Clone, Reject)]
enum BidError {
    ContractSender, // raised if a contract, as opposed to account, tries to bid
    BidTooLow,      /* { bid: Amount, highest_bid: Amount } */
    // raised if bid is lower than highest amount
    BidsOverWaitingForAuctionFinalization, // raised if bid is placed after auction expiry time
    AuctionFinalized,                      /* raised if bid is placed after auction has been
                                            * finalized */
}

/// For errors in which the `finalize` function can result
#[derive(Debug, PartialEq, Eq, Clone, Reject)]
enum FinalizeError {
    BidMapError,        /* raised if there is a mistake in the bid map that keeps track of all
                         * accounts' bids */
    AuctionStillActive, // raised if there is an attempt to finalize the auction before its expiry
    AuctionFinalized,   // raised if there is an attempt to finalize an already finalized auction
}

/// Init function that creates a new auction
#[init(contract = "auction", parameter = "InitParameter")]
fn auction_init(ctx: &impl HasInitContext) -> InitResult<State> {
    let parameter: InitParameter = ctx.parameter_cursor().get()?;
    Ok(fresh_state(parameter.item, parameter.expiry))
}

/// Receive function in which accounts can bid before the auction end time
#[receive(contract = "auction", name = "bid", payable)]
fn auction_bid<A: HasActions>(
    ctx: &impl HasReceiveContext,
    amount: Amount,
    state: &mut State,
) -> Result<A, BidError> {
    ensure!(state.auction_state == AuctionState::NotSoldYet, BidError::AuctionFinalized);

    let slot_time = ctx.metadata().slot_time();
    ensure!(slot_time <= state.expiry, BidError::BidsOverWaitingForAuctionFinalization);

    let sender_address = match ctx.sender() {
        Address::Contract(_) => bail!(BidError::ContractSender),
        Address::Account(account_address) => account_address,
    };
    let bid_to_update = state.bids.entry(sender_address).or_insert_with(Amount::zero);

    *bid_to_update += amount;
    // Ensure that the new bid exceeds the highest bid so far
    ensure!(
        *bid_to_update > state.highest_bid,
        BidError::BidTooLow /* { bid: amount, highest_bid: state.highest_bid } */
    );
    state.highest_bid = *bid_to_update;

    Ok(A::accept())
}

/// Receive function used to finalize the auction, returning all bids to their
/// senders, except for the winning bid
#[receive(contract = "auction", name = "finalize")]
fn auction_finalize<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut State,
) -> Result<A, FinalizeError> {
    ensure!(state.auction_state == AuctionState::NotSoldYet, FinalizeError::AuctionFinalized);

    let slot_time = ctx.metadata().slot_time();
    ensure!(slot_time > state.expiry, FinalizeError::AuctionStillActive);

    let owner = ctx.owner();

    let balance = ctx.self_balance();
    if balance == Amount::zero() {
        Ok(A::accept())
    } else {
        let mut return_action = A::simple_transfer(&owner, state.highest_bid);
        let mut remaining_bid = None;
        // Return bids that are smaller than highest
        for (addr, &amnt) in state.bids.iter() {
            if amnt < state.highest_bid {
                return_action = return_action.and_then(A::simple_transfer(addr, amnt));
            } else {
                ensure!(remaining_bid.is_none(), FinalizeError::BidMapError);
                state.auction_state = AuctionState::Sold(*addr);
                remaining_bid = Some((addr, amnt));
            }
        }
        // Ensure that the only bidder left in the map is the one with the highest bid
        match remaining_bid {
            Some((_, amount)) => {
                ensure!(amount == state.highest_bid, FinalizeError::BidMapError);
                Ok(return_action)
            }
            None => bail!(FinalizeError::BidMapError),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU8, Ordering};
    use test_infrastructure::*;

    // A counter for generating new account addresses
    static ADDRESS_COUNTER: AtomicU8 = AtomicU8::new(0);
    const AUCTION_END: u64 = 1;
    const ITEM: &str = "Starry night by Van Gogh";

    fn dummy_fresh_state() -> State { dummy_active_state(Amount::zero(), BTreeMap::new()) }

    fn dummy_active_state(highest: Amount, bids: BTreeMap<AccountAddress, Amount>) -> State {
        State {
            auction_state: AuctionState::NotSoldYet,
            highest_bid: highest,
            item: ITEM.as_bytes().to_vec(),
            expiry: Timestamp::from_timestamp_millis(AUCTION_END),
            bids,
        }
    }

    fn expect_error<E, T>(expr: Result<T, E>, err: E, msg: &str)
    where
        E: Eq + Debug,
        T: Debug, {
        let actual = expr.expect_err(msg);
        assert_eq!(actual, err);
    }

    fn item_expiry_parameter() -> InitParameter {
        InitParameter {
            item:   ITEM.as_bytes().to_vec(),
            expiry: Timestamp::from_timestamp_millis(AUCTION_END),
        }
    }

    fn create_parameter_bytes(parameter: &InitParameter) -> Vec<u8> { to_bytes(parameter) }

    fn parametrized_init_ctx<'a>(parameter_bytes: &'a Vec<u8>) -> InitContextTest<'a> {
        let mut ctx = InitContextTest::empty();
        ctx.set_parameter(parameter_bytes);
        ctx
    }

    fn new_account() -> AccountAddress {
        let account = AccountAddress([ADDRESS_COUNTER.load(Ordering::SeqCst); 32]);
        ADDRESS_COUNTER.fetch_add(1, Ordering::SeqCst);
        account
    }

    fn new_account_ctx<'a>() -> (AccountAddress, ReceiveContextTest<'a>) {
        let account = new_account();
        let ctx = new_ctx(account, account, AUCTION_END);
        (account, ctx)
    }

    fn new_ctx<'a>(
        owner: AccountAddress,
        sender: AccountAddress,
        slot_time: u64,
    ) -> ReceiveContextTest<'a> {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(Address::Account(sender));
        ctx.set_owner(owner);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(slot_time));
        ctx
    }

    #[test]
    /// Test that the smart-contract initialization sets the state correctly
    /// (no bids, active state, indicated auction-end time and item name).
    fn test_init() {
        let parameter_bytes = create_parameter_bytes(&item_expiry_parameter());
        let ctx = parametrized_init_ctx(&parameter_bytes);

        let state_result = auction_init(&ctx);
        let state = state_result.expect("Contract initialization results in error");
        assert_eq!(state, dummy_fresh_state(), "Auction state should be new after initialization");
    }

    #[test]
    /// Test a sequence of bids and finalizations:
    /// 0. Auction is initialized.
    /// 1. Alice successfully bids 0.1 GTU.
    /// 2. Alice successfully bids another 0.1 GTU, highest bid becomes 0.2 GTU
    /// (the sum of her two bids). 3. Bob successfully bids 0.3 GTU, highest
    /// bid becomes 0.3 GTU. 4. Someone tries to finalize the auction before
    /// its end time. Attempt fails. 5. Dave successfully finalizes the
    /// auction after its end time.    Alice gets her money back, while
    /// Carol (the owner of the contract) collects the highest bid amount.
    /// 6. Attempts to subsequently bid or finalize fail.
    fn test_auction_bid_and_finalize() {
        let parameter_bytes = create_parameter_bytes(&item_expiry_parameter());
        let ctx0 = parametrized_init_ctx(&parameter_bytes);

        let amount = Amount::from_micro_gtu(100);
        let winning_amount = Amount::from_micro_gtu(300);
        let big_amount = Amount::from_micro_gtu(500);

        let mut bid_map = BTreeMap::new();

        // initializing auction
        let mut state = auction_init(&ctx0).expect("Initialization should pass");

        // 1st bid: account1 bids amount1
        let (alice, alice_ctx) = new_account_ctx();
        verify_bid(&mut state, alice, &alice_ctx, amount, &mut bid_map, amount);

        // 2nd bid: account1 bids `amount` again
        // should work even though it's the same amount because account1 simply
        // increases their bid
        verify_bid(&mut state, alice, &alice_ctx, amount, &mut bid_map, amount + amount);

        // 3rd bid: second account
        let (bob, bob_ctx) = new_account_ctx();
        verify_bid(&mut state, bob, &bob_ctx, winning_amount, &mut bid_map, winning_amount);

        // trying to finalize auction that is still active
        // (specifically, the bid is submitted at the last moment, at the AUCTION_END
        // time)
        let mut ctx4 = ReceiveContextTest::empty();
        ctx4.set_metadata_slot_time(Timestamp::from_timestamp_millis(AUCTION_END));
        let finres: Result<ActionsTree, _> = auction_finalize(&ctx4, &mut state);
        expect_error(
            finres,
            FinalizeError::AuctionStillActive,
            "Finalizing auction should fail when it's before auction-end time",
        );

        // finalizing auction
        let carol = new_account();
        let dave = new_account();
        let mut ctx5 = new_ctx(carol, dave, AUCTION_END + 1);
        ctx5.set_self_balance(winning_amount);
        let finres2: Result<ActionsTree, _> = auction_finalize(&ctx5, &mut state);
        let actions = finres2.expect("Finalizing auction should work");
        assert_eq!(
            actions,
            ActionsTree::simple_transfer(&carol, winning_amount)
                .and_then(ActionsTree::simple_transfer(&alice, amount + amount))
        );
        assert_eq!(state, State {
            auction_state: AuctionState::Sold(bob),
            highest_bid:   winning_amount,
            item:          ITEM.as_bytes().to_vec(),
            expiry:        Timestamp::from_timestamp_millis(AUCTION_END),
            bids:          bid_map,
        });

        // attempting to finalize auction again should fail
        let finres3: Result<ActionsTree, _> = auction_finalize(&ctx5, &mut state);
        expect_error(
            finres3,
            FinalizeError::AuctionFinalized,
            "Finalizing auction a second time should fail",
        );

        // attempting to bid again should fail
        let res4: Result<ActionsTree, _> = auction_bid(&bob_ctx, big_amount, &mut state);
        expect_error(
            res4,
            BidError::AuctionFinalized,
            "Bidding should fail because the auction is finalized",
        );
    }

    fn verify_bid(
        mut state: &mut State,
        account: AccountAddress,
        ctx: &ContextTest<ReceiveOnlyDataTest>,
        amount: Amount,
        bid_map: &mut BTreeMap<AccountAddress, Amount>,
        highest_bid: Amount,
    ) {
        let res: Result<ActionsTree, _> = auction_bid(ctx, amount, &mut state);
        res.expect("Bidding should pass");
        bid_map.insert(account, highest_bid);
        assert_eq!(*state, dummy_active_state(highest_bid, bid_map.clone()));
    }

    #[test]
    /// Bids for amounts lower or equal to the highest bid should be rejected.
    fn test_auction_bid_repeated_bid() {
        let (account1, ctx1) = new_account_ctx();
        let ctx2 = new_account_ctx().1;

        let parameter_bytes = create_parameter_bytes(&item_expiry_parameter());
        let ctx0 = parametrized_init_ctx(&parameter_bytes);

        let amount = Amount::from_micro_gtu(100);

        let mut bid_map = BTreeMap::new();

        // initializing auction
        let mut state = auction_init(&ctx0).expect("Init results in error");

        // 1st bid: account1 bids amount1
        verify_bid(&mut state, account1, &ctx1, amount, &mut bid_map, amount);

        // 2nd bid: account2 bids amount1
        // should fail because amount is equal to highest bid
        let res2: Result<ActionsTree, _> = auction_bid(&ctx2, amount, &mut state);
        expect_error(
            res2,
            BidError::BidTooLow, /* { bid: amount, highest_bid: amount } */
            "Bidding 2 should fail because bid amount must be higher than highest bid",
        );
    }

    #[test]
    /// Bids for 0 GTU should be rejected.
    fn test_auction_bid_zero() {
        let ctx1 = new_account_ctx().1;
        let parameter_bytes = create_parameter_bytes(&item_expiry_parameter());
        let ctx = parametrized_init_ctx(&parameter_bytes);

        let mut state = auction_init(&ctx).expect("Init results in error");

        let res: Result<ActionsTree, _> = auction_bid(&ctx1, Amount::zero(), &mut state);
        expect_error(
            res,
            BidError::BidTooLow, /* { bid: Amount::zero(), highest_bid: Amount::zero()} */
            "Bidding zero should fail",
        );
    }
}
