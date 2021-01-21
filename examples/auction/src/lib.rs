use concordium_std::*;
use std::collections::btree_map::BTreeMap;
use core::fmt::Debug;

// Implementation of an auction smart contract
//
// To bid, participants send GTU using the bid function.
// The participant with the highest bid wins the auction.
// Bids are to be placed before the auction end. After that, bids are refused.
// Only bids that exceed the highest bid are accepted.
// Bids are placed incrementally, i.e., an account's bid is considered
// to be the **sum** of all bids.
// Example: if Alice first bid 1 GTU and then bid 2 GTU, her total
// bid is 3 GTU. The bidding will only go through if 3 GTU is higher than
// the currently highest bid.
//
// After the auction end, any account can finalize the auction.
// The auction can be finalized only once.
// When the auction is finalized, every participant except the
// winner gets their money back.

#[contract_state(contract = "auction")]
#[derive(Debug, Serialize, SchemaType, Eq, PartialEq)]
pub struct State {
    // Is the auction active?
    auction_state: AuctionState,
    // The highest bid so far (stored explicitly so that bidders can quickly see it)
    highest_bid: Amount,
    // The sold item (to be displayed to the auction participants), encoded in ASCII
    item: Vec<u8>,
    // Expiration time of the auction at which bids will be closed (to be displayed to the auction participants)
    expiry: Timestamp,
    // Keeping track of which account bid how much money
    #[concordium(map_size_length = 2)]
    bids: BTreeMap<AccountAddress, Amount>,
}

#[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd)]
pub enum AuctionState {
    Active,
    BidsOverWaitingForAuctionFinalization,
    Sold(AccountAddress), // winning account's address
}

fn fresh_state(itm: Vec<u8>, exp: Timestamp) -> State {
    State {
        auction_state: AuctionState::Active,
        highest_bid: Amount::zero(),
        item: itm,
        expiry: exp,
        bids: BTreeMap::new(),
    }
}

#[derive(Serialize, SchemaType)]
struct InitParameter {
    item: Vec<u8>, // item to be sold as a sequence of ASCII codes
    expiry: Timestamp, // time of the auction end
}

#[derive(Debug, PartialEq, Eq)]
enum ReceiveError {
    ContractSender, // raised if a contract, as opposed to account, tries to bid
    BidTooLow { bidded: Amount, highest_bid: Amount }, // raised if bid is lower than highest amount
    BidsOverWaitingForAuctionFinalization, // raised if bid is placed after auction expiry time
    AuctionFinalized, // raised if bid is placed after auction has been finalized
}

#[derive(Debug, PartialEq, Eq)]
enum FinalizeError {
    BidMapError, // raised if there is a mistake in the bid map that keeps track of all accounts' bids
    AuctionStillActive, // raised if there is an attempt to finalize the auction before its expiry
    AuctionFinalized, // raised if there is an attempt to finalize an already finalized auction
}

#[init(contract = "auction", parameter = "InitParameter")]
fn auction_init(ctx: &impl HasInitContext) -> InitResult<State> {
    let parameter: InitParameter = ctx.parameter_cursor().get()?;
    Ok(fresh_state(parameter.item, parameter.expiry))
}

#[receive(contract = "auction", name = "bid", payable)]
fn auction_bid<A: HasActions>(
    ctx: &impl HasReceiveContext,
    amount: Amount,
    state: &mut State,
) -> Result<A, ReceiveError> {
    ensure!(state.auction_state <= AuctionState::BidsOverWaitingForAuctionFinalization, ReceiveError::AuctionFinalized);

    let slot_time = ctx.metadata().slot_time();
    if slot_time > state.expiry {
        state.auction_state = AuctionState::BidsOverWaitingForAuctionFinalization;
        bail!(ReceiveError::BidsOverWaitingForAuctionFinalization);
    }

    let sender_address = match ctx.sender() {
        Address::Contract(_) => bail!(ReceiveError::ContractSender),
        Address::Account(account_address) => account_address,
    };
    let existing_bid = *state.bids.entry(sender_address).or_insert_with(|| Amount::zero());

    let new_bid = existing_bid + amount;
    // Ensure that the new bid exceeds the highest bid so far
    ensure!(new_bid > state.highest_bid, ReceiveError::BidTooLow { bidded: amount, highest_bid: state.highest_bid });
    state.highest_bid = new_bid;
    state.bids.insert(sender_address, existing_bid + amount);

    Ok(A::accept())
}

#[receive(contract = "auction", name = "finalize")]
fn auction_finalize<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut State,
) -> Result<A, FinalizeError> {
    ensure!(state.auction_state <= AuctionState::BidsOverWaitingForAuctionFinalization, FinalizeError::AuctionFinalized);

    let slot_time = ctx.metadata().slot_time();
    if slot_time <= state.expiry {
        bail!(FinalizeError::AuctionStillActive);
    }

    let owner = ctx.owner();

    ensure!(state.auction_state == AuctionState::Active, FinalizeError::AuctionFinalized);

    let balance = ctx.self_balance();
    if balance == Amount::zero() {
        Ok(A::accept())
    } else {
        let mut return_action = A::simple_transfer(&owner, state.highest_bid);
        let mut remaining_bids = BTreeMap::new();
        // Return bids that are smaller than highest
        for (addr, &amnt) in state.bids.iter() {
            if amnt < state.highest_bid {
                return_action = return_action.and_then(A::simple_transfer(addr, amnt));
            } else {
                state.auction_state = AuctionState::Sold(*addr);
                remaining_bids.insert(addr, amnt);
            }
        }
        // Ensure that the only bidder left in the map is the one with the highest bid
        ensure!(remaining_bids.len() == 1, FinalizeError::BidMapError);
        match remaining_bids.iter().next() {
            Some((_, &amount)) => {
                ensure!(amount == state.highest_bid, FinalizeError::BidMapError);
                Ok(return_action)
            }
            None =>
                bail!(FinalizeError::BidMapError)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_infrastructure::*;
    use std::sync::atomic::{AtomicU8, Ordering};

    // A counter for generating new account addresses
    static ADDRESS_COUNTER: AtomicU8 = AtomicU8::new(0);
    const AUCTION_END: u64 = 1;
    const ITEM: &str = "Starry night by Van Gogh";

    fn dummy_fresh_state() -> State {
        dummy_state(Amount::zero(), BTreeMap::new())
    }

    fn dummy_state(highest: Amount, bids: BTreeMap<AccountAddress, Amount>) -> State {
        State {
            auction_state: AuctionState::Active,
            highest_bid: highest,
            item: ITEM.as_bytes().to_vec(),
            expiry: Timestamp::from_timestamp_millis(AUCTION_END),
            bids: bids,
        }
    }

    fn expect_error<E, T>(expr: Result<T, E>, err: E, msg: &str)
        where E: Eq + Debug, T: Debug {
        let actual = expr.expect_err(msg);
        assert_eq!(actual, err);
    }

    fn item_expiry_parameter() -> InitParameter {
        InitParameter {
            item: ITEM.as_bytes().to_vec(),
            expiry: Timestamp::from_timestamp_millis(AUCTION_END),
        }
    }

    fn create_parameter_bytes(parameter: &InitParameter) -> Vec<u8> {
        to_bytes(parameter)
    }

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

    fn new_ctx<'a>(owner: AccountAddress, sender: AccountAddress, slot_time: u64) -> ReceiveContextTest<'a> {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(Address::Account(sender));
        ctx.set_owner(owner);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(slot_time));
        ctx
    }

    #[test]
    fn test_init() {
        let parameter_bytes = create_parameter_bytes(&item_expiry_parameter());
        let ctx = parametrized_init_ctx(&parameter_bytes);

        let state_result = auction_init(&ctx);
        let state = state_result.expect("Contract initialization results in error");
        assert_eq!(state,
                   dummy_fresh_state(),
                   "Auction state should be new after initialization"
        );
    }

    #[test]
    fn test_auction_bid_and_finalize() {
        let owner = new_account();

        let parameter_bytes = create_parameter_bytes(&item_expiry_parameter());
        let ctx0 = parametrized_init_ctx(&parameter_bytes);

        let amount = Amount::from_micro_gtu(100);
        let winning_amount = Amount::from_micro_gtu(300);
        let big_amount = Amount::from_micro_gtu(500);

        let mut bid_map = BTreeMap::new();

        // initializing auction
        let mut state = auction_init(&ctx0).expect("Initialization should pass");

        // 1st bid: account1 bids amount1
        let (account1, ctx1) = new_account_ctx();
        verify_bid(account1, &ctx1, amount, &mut bid_map, &mut state, amount);

        // 2nd bid: account1 bids `amount` again
        // should work even though it's the same amount because account1 simply increases their bid
        verify_bid(account1, &ctx1, amount, &mut bid_map, &mut state, amount + amount);

        // 3rd bid: second account
        let (account2, ctx2) = new_account_ctx();
        verify_bid(account2, &ctx2, winning_amount, &mut bid_map, &mut state, winning_amount);

        // trying to finalize auction that is still active
        // (specifically, the bid is submitted at the last moment, at the AUCTION_END time)
        let mut ctx4 = ReceiveContextTest::empty();
        ctx4.set_metadata_slot_time(Timestamp::from_timestamp_millis(AUCTION_END));
        let finres: Result<ActionsTree, _> = auction_finalize(&ctx4, &mut state);
        expect_error(finres, FinalizeError::AuctionStillActive,
                     "Finalizing auction should fail when it's before auction-end time");

        // finalizing auction
        let mut ctx5 = new_ctx(owner, owner, AUCTION_END + 1);
        ctx5.set_self_balance(winning_amount);
        let finres2: Result<ActionsTree, _> = auction_finalize(&ctx5, &mut state);
        let actions = finres2.expect("Finalizing auction should work");
        assert_eq!(actions, ActionsTree::simple_transfer(&owner, winning_amount)
            .and_then(ActionsTree::simple_transfer(&account1, amount + amount)));
        assert_eq!(state, State {
            auction_state: AuctionState::Sold(account2),
            highest_bid: winning_amount,
            item: ITEM.as_bytes().to_vec(),
            expiry: Timestamp::from_timestamp_millis(AUCTION_END),
            bids: bid_map.clone(), // todo bad
        });

        // attempting to finalize auction again should fail
        let finres3: Result<ActionsTree, _> = auction_finalize(&ctx5, &mut state);
        expect_error(finres3, FinalizeError::AuctionFinalized,
                     "Finalizing auction a second time should fail");

        // attempting to bid again should fail
        let res4: Result<ActionsTree, _> = auction_bid(&ctx2, big_amount, &mut state);
        expect_error(res4, ReceiveError::AuctionFinalized,
                     "Bidding should fail because the auction is finalized");
    }

    fn verify_bid(
        account: AccountAddress,
        ctx: &ContextTest<ReceiveOnlyDataTest>,
        amount: Amount,
        bid_map: &mut BTreeMap<AccountAddress, Amount>,
        mut state: &mut State,
        highest_bid: Amount,
    ) {
        let res: Result<ActionsTree, _> = auction_bid(ctx, amount, &mut state);
        res.expect("Bidding should pass");
        bid_map.insert(account, highest_bid);
        assert_eq!(*state, dummy_state(highest_bid, bid_map.clone()));
    }

    #[test]
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
        verify_bid(account1, &ctx1, amount, &mut bid_map, &mut state, amount);

        // 2nd bid: account2 bids amount1
        // should fail because amount is equal to highest bid
        let res2: Result<ActionsTree, _> = auction_bid(&ctx2, amount, &mut state);
        expect_error(res2, ReceiveError::BidTooLow { bidded: amount, highest_bid: amount },
                     "Bidding 2 should fail because bidded amount must be higher than highest bid");
    }

    #[test]
    fn test_auction_bid_zero() {
        let ctx1 = new_account_ctx().1;
        let parameter_bytes = create_parameter_bytes(&item_expiry_parameter());
        let ctx = parametrized_init_ctx(&parameter_bytes);

        let mut state = auction_init(&ctx).expect("Init results in error");

        let res: Result<ActionsTree, _> = auction_bid(&ctx1, Amount::zero(), &mut state);
        expect_error(res, ReceiveError::BidTooLow { bidded: Amount::zero(), highest_bid: Amount::zero()},
                     "Bidding zero should fail");
    }
}