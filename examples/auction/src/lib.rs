//! # Implementation of an auction smart contract
//!
//! Accounts can invoke the bid function to participate in the auction.
//! An account has to send some CCD when invoking the bid function.
//! This CCD amount has to exceed the current highest bid to be accepted by the
//! smart contract.
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
use concordium_std::*;
use core::fmt::Debug;

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
#[derive(Debug, Serialize, SchemaType, Clone)]
pub struct State {
    /// State of the auction
    auction_state:  AuctionState,
    /// The highest bidder so far; The variant `None` represents
    /// that no bidder has taken part in the auction yet.
    highest_bidder: Option<AccountAddress>,
    /// The item to be sold (to be displayed by the front-end)
    item:           String,
    /// Time when auction ends (to be displayed by the front-end)
    end:            Timestamp,
}

/// Type of the parameter to the `init` function
#[derive(Serialize, SchemaType)]
struct InitParameter {
    /// The item to be sold
    item: String,
    /// Time when auction ends using the RFC 3339 format (https://tools.ietf.org/html/rfc3339)
    end:  Timestamp,
}

/// `bid` function errors
#[derive(Debug, PartialEq, Eq, Clone, Reject)]
enum BidError {
    /// Raised when a contract tries to bid; Only accounts
    /// are allowed to bid.
    OnlyAccount,
    /// Raised when new bid amount is lower than current highest bid
    BidTooLow,
    /// Raised when bid is placed after auction end time passed
    BidTooLate,
    /// Raised when bid is placed after auction has been finalized
    AuctionAlreadyFinalized,
}

/// `finalize` function errors
#[derive(Debug, PartialEq, Eq, Clone, Reject)]
enum FinalizeError {
    /// Raised when finalizing an auction before auction end time passed
    AuctionStillActive,
    /// Raised when finalizing an auction that is already finalized
    AuctionAlreadyFinalized,
}

/// Init function that creates a new auction
#[init(contract = "auction", parameter = "InitParameter")]
fn auction_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<State> {
    // Getting input parameters
    let parameter: InitParameter = ctx.parameter_cursor().get()?;
    // Creating `State`
    let state = State {
        auction_state:  AuctionState::NotSoldYet,
        highest_bidder: None,
        item:           parameter.item,
        end:            parameter.end,
    };
    Ok(state)
}

/// Receive function for accounts to place a bid in the auction
#[receive(contract = "auction", name = "bid", payable, mutable)]
fn auction_bid<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
    amount: Amount,
) -> Result<(), BidError> {
    let balance = host.self_balance();
    let state = host.state_mut();
    // Ensure the auction has not been finalized yet
    ensure_eq!(state.auction_state, AuctionState::NotSoldYet, BidError::AuctionAlreadyFinalized);

    let slot_time = ctx.metadata().slot_time();
    // Ensure the auction has not ended yet
    ensure!(slot_time <= state.end, BidError::BidTooLate);

    // Ensure that only accounts can place a bid
    let sender_address = match ctx.sender() {
        Address::Contract(_) => bail!(BidError::OnlyAccount),
        Address::Account(account_address) => account_address,
    };

    // Ensure that the new bid exceeds the highest bid so far
    ensure!(amount > balance, BidError::BidTooLow);

    if let Some(account_address) = state.highest_bidder.replace(sender_address) {
        // Refunding old highest bidder;
        // This transfer (given enough NRG of course) always succeeds because the
        // `account_address` exists since it was recorded when it placed a bid.
        // If an `account_address` exists, and the contract has the funds then the
        // transfer will always succeed.
        // Please consider using a pull-over-push pattern when expanding this smart
        // contract to allow smart contract instances to participate in the auction as
        // well. https://consensys.github.io/smart-contract-best-practices/attacks/denial-of-service/
        host.invoke_transfer(&account_address, balance).unwrap_abort();
    }
    Ok(())
}

/// View function that returns the content of the state
#[receive(contract = "auction", name = "view", return_value = "State")]
fn view<'a, 'b, S: HasStateApi>(
    _ctx: &'a impl HasReceiveContext,
    host: &'b impl HasHost<State, StateApiType = S>,
) -> ReceiveResult<&'b State> {
    Ok(host.state())
}

/// Receive function used to finalize the auction. It sends the highest bid (the
/// current balance of this smart contract) to the owner of the smart contract
/// instance.
#[receive(contract = "auction", name = "finalize", mutable)]
fn auction_finalize<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<(), FinalizeError> {
    let state = host.state();
    // Ensure the auction has not been finalized yet
    ensure_eq!(
        state.auction_state,
        AuctionState::NotSoldYet,
        FinalizeError::AuctionAlreadyFinalized
    );

    let slot_time = ctx.metadata().slot_time();
    // Ensure the auction has ended already
    ensure!(slot_time > state.end, FinalizeError::AuctionStillActive);

    if let Some(account_address) = state.highest_bidder {
        // Marking the highest bid (the last bidder) as winner of the auction
        host.state_mut().auction_state = AuctionState::Sold(account_address);
        let owner = ctx.owner();
        let balance = host.self_balance();
        // Sending the highest bid (the balance of this contract) to the owner of the
        // smart contract instance;
        // This transfer (given enough NRG of course) always succeeds because the
        // `owner` exists since it deployed the smart contract instance.
        // If an account exists, and the contract has the funds then the
        // transfer will always succeed.
        host.invoke_transfer(&owner, balance).unwrap_abort();
    }
    Ok(())
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU8, Ordering};
    use test_infrastructure::*;

    // A counter for generating new accounts
    static ADDRESS_COUNTER: AtomicU8 = AtomicU8::new(0);
    const AUCTION_END: u64 = 1;
    const ITEM: &str = "Starry night by Van Gogh";

    fn expect_error<E, T>(expr: Result<T, E>, err: E, msg: &str)
    where
        E: Eq + Debug,
        T: Debug, {
        let actual = expr.expect_err_report(msg);
        claim_eq!(actual, err);
    }

    fn item_end_parameter() -> InitParameter {
        InitParameter {
            item: ITEM.into(),
            end:  Timestamp::from_timestamp_millis(AUCTION_END),
        }
    }

    fn create_parameter_bytes(parameter: &InitParameter) -> Vec<u8> { to_bytes(parameter) }

    fn parametrized_init_ctx(parameter_bytes: &[u8]) -> TestInitContext {
        let mut ctx = TestInitContext::empty();
        ctx.set_parameter(parameter_bytes);
        ctx
    }

    fn new_account() -> AccountAddress {
        let account = AccountAddress([ADDRESS_COUNTER.load(Ordering::SeqCst); 32]);
        ADDRESS_COUNTER.fetch_add(1, Ordering::SeqCst);
        account
    }

    fn new_account_ctx<'a>() -> (AccountAddress, TestReceiveContext<'a>) {
        let account = new_account();
        let ctx = new_ctx(account, account, AUCTION_END);
        (account, ctx)
    }

    fn new_ctx<'a>(
        owner: AccountAddress,
        sender: AccountAddress,
        slot_time: u64,
    ) -> TestReceiveContext<'a> {
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(Address::Account(sender));
        ctx.set_owner(owner);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(slot_time));
        ctx
    }

    #[concordium_test]
    /// Test that the smart-contract initialization sets the state correctly
    /// (no bids, active state, indicated auction-end time and item name).
    fn test_init() {
        let parameter_bytes = create_parameter_bytes(&item_end_parameter());
        let ctx = parametrized_init_ctx(&parameter_bytes);

        let mut state_builder = TestStateBuilder::new();

        let state_result = auction_init(&ctx, &mut state_builder);
        state_result.expect_report("Contract initialization results in error");
    }

    #[concordium_test]
    /// Test a sequence of bids and finalizations:
    /// 0. Auction is initialized.
    /// 1. Alice successfully bids 0.1 CCD.
    /// 2. Alice successfully bids 0.2 CCD, highest
    /// bid becomes 0.2 CCD. Alice gets her 0.1 CCD refunded.
    /// 3. Bob successfully bids 0.3 CCD, highest
    /// bid becomes 0.3 CCD. Alice gets her 0.2 CCD refunded.
    /// 4. Someone tries to finalize the auction before
    /// its end time. Attempt fails.
    /// 5. Dave successfully finalizes the auction after its end time.
    /// Carol (the owner of the contract) collects the highest bid amount.
    /// 6. Attempts to subsequently bid or finalize fail.
    fn test_auction_bid_and_finalize() {
        let parameter_bytes = create_parameter_bytes(&item_end_parameter());
        let ctx0 = parametrized_init_ctx(&parameter_bytes);

        let amount = Amount::from_micro_ccd(100);
        let winning_amount = Amount::from_micro_ccd(300);
        let big_amount = Amount::from_micro_ccd(500);

        let mut state_builder = TestStateBuilder::new();

        // Initializing auction
        let initial_state =
            auction_init(&ctx0, &mut state_builder).expect("Initialization should pass");

        let mut host = TestHost::new(initial_state, state_builder);

        // 1st bid: Alice bids `amount`.
        let (alice, alice_ctx) = new_account_ctx();
        verify_bid(&mut host, &alice_ctx, amount);

        // 2nd bid: Alice bids `amount + amount`.
        // Alice gets her initial bid refunded.
        verify_bid(&mut host, &alice_ctx, amount + amount);

        // 3rd bid: Bob bids `winning_amount`.
        // Alice gets refunded.
        let (bob, bob_ctx) = new_account_ctx();
        verify_bid(&mut host, &bob_ctx, winning_amount);

        // Trying to finalize auction that is still active
        // (specifically, the tx is submitted at the last moment,
        // at the AUCTION_END time)
        let mut ctx4 = TestReceiveContext::empty();
        ctx4.set_metadata_slot_time(Timestamp::from_timestamp_millis(AUCTION_END));
        let finres = auction_finalize(&ctx4, &mut host);
        expect_error(
            finres,
            FinalizeError::AuctionStillActive,
            "Finalizing the auction should fail when it's before auction end time",
        );

        // Finalizing auction
        let carol = new_account();
        let dave = new_account();
        let ctx5 = new_ctx(carol, dave, AUCTION_END + 1);

        let finres2 = auction_finalize(&ctx5, &mut host);
        finres2.expect_report("Finalizing the auction should work");
        let transfers = host.get_transfers();
        // The input arguments of all executed `host.invoke_transfer`
        // functions are checked here.
        claim_eq!(
            &transfers[..],
            &[(alice, amount), (alice, amount + amount), (carol, winning_amount),],
            "Transferring CCD to Alice/Carol should work"
        );
        claim_eq!(
            host.state().auction_state,
            AuctionState::Sold(bob),
            "Finalizing the auction should change the auction state to `Sold(bob)`"
        );
        claim_eq!(
            host.state().highest_bidder,
            Some(bob),
            "Finalizing the auction should mark bob as highest bidder"
        );

        // Attempting to finalize auction again should fail.
        let finres3 = auction_finalize(&ctx5, &mut host);
        expect_error(
            finres3,
            FinalizeError::AuctionAlreadyFinalized,
            "Finalizing the auction a second time should fail",
        );

        // Attempting to bid again should fail.
        let res4 = auction_bid(&bob_ctx, &mut host, big_amount);
        expect_error(
            res4,
            BidError::AuctionAlreadyFinalized,
            "Bidding should fail because the auction is finalized",
        );
    }

    fn verify_bid(
        host: &mut TestHost<State>,
        ctx: &TestContext<TestReceiveOnlyData>,
        amount: Amount,
    ) {
        auction_bid(ctx, host, amount).expect_report("Bidding should pass.");
        host.set_self_balance(amount);
    }

    #[concordium_test]
    /// Bids for amounts lower or equal to the highest bid should be rejected.
    fn test_auction_bid_repeated_bid() {
        let ctx1 = new_account_ctx().1;
        let ctx2 = new_account_ctx().1;

        let parameter_bytes = create_parameter_bytes(&item_end_parameter());
        let ctx0 = parametrized_init_ctx(&parameter_bytes);

        let amount = Amount::from_micro_ccd(100);

        let mut state_builder = TestStateBuilder::new();

        // Initializing auction
        let initial_state =
            auction_init(&ctx0, &mut state_builder).expect("Initialization should succeed.");

        let mut host = TestHost::new(initial_state, state_builder);

        // 1st bid: Account1 bids `amount`.
        verify_bid(&mut host, &ctx1, amount);

        // 2nd bid: Account2 bids `amount` (should fail
        // because amount is equal to highest bid).
        let res2 = auction_bid(&ctx2, &mut host, amount);
        expect_error(
            res2,
            BidError::BidTooLow,
            "Bidding 2 should fail because bid amount must be higher than highest bid",
        );
    }

    #[concordium_test]
    /// Bids for 0 CCD should be rejected.
    fn test_auction_bid_zero() {
        let ctx1 = new_account_ctx().1;
        let parameter_bytes = create_parameter_bytes(&item_end_parameter());
        let ctx = parametrized_init_ctx(&parameter_bytes);

        let mut state_builder = TestStateBuilder::new();

        // initializing auction
        let initial_state =
            auction_init(&ctx, &mut state_builder).expect("Initialization should succeed.");

        let mut host = TestHost::new(initial_state, state_builder);

        let res = auction_bid(&ctx1, &mut host, Amount::zero());
        expect_error(res, BidError::BidTooLow, "Bidding zero should fail");
    }
}
