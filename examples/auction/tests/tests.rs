//! Tests for the auction smart contract.
use auction_smart_contract::*;
use concordium_smart_contract_testing::*;
use concordium_std_derive::*;

/// The tests accounts.
const ALICE: AccountAddress = account_address!("2wkBET2rRgE8pahuaczxKbmv7ciehqsne57F9gtzf1PVdr2VP3");
const BOB: AccountAddress = account_address!("2xBpaHottqhwFZURMZW4uZduQvpxNDSy46iXMYs9kceNGaPpZX");
const CAROL: AccountAddress = account_address!("2xdTv8awN1BjgYEw8W1BVXVtiEwG2b29U8KoZQqJrDuEqddseE");
const DAVE: AccountAddress = account_address!("2y57FyMyqAfY7X1SuSWJ5VMt1Z3ZgxbKt9w5mGoTwqA7YcpbXr");

const SIGNER: Signer = Signer::with_one_key();
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

/// Test a sequence of bids and finalizations:
/// 0. Auction is initialized.
/// 1. Alice successfully bids 1 CCD.
/// 2. Alice successfully bids 2 CCD, highest
/// bid becomes 2 CCD. Alice gets her 1 CCD refunded.
/// 3. Bob successfully bids 3 CCD, highest
/// bid becomes 3 CCD. Alice gets her 2 CCD refunded.
/// 4. Alice tries to bid 3 CCD, which matches the current highest bid, which
/// fails.
/// 5. Alice tries to bid 3.5 CCD, which is below the minimum raise
/// threshold of 1 CCD.
/// 6. Someone tries to finalize the auction before
/// its end time. Attempt fails.
/// 7. Someone tries to bid after the auction has ended (but before it has been
/// finalized), which fails.
/// 8. Dave successfully finalizes the auction after
/// its end time. Carol (the owner of the contract) collects the highest bid
/// amount.
/// 9. Attempts to subsequently bid or finalize fail.
#[test]
fn test_multiple_scenarios() {
    let (mut chain, contract_address) = initialize_chain_and_auction();

    // 1. Alice successfully bids 1 CCD.
    let _update_1 = chain
        .contract_update(
            SIGNER,
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::from_ccd(1),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("auction.bid".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect("Alice successfully bids 1 CCD");

    // 2. Alice successfully bids 2 CCD, highest
    // bid becomes 2 CCD. Alice gets her 1 CCD refunded.
    let update_2 = chain
        .contract_update(
            SIGNER,
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::from_ccd(2),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("auction.bid".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect("Alice successfully bids 2 CCD");
    // Check that 1 CCD is transferred back to ALICE.
    assert_eq!(update_2.account_transfers().collect::<Vec<_>>()[..], [(
        contract_address,
        Amount::from_ccd(1),
        ALICE
    )]);

    // 3. Bob successfully bids 3 CCD, highest
    // bid becomes 3 CCD. Alice gets her 2 CCD refunded.
    let update_3 = chain
        .contract_update(
            SIGNER,
            BOB,
            Address::Account(BOB),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::from_ccd(3),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("auction.bid".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect("Bob successfully bids 3 CCD");
    // Check that 2 CCD is transferred back to ALICE.
    assert_eq!(update_3.account_transfers().collect::<Vec<_>>()[..], [(
        contract_address,
        Amount::from_ccd(2),
        ALICE
    )]);

    // 4. Alice tries to bid 3 CCD, which matches the current highest bid, which
    // fails.
    let update_4 = chain
        .contract_update(
            SIGNER,
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::from_ccd(3),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("auction.bid".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect_err("Alice tries to bid 3 CCD");
    // Check that the correct error is returned.
    let rv: BidError = update_4.parse_return_value().expect("Return value is valid");
    assert_eq!(rv, BidError::BidBelowCurrentBid);

    // 5. Alice tries to bid 3.5 CCD, which is below the minimum raise threshold of
    // 1 CCD.
    let update_5 = chain
        .contract_update(
            SIGNER,
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::from_micro_ccd(3_500_000),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("auction.bid".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect_err("Alice tries to bid 3.5 CCD");
    // Check that the correct error is returned.
    let rv: BidError = update_5.parse_return_value().expect("Return value is valid");
    assert_eq!(rv, BidError::BidBelowMinimumRaise);

    // 6. Someone tries to finalize the auction before
    // its end time. Attempt fails.
    let update_6 = chain
        .contract_update(
            SIGNER,
            DAVE,
            Address::Account(DAVE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("auction.finalize".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect_err("Attempt to finalize auction before end time");
    // Check that the correct error is returned.
    let rv: FinalizeError = update_6.parse_return_value().expect("Return value is valid");
    assert_eq!(rv, FinalizeError::AuctionStillActive);

    // Increment the chain time by 1001 milliseconds.
    chain.tick_block_time(Duration::from_millis(1001)).expect("Increment chain time");

    // 7. Someone tries to bid after the auction has ended (but before it has been
    // finalized), which fails.
    let update_7 = chain
        .contract_update(
            SIGNER,
            DAVE,
            Address::Account(DAVE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::from_ccd(10),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("auction.bid".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect_err("Attempt to bid after auction has reached the endtime");
    // Check that the return value is `BidTooLate`.
    let rv: BidError = update_7.parse_return_value().expect("Return value is valid");
    assert_eq!(rv, BidError::BidTooLate);

    // 8. Dave successfully finalizes the auction after its end time.
    let update_8 = chain
        .contract_update(
            SIGNER,
            DAVE,
            Address::Account(DAVE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("auction.finalize".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect("Dave successfully finalizes the auction after its end time");

    // Check that the correct amount is transferred to Carol.
    assert_eq!(update_8.account_transfers().collect::<Vec<_>>()[..], [(
        contract_address,
        Amount::from_ccd(3),
        CAROL
    )]);

    // 9. Attempts to subsequently bid or finalize fail.
    let update_9 = chain
        .contract_update(
            SIGNER,
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::from_ccd(1),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("auction.bid".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect_err("Attempt to bid after auction has been finalized");
    // Check that the return value is `AuctionAlreadyFinalized`.
    let rv: BidError = update_9.parse_return_value().expect("Return value is valid");
    assert_eq!(rv, BidError::AuctionAlreadyFinalized);

    let update_10 = chain
        .contract_update(
            SIGNER,
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("auction.finalize".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect_err("Attempt to finalize auction after it has been finalized");
    let rv: FinalizeError = update_10.parse_return_value().expect("Return value is valid");
    assert_eq!(rv, FinalizeError::AuctionAlreadyFinalized);
}

/// Setup auction and chain.
///
/// Carol is the owner of the auction, which ends at `1000` milliseconds after
/// the unix epoch. The 'microCCD per euro' exchange rate is set to `1_000_000`,
/// so 1 CCD = 1 euro.
fn initialize_chain_and_auction() -> (Chain, ContractAddress) {
    let mut chain = Chain::builder()
        .micro_ccd_per_euro(
            ExchangeRate::new(1_000_000, 1).expect("Exchange rate is in valid range"),
        )
        .build()
        .expect("Exchange rate is in valid range");

    // Create some accounts on the chain.
    chain.create_account(Account::new(ALICE, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(BOB, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(CAROL, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(DAVE, ACC_INITIAL_BALANCE));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, CAROL, module).expect("Deploy valid module");

    // Create the InitParameter.
    let parameter = InitParameter {
        item:          "Auction item".to_string(),
        end:           Timestamp::from_timestamp_millis(1000),
        minimum_raise: 100, // 100 eurocent = 1 euro
    };

    // Initialize the auction contract.
    let init = chain
        .contract_init(SIGNER, CAROL, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_auction".to_string()),
            param:     OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
        })
        .expect("Initialize auction");

    (chain, init.contract_address)
}
