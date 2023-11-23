//! Tests for the auction smart contract.
use concordium_cis2::{
    BalanceOfQuery, BalanceOfQueryParams, BalanceOfQueryResponse, TokenAmountU64, TokenIdU32,
};
use concordium_smart_contract_testing::*;
use sponsored_tx_enabled_auction::*;

/// The tests accounts.
const ALICE: AccountAddress = AccountAddress([0; 32]);
const ALICE_ADDR: Address = Address::Account(AccountAddress([0; 32]));
const BOB: AccountAddress = AccountAddress([1; 32]);
const CAROL: AccountAddress = AccountAddress([2; 32]);
const DAVE: AccountAddress = AccountAddress([3; 32]);

const SIGNER: Signer = Signer::with_one_key();
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

#[test]
fn test_finalizing_auction() {
    let (mut chain, auction_contract_address, token_contract_address) =
        initialize_chain_and_auction();

    // Create the InitParameter.
    let parameter = AddItemParameter {
        name:        "MyItem".to_string(),
        end:         Timestamp::from_timestamp_millis(1000),
        start:       Timestamp::from_timestamp_millis(5000),
        token_id:    TokenIdU32(1),
        minimum_bid: TokenAmountU64(3),
    };

    let _update = chain
        .contract_update(
            SIGNER,
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::from_ccd(0),
                address:      auction_contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "sponsored_tx_enabled_auction.addItem".to_string(),
                ),
                message:      OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
            },
        )
        .expect("Should be able to add Item");

    let _update = chain
        .contract_update(
            SIGNER,
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::from_ccd(0),
                address:      auction_contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "sponsored_tx_enabled_auction.bid".to_string(),
                ),
                message:      OwnedParameter::from_serial(&0u16).expect("Serialize parameter"),
            },
        )
        .expect("Should be able to finalize");

    let parameter = cis3_nft_sponsored_txs::MintParams {
        owner: concordium_smart_contract_testing::Address::Contract(auction_contract_address),
    };

    let _update = chain
        .contract_update(
            SIGNER,
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::from_ccd(0),
                address:      token_contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis3_nft.mint".to_string()),
                message:      OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
            },
        )
        .expect("Should be able to finalize");

    // Invoke the view entrypoint and check that the tokens are owned by Alice.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "sponsored_tx_enabled_auction.viewItemState".to_string(),
            ),
            address:      auction_contract_address,
            message:      OwnedParameter::from_serial(&0u16).expect("Serialize parameter"),
        })
        .expect("Invoke view");

    // Check that the tokens are owned by Alice.
    let rv: ItemState = invoke.parse_return_value().expect("ViewItemState return value");
    println!("{:?}", rv);

    let balance_of_params = ContractBalanceOfQueryParams {
        queries: vec![BalanceOfQuery {
            token_id: TokenIdU32(1),
            address:  ALICE_ADDR,
        }],
    };

    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis3_nft.balanceOf".to_string()),
            address:      token_contract_address,
            message:      OwnedParameter::from_serial(&balance_of_params)
                .expect("BalanceOf params"),
        })
        .expect("Invoke balanceOf");
    let rv: ContractBalanceOfQueryResponse =
        invoke.parse_return_value().expect("BalanceOf return value");
    println!("{rv:?}");

    // Increment the chain time by 100000 milliseconds.
    chain.tick_block_time(Duration::from_millis(100000)).expect("Increment chain time");

    let _update = chain
        .contract_update(
            SIGNER,
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::from_ccd(0),
                address:      auction_contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "sponsored_tx_enabled_auction.finalize".to_string(),
                ),
                message:      OwnedParameter::from_serial(&0u16).expect("Serialize parameter"),
            },
        )
        .expect("Should be able to finalize");

    // Invoke the view entrypoint and check that the tokens are owned by Alice.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "sponsored_tx_enabled_auction.viewItemState".to_string(),
            ),
            address:      auction_contract_address,
            message:      OwnedParameter::from_serial(&0u16).expect("Serialize parameter"),
        })
        .expect("Invoke view");

    // Check that the tokens are owned by Alice.
    let rv: ItemState = invoke.parse_return_value().expect("ViewItemState return value");
    println!("{rv:?}");
    assert_eq!(rv.auction_state, AuctionState::Sold(ALICE));

    /// Parameter type for the CIS-2 function `balanceOf` specialized to the
    /// subset of TokenIDs used by this contract.
    pub type ContractBalanceOfQueryParams = BalanceOfQueryParams<ContractTokenId>;
    /// Response type for the CIS-2 function `balanceOf` specialized to the
    /// subset of TokenAmounts used by this contract.
    pub type ContractBalanceOfQueryResponse = BalanceOfQueryResponse<ContractTokenAmount>;

    let balance_of_params = ContractBalanceOfQueryParams {
        queries: vec![BalanceOfQuery {
            token_id: TokenIdU32(1),
            address:  ALICE_ADDR,
        }],
    };

    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis3_nft.balanceOf".to_string()),
            address:      token_contract_address,
            message:      OwnedParameter::from_serial(&balance_of_params)
                .expect("BalanceOf params"),
        })
        .expect("Invoke balanceOf");
    let rv: ContractBalanceOfQueryResponse =
        invoke.parse_return_value().expect("BalanceOf return value");
    println!("{rv:?}");
}

#[test]
fn test_add_item() {
    let (mut chain, auction_contract_address, _token_contract_address) =
        initialize_chain_and_auction();

    // Create the InitParameter.
    let parameter = AddItemParameter {
        name:        "MyItem".to_string(),
        end:         Timestamp::from_timestamp_millis(1000),
        start:       Timestamp::from_timestamp_millis(5000),
        token_id:    TokenIdU32(1),
        minimum_bid: TokenAmountU64(3),
    };

    let _update = chain
        .contract_update(
            SIGNER,
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::from_ccd(0),
                address:      auction_contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "sponsored_tx_enabled_auction.addItem".to_string(),
                ),
                message:      OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
            },
        )
        .expect("Should be able to add Item");

    // Invoke the view entrypoint and check that the tokens are owned by Alice.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "sponsored_tx_enabled_auction.view".to_string(),
            ),
            address:      auction_contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");

    // Check that the tokens are owned by Alice.
    let rv: ReturnParamView = invoke.parse_return_value().expect("View return value");

    assert_eq!(rv, ReturnParamView {
        item_states:   vec![(0, ItemState {
            auction_state:  AuctionState::NotSoldYet,
            highest_bidder: None,
            name:           "MyItem".to_string(),
            end:            Timestamp::from_timestamp_millis(1000),
            start:          Timestamp::from_timestamp_millis(5000),
            token_id:       TokenIdU32(1),
            creator:        ALICE,
            highest_bid:    TokenAmountU64(3),
        })],
        cis2_contract: ContractAddress::new(0, 0),
        counter:       1,
    });

    // Invoke the view entrypoint and check that the tokens are owned by Alice.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "sponsored_tx_enabled_auction.viewItemState".to_string(),
            ),
            address:      auction_contract_address,
            message:      OwnedParameter::from_serial(&0u16).expect("Serialize parameter"),
        })
        .expect("Invoke view");

    // Check that the tokens are owned by Alice.
    let rv: ItemState = invoke.parse_return_value().expect("ViewItemState return value");

    assert_eq!(rv, ItemState {
        auction_state:  AuctionState::NotSoldYet,
        highest_bidder: None,
        name:           "MyItem".to_string(),
        end:            Timestamp::from_timestamp_millis(1000),
        start:          Timestamp::from_timestamp_millis(5000),
        token_id:       TokenIdU32(1),
        creator:        ALICE,
        highest_bid:    TokenAmountU64(3),
    });
}

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
// #[test]
// fn test_multiple_scenarios() {
//     let (mut chain, contract_address) = initialize_chain_and_auction();

//     // 1. Alice successfully bids 1 CCD.
//     let _update_1 = chain
//         .contract_update(
//             SIGNER,
//             ALICE,
//             Address::Account(ALICE),
//             Energy::from(10000),
//             UpdateContractPayload {
//                 amount:       Amount::from_ccd(1),
//                 address:      contract_address,
//                 receive_name:
// OwnedReceiveName::new_unchecked("sponsored_tx_enabled_auction.bid".to_string()),
// message:      OwnedParameter::empty(),             },
//         )
//         .expect("Alice successfully bids 1 CCD");

//     // 2. Alice successfully bids 2 CCD, highest
//     // bid becomes 2 CCD. Alice gets her 1 CCD refunded.
//     let update_2 = chain
//         .contract_update(
//             SIGNER,
//             ALICE,
//             Address::Account(ALICE),
//             Energy::from(10000),
//             UpdateContractPayload {
//                 amount:       Amount::from_ccd(2),
//                 address:      contract_address,
//                 receive_name:
// OwnedReceiveName::new_unchecked("sponsored_tx_enabled_auction.bid".to_string()),
// message:      OwnedParameter::empty(),             },
//         )
//         .expect("Alice successfully bids 2 CCD");
//     // Check that 1 CCD is transferred back to ALICE.
//     assert_eq!(update_2.account_transfers().collect::<Vec<_>>()[..], [(
//         contract_address,
//         Amount::from_ccd(1),
//         ALICE
//     )]);

//     // 3. Bob successfully bids 3 CCD, highest
//     // bid becomes 3 CCD. Alice gets her 2 CCD refunded.
//     let update_3 = chain
//         .contract_update(
//             SIGNER,
//             BOB,
//             Address::Account(BOB),
//             Energy::from(10000),
//             UpdateContractPayload {
//                 amount:       Amount::from_ccd(3),
//                 address:      contract_address,
//                 receive_name:
// OwnedReceiveName::new_unchecked("sponsored_tx_enabled_auction.bid".to_string()),
// message:      OwnedParameter::empty(),             },
//         )
//         .expect("Bob successfully bids 3 CCD");
//     // Check that 2 CCD is transferred back to ALICE.
//     assert_eq!(update_3.account_transfers().collect::<Vec<_>>()[..], [(
//         contract_address,
//         Amount::from_ccd(2),
//         ALICE
//     )]);

//     // 4. Alice tries to bid 3 CCD, which matches the current highest bid, which
//     // fails.
//     let update_4 = chain
//         .contract_update(
//             SIGNER,
//             ALICE,
//             Address::Account(ALICE),
//             Energy::from(10000),
//             UpdateContractPayload {
//                 amount:       Amount::from_ccd(3),
//                 address:      contract_address,
//                 receive_name:
// OwnedReceiveName::new_unchecked("sponsored_tx_enabled_auction.bid".to_string()),
// message:      OwnedParameter::empty(),             },
//         )
//         .expect_err("Alice tries to bid 3 CCD");
//     // Check that the correct error is returned.
//     let rv: BidError = update_4.parse_return_value().expect("Return value is valid");
//     assert_eq!(rv, BidError::BidBelowCurrentBid);

//     // 5. Alice tries to bid 3.5 CCD, which is below the minimum raise threshold of
//     // 1 CCD.
//     let update_5 = chain
//         .contract_update(
//             SIGNER,
//             ALICE,
//             Address::Account(ALICE),
//             Energy::from(10000),
//             UpdateContractPayload {
//                 amount:       Amount::from_micro_ccd(3_500_000),
//                 address:      contract_address,
//                 receive_name:
// OwnedReceiveName::new_unchecked("sponsored_tx_enabled_auction.bid".to_string()),
// message:      OwnedParameter::empty(),             },
//         )
//         .expect_err("Alice tries to bid 3.5 CCD");
//     // Check that the correct error is returned.
//     let rv: BidError = update_5.parse_return_value().expect("Return value is valid");
//     assert_eq!(rv, BidError::BidBelowMinimumRaise);

//     // 6. Someone tries to finalize the auction before
//     // its end time. Attempt fails.
//     let update_6 = chain
//         .contract_update(
//             SIGNER,
//             DAVE,
//             Address::Account(DAVE),
//             Energy::from(10000),
//             UpdateContractPayload {
//                 amount:       Amount::zero(),
//                 address:      contract_address,
//                 receive_name:
// OwnedReceiveName::new_unchecked("sponsored_tx_enabled_auction.finalize".to_string()),
// message:      OwnedParameter::empty(),             },
//         )
//         .expect_err("Attempt to finalize auction before end time");
//     // Check that the correct error is returned.
//     let rv: FinalizeError = update_6.parse_return_value().expect("Return value is valid");
//     assert_eq!(rv, FinalizeError::AuctionStillActive);

//     // Increment the chain time by 1001 milliseconds.
//     chain.tick_block_time(Duration::from_millis(1001)).expect("Increment chain time");

//     // 7. Someone tries to bid after the auction has ended (but before it has been
//     // finalized), which fails.
//     let update_7 = chain
//         .contract_update(
//             SIGNER,
//             DAVE,
//             Address::Account(DAVE),
//             Energy::from(10000),
//             UpdateContractPayload {
//                 amount:       Amount::from_ccd(10),
//                 address:      contract_address,
//                 receive_name:
// OwnedReceiveName::new_unchecked("sponsored_tx_enabled_auction.bid".to_string()),
// message:      OwnedParameter::empty(),             },
//         )
//         .expect_err("Attempt to bid after auction has reached the endtime");
//     // Check that the return value is `BidTooLate`.
//     let rv: BidError = update_7.parse_return_value().expect("Return value is valid");
//     assert_eq!(rv, BidError::BidTooLate);

//     // 8. Dave successfully finalizes the auction after its end time.
//     let update_8 = chain
//         .contract_update(
//             SIGNER,
//             DAVE,
//             Address::Account(DAVE),
//             Energy::from(10000),
//             UpdateContractPayload {
//                 amount:       Amount::zero(),
//                 address:      contract_address,
//                 receive_name:
// OwnedReceiveName::new_unchecked("sponsored_tx_enabled_auction.finalize".to_string()),
// message:      OwnedParameter::empty(),             },
//         )
//         .expect("Dave successfully finalizes the auction after its end time");

//     // Check that the correct amount is transferred to Carol.
//     assert_eq!(update_8.account_transfers().collect::<Vec<_>>()[..], [(
//         contract_address,
//         Amount::from_ccd(3),
//         CAROL
//     )]);

//     // 9. Attempts to subsequently bid or finalize fail.
//     let update_9 = chain
//         .contract_update(
//             SIGNER,
//             ALICE,
//             Address::Account(ALICE),
//             Energy::from(10000),
//             UpdateContractPayload {
//                 amount:       Amount::from_ccd(1),
//                 address:      contract_address,
//                 receive_name:
// OwnedReceiveName::new_unchecked("sponsored_tx_enabled_auction.bid".to_string()),
// message:      OwnedParameter::empty(),             },
//         )
//         .expect_err("Attempt to bid after auction has been finalized");
//     // Check that the return value is `AuctionAlreadyFinalized`.
//     let rv: BidError = update_9.parse_return_value().expect("Return value is valid");
//     assert_eq!(rv, BidError::AuctionAlreadyFinalized);

//     let update_10 = chain
//         .contract_update(
//             SIGNER,
//             ALICE,
//             Address::Account(ALICE),
//             Energy::from(10000),
//             UpdateContractPayload {
//                 amount:       Amount::zero(),
//                 address:      contract_address,
//                 receive_name:
// OwnedReceiveName::new_unchecked("sponsored_tx_enabled_auction.finalize".to_string()),
// message:      OwnedParameter::empty(),             },
//         )
//         .expect_err("Attempt to finalize auction after it has been finalized");
//     let rv: FinalizeError = update_10.parse_return_value().expect("Return value is valid");
//     assert_eq!(rv, FinalizeError::AuctionAlreadyFinalized);
// }

/// Setup auction and chain.
///
/// Carol is the owner of the auction, which ends at `1000` milliseconds after
/// the unix epoch. The 'microCCD per euro' exchange rate is set to `1_000_000`,
/// so 1 CCD = 1 euro.
fn initialize_chain_and_auction() -> (Chain, ContractAddress, ContractAddress) {
    let mut chain = Chain::builder()
        .micro_ccd_per_euro(
            ExchangeRate::new(1_000_000, 1).expect("Exchange rate is in valid range"),
        )
        .build()
        .expect("Exchange rate is in valid range");

    // Create some accounts accounts on the chain.
    chain.create_account(Account::new(ALICE, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(BOB, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(CAROL, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(DAVE, ACC_INITIAL_BALANCE));

    // Load and deploy the module.
    let module = module_load_v1("../cis3-nft-sponsored-txs/concordium-out/module.wasm.v1")
        .expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, CAROL, module).expect("Deploy valid module");

    // Create the InitParameter.
    let parameter = ContractAddress::new(0, 0);

    // Initialize the auction contract.
    let token = chain
        .contract_init(SIGNER, CAROL, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_cis3_nft".to_string()),
            param:     OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
        })
        .expect("Initialize auction");

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, CAROL, module).expect("Deploy valid module");

    // Create the InitParameter.
    let parameter = token.contract_address;

    // Initialize the auction contract.
    let init_auction = chain
        .contract_init(SIGNER, CAROL, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked(
                "init_sponsored_tx_enabled_auction".to_string(),
            ),
            param:     OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
        })
        .expect("Initialize auction");

    (chain, init_auction.contract_address, token.contract_address)
}
