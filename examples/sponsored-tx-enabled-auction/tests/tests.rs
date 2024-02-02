//! Tests for the sponsored-tx-enabled-auction smart contract.
use cis2_multi::{
    ContractBalanceOfQueryParams, ContractBalanceOfQueryResponse, PermitMessage, PermitParam,
};
use concordium_cis2::{
    AdditionalData, BalanceOfQuery, BalanceOfQueryParams, Receiver, TokenAmountU64, TokenIdU8,
    TransferParams,
};
use concordium_smart_contract_testing::*;
use concordium_std::{
    AccountSignatures, CredentialSignatures, HashSha2256, MetadataUrl, SignatureEd25519,
};
use sponsored_tx_enabled_auction::*;
use std::collections::BTreeMap;

/// The test accounts.
const ALICE: AccountAddress = AccountAddress([0; 32]);
const ALICE_ADDR: Address = Address::Account(AccountAddress([0; 32]));
const BOB: AccountAddress = AccountAddress([1; 32]);
const BOB_ADDR: Address = Address::Account(AccountAddress([1; 32]));
const CAROL: AccountAddress = AccountAddress([2; 32]);

const SIGNER: Signer = Signer::with_one_key();
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

const DUMMY_SIGNATURE: SignatureEd25519 = SignatureEd25519([
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
]);

#[test]
fn test_add_item() {
    let (mut chain, _keypairs_alice, auction_contract_address, _token_contract_address) =
        initialize_chain_and_auction();

    // Create the InitParameter.
    let parameter = AddItemParameter {
        name:        "MyItem".to_string(),
        start:       Timestamp::from_timestamp_millis(1000),
        end:         Timestamp::from_timestamp_millis(5000),
        token_id:    TokenIdU8(1),
        minimum_bid: TokenAmountU64(3),
    };

    // Add item.
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

    // Invoke the view entry point and check that the item was added.
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

    let rv: ReturnParamView = invoke.parse_return_value().expect("View return value");

    assert_eq!(rv, ReturnParamView {
        item_states:   vec![(1, ItemState {
            auction_state:  AuctionState::NotSoldYet,
            highest_bidder: None,
            name:           "MyItem".to_string(),
            start:          Timestamp::from_timestamp_millis(1000),
            end:            Timestamp::from_timestamp_millis(5000),
            token_id:       TokenIdU8(1),
            creator:        ALICE,
            highest_bid:    TokenAmountU64(3),
        })],
        cis2_contract: ContractAddress::new(0, 0),
        counter:       1,
    });

    // Invoke the viewItemState entry point and check that the item was added.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "sponsored_tx_enabled_auction.viewItemState".to_string(),
            ),
            address:      auction_contract_address,
            message:      OwnedParameter::from_serial(&1u16).expect("Serialize parameter"),
        })
        .expect("Invoke viewItemState");

    let rv: ItemState = invoke.parse_return_value().expect("ViewItemState return value");

    assert_eq!(rv, ItemState {
        auction_state:  AuctionState::NotSoldYet,
        highest_bidder: None,
        name:           "MyItem".to_string(),
        start:          Timestamp::from_timestamp_millis(1000),
        end:            Timestamp::from_timestamp_millis(5000),
        token_id:       TokenIdU8(1),
        creator:        ALICE,
        highest_bid:    TokenAmountU64(3),
    });
}

#[test]
fn full_auction_flow_with_cis3_permit_function() {
    let (mut chain, keypairs_alice, auction_contract_address, token_contract_address) =
        initialize_chain_and_auction();

    // Create the InitParameter.
    let parameter = AddItemParameter {
        name:        "MyItem".to_string(),
        start:       Timestamp::from_timestamp_millis(1000),
        end:         Timestamp::from_timestamp_millis(5000),
        token_id:    TokenIdU8(1),
        minimum_bid: TokenAmountU64(0),
    };

    // Add item.
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

    // Airdrop tokens to ALICE.
    let parameter = cis2_multi::MintParams {
        owner:        concordium_smart_contract_testing::Address::Account(ALICE),
        metadata_url: MetadataUrl {
            url:  "https://some.example/token/0".to_string(),
            hash: None,
        },
        token_id:     concordium_cis2::TokenIdU8(1u8),
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
                receive_name: OwnedReceiveName::new_unchecked("cis2_multi.mint".to_string()),
                message:      OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
            },
        )
        .expect("Should be able to mint");

    // Check balances in state.
    let balance_of_alice_and_auction_contract =
        get_balances(&chain, auction_contract_address, token_contract_address);
    assert_eq!(balance_of_alice_and_auction_contract.0, [TokenAmountU64(100), TokenAmountU64(0)]);

    // Create input parameters for the `permit` transfer function.
    let additional_data = AdditionalDataIndex {
        item_index: 1u16,
    };

    let transfer = concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::Contract(
            auction_contract_address,
            OwnedEntrypointName::new_unchecked("bid".to_string()),
        ),
        token_id: TokenIdU8(1),
        amount:   TokenAmountU64(1),
        data:     AdditionalData::from(to_bytes(&additional_data)),
    };
    let payload = TransferParams::from(vec![transfer]);

    // The `viewMessageHash` function uses the same input parameter `PermitParam` as
    // the `permit` function. The `PermitParam` type includes a `signature` and
    // a `signer`. Because these two values (`signature` and `signer`) are not
    // read in the `viewMessageHash` function, any value can be used and we choose
    // to use `DUMMY_SIGNATURE` and `ALICE` in the test case below.
    let signature_map = BTreeMap::from([(0u8, CredentialSignatures {
        sigs: BTreeMap::from([(0u8, concordium_std::Signature::Ed25519(DUMMY_SIGNATURE))]),
    })]);

    let mut permit_transfer_param = PermitParam {
        signature: AccountSignatures {
            sigs: signature_map,
        },
        signer:    ALICE,
        message:   PermitMessage {
            timestamp:        Timestamp::from_timestamp_millis(10_000_000_000),
            contract_address: ContractAddress::new(0, 0),
            entry_point:      OwnedEntrypointName::new_unchecked("transfer".into()),
            nonce:            0,
            payload:          to_bytes(&payload),
        },
    };

    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      token_contract_address,
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.viewMessageHash".to_string()),
            message:      OwnedParameter::from_serial(&permit_transfer_param)
                .expect("Should be a valid inut parameter"),
        })
        .expect("Should be able to query viewMessageHash");

    let message_hash: HashSha2256 =
        from_bytes(&invoke.return_value).expect("Should return a valid result");

    // Sign message hash.
    permit_transfer_param.signature = keypairs_alice.sign_message(&to_bytes(&message_hash));

    // Transfer token with the permit function.
    let _update = chain
        .contract_update(
            Signer::with_one_key(),
            BOB,
            BOB_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      token_contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis2_multi.permit".to_string()),
                message:      OwnedParameter::from_serial(&permit_transfer_param)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to transfer token with permit");

    // Check balances in state.
    let balance_of_alice_and_auction_contract =
        get_balances(&chain, auction_contract_address, token_contract_address);
    assert_eq!(balance_of_alice_and_auction_contract.0, [TokenAmountU64(99), TokenAmountU64(1)]);

    // Check that the item is not sold yet.
    let item_state = view_item_state(&chain, auction_contract_address);
    assert_eq!(item_state.auction_state, AuctionState::NotSoldYet);

    // Increment the chain time by 100000 milliseconds.
    chain.tick_block_time(Duration::from_millis(100000)).expect("Increment chain time");

    // Finalize the auction.
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
                message:      OwnedParameter::from_serial(&1u16).expect("Serialize parameter"),
            },
        )
        .expect("Should be able to finalize");

    // Check that the item is sold to ALICE.
    let item_state = view_item_state(&chain, auction_contract_address);
    assert_eq!(item_state.auction_state, AuctionState::Sold(ALICE));
}

#[test]
fn full_auction_flow_with_several_bids() {
    let (mut chain, keypairs_alice, auction_contract_address, token_contract_address) =
        initialize_chain_and_auction();

    // Create the InitParameter.
    let parameter = AddItemParameter {
        name:        "MyItem".to_string(),
        start:       Timestamp::from_timestamp_millis(1000),
        end:         Timestamp::from_timestamp_millis(5000),
        token_id:    TokenIdU8(1),
        minimum_bid: TokenAmountU64(0),
    };

    // Add item.
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

    // Airdrop tokens to ALICE.
    let parameter = cis2_multi::MintParams {
        owner:        concordium_smart_contract_testing::Address::Account(ALICE),
        metadata_url: MetadataUrl {
            url:  "https://some.example/token/0".to_string(),
            hash: None,
        },
        token_id:     concordium_cis2::TokenIdU8(1u8),
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
                receive_name: OwnedReceiveName::new_unchecked("cis2_multi.mint".to_string()),
                message:      OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
            },
        )
        .expect("Should be able to mint");

    // Check balances in state.
    let balance_of_alice_and_auction_contract =
        get_balances(&chain, auction_contract_address, token_contract_address);
    assert_eq!(balance_of_alice_and_auction_contract.0, [TokenAmountU64(100), TokenAmountU64(0)]);

    // Create input parameters for the `permit` transfer function.
    let additional_data = AdditionalDataIndex {
        item_index: 1u16,
    };

    let transfer = concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::Contract(
            auction_contract_address,
            OwnedEntrypointName::new_unchecked("bid".to_string()),
        ),
        token_id: TokenIdU8(1),
        amount:   TokenAmountU64(1),
        data:     AdditionalData::from(to_bytes(&additional_data)),
    };
    let payload = TransferParams::from(vec![transfer]);

    // The `viewMessageHash` function uses the same input parameter `PermitParam` as
    // the `permit` function. The `PermitParam` type includes a `signature` and
    // a `signer`. Because these two values (`signature` and `signer`) are not
    // read in the `viewMessageHash` function, any value can be used and we choose
    // to use `DUMMY_SIGNATURE` and `ALICE` in the test case below.
    let signature_map = BTreeMap::from([(0u8, CredentialSignatures {
        sigs: BTreeMap::from([(0u8, concordium_std::Signature::Ed25519(DUMMY_SIGNATURE))]),
    })]);

    let mut permit_transfer_param = PermitParam {
        signature: AccountSignatures {
            sigs: signature_map,
        },
        signer:    ALICE,
        message:   PermitMessage {
            timestamp:        Timestamp::from_timestamp_millis(10_000_000_000),
            contract_address: ContractAddress::new(0, 0),
            entry_point:      OwnedEntrypointName::new_unchecked("transfer".into()),
            nonce:            0,
            payload:          to_bytes(&payload),
        },
    };

    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      token_contract_address,
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.viewMessageHash".to_string()),
            message:      OwnedParameter::from_serial(&permit_transfer_param)
                .expect("Should be a valid inut parameter"),
        })
        .expect("Should be able to query viewMessageHash");

    let message_hash: HashSha2256 =
        from_bytes(&invoke.return_value).expect("Should return a valid result");

    // Sign message hash.
    permit_transfer_param.signature = keypairs_alice.sign_message(&to_bytes(&message_hash));

    // Transfer token with the permit function.
    let _update = chain
        .contract_update(
            Signer::with_one_key(),
            BOB,
            BOB_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      token_contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis2_multi.permit".to_string()),
                message:      OwnedParameter::from_serial(&permit_transfer_param)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to transfer token with permit");

    // Check balances in state.
    let balance_of_alice_and_auction_contract =
        get_balances(&chain, auction_contract_address, token_contract_address);
    assert_eq!(balance_of_alice_and_auction_contract.0, [TokenAmountU64(99), TokenAmountU64(1)]);

    // Airdrop tokens to BOB.
    let parameter = cis2_multi::MintParams {
        owner:        concordium_smart_contract_testing::Address::Account(BOB),
        metadata_url: MetadataUrl {
            url:  "https://some.example/token/0".to_string(),
            hash: None,
        },
        token_id:     concordium_cis2::TokenIdU8(1u8),
    };

    let _update = chain
        .contract_update(
            SIGNER,
            ALICE,
            Address::Account(BOB),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::from_ccd(0),
                address:      token_contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis2_multi.mint".to_string()),
                message:      OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
            },
        )
        .expect("Should be able to mint");

    // Transfer two tokens from BOB to the auction contract.
    let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     BOB_ADDR,
        to:       Receiver::Contract(
            auction_contract_address,
            OwnedEntrypointName::new_unchecked("bid".to_string()),
        ),
        token_id: TokenIdU8(1),
        amount:   TokenAmountU64(2),
        data:     AdditionalData::from(to_bytes(&additional_data)),
    }]);

    let _update = chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.transfer".to_string()),
            address:      token_contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect("Transfer tokens");

    // Check that ALICE has been refunded her initial bid and the auction contract
    // received the 2 tokens from BOB.
    let balance_of_alice_and_auction_contract =
        get_balances(&chain, auction_contract_address, token_contract_address);
    assert_eq!(balance_of_alice_and_auction_contract.0, [TokenAmountU64(100), TokenAmountU64(2)]);

    // Check that the item is not sold yet.
    let item_state = view_item_state(&chain, auction_contract_address);
    assert_eq!(item_state.auction_state, AuctionState::NotSoldYet);

    // Increment the chain time by 100000 milliseconds.
    chain.tick_block_time(Duration::from_millis(100000)).expect("Increment chain time");

    // Finalize the auction.
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
                message:      OwnedParameter::from_serial(&1u16).expect("Serialize parameter"),
            },
        )
        .expect("Should be able to finalize");

    // Check that the item is sold to BOB.
    let item_state = view_item_state(&chain, auction_contract_address);
    assert_eq!(item_state.auction_state, AuctionState::Sold(BOB));

    // Check that ALICE as creator got the payout when the auction ended.
    let balance_of_alice_and_auction_contract =
        get_balances(&chain, auction_contract_address, token_contract_address);
    assert_eq!(balance_of_alice_and_auction_contract.0, [TokenAmountU64(102), TokenAmountU64(0)]);
}

#[test]
fn full_auction_flow_with_cis3_transfer_function() {
    let (mut chain, _keypair_alice, auction_contract_address, token_contract_address) =
        initialize_chain_and_auction();

    // Create the InitParameter.
    let parameter = AddItemParameter {
        name:        "MyItem".to_string(),
        start:       Timestamp::from_timestamp_millis(1000),
        end:         Timestamp::from_timestamp_millis(5000),
        token_id:    TokenIdU8(1),
        minimum_bid: TokenAmountU64(0),
    };

    // Add item.
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

    // Airdrop tokens to ALICE.
    let parameter = cis2_multi::MintParams {
        owner:        concordium_smart_contract_testing::Address::Account(ALICE),
        metadata_url: MetadataUrl {
            url:  "https://some.example/token/0".to_string(),
            hash: None,
        },
        token_id:     concordium_cis2::TokenIdU8(1u8),
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
                receive_name: OwnedReceiveName::new_unchecked("cis2_multi.mint".to_string()),
                message:      OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
            },
        )
        .expect("Should be able to mint");

    // Check balances in state.
    let balance_of_alice_and_auction_contract =
        get_balances(&chain, auction_contract_address, token_contract_address);
    assert_eq!(balance_of_alice_and_auction_contract.0, [TokenAmountU64(100), TokenAmountU64(0)]);

    let additional_data = AdditionalDataIndex {
        item_index: 1u16,
    };

    // Transfer one token from ALICE to the auction contract.
    let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::Contract(
            auction_contract_address,
            OwnedEntrypointName::new_unchecked("bid".to_string()),
        ),
        token_id: TokenIdU8(1),
        amount:   TokenAmountU64(1),
        data:     AdditionalData::from(to_bytes(&additional_data)),
    }]);

    let _update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.transfer".to_string()),
            address:      token_contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect("Transfer tokens");

    // Check that the item is not sold yet.
    let item_state = view_item_state(&chain, auction_contract_address);
    assert_eq!(item_state.auction_state, AuctionState::NotSoldYet);

    // Check balances in state.
    let balance_of_alice_and_auction_contract =
        get_balances(&chain, auction_contract_address, token_contract_address);
    assert_eq!(balance_of_alice_and_auction_contract.0, [TokenAmountU64(99), TokenAmountU64(1)]);

    // Increment the chain time by 100000 milliseconds.
    chain.tick_block_time(Duration::from_millis(100000)).expect("Increment chain time");

    // Finalize the auction.
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
                message:      OwnedParameter::from_serial(&1u16).expect("Serialize parameter"),
            },
        )
        .expect("Should be able to finalize");

    // Check that the item is sold to ALICE.
    let item_state = view_item_state(&chain, auction_contract_address);
    assert_eq!(item_state.auction_state, AuctionState::Sold(ALICE));

    // Check that ALICE as creator got the payout when the auction ended.
    let balance_of_alice_and_auction_contract =
        get_balances(&chain, auction_contract_address, token_contract_address);
    assert_eq!(balance_of_alice_and_auction_contract.0, [TokenAmountU64(100), TokenAmountU64(0)]);
}

/// Get the `ItemState` at index 0.
fn view_item_state(chain: &Chain, auction_contract_address: ContractAddress) -> ItemState {
    // Invoke the view entry point.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "sponsored_tx_enabled_auction.viewItemState".to_string(),
            ),
            address:      auction_contract_address,
            message:      OwnedParameter::from_serial(&1u16).expect("Serialize parameter"),
        })
        .expect("Invoke viewItemState");

    invoke.parse_return_value().expect("ViewItemState return value")
}

/// Get the `TokenIdU8(1)` balances for Alice and the auction contract.
fn get_balances(
    chain: &Chain,
    auction_contract_address: ContractAddress,
    token_contract_address: ContractAddress,
) -> ContractBalanceOfQueryResponse {
    let balance_of_params: ContractBalanceOfQueryParams = BalanceOfQueryParams {
        queries: vec![
            BalanceOfQuery {
                token_id: TokenIdU8(1),
                address:  ALICE_ADDR,
            },
            BalanceOfQuery {
                token_id: TokenIdU8(1),
                address:  Address::from(auction_contract_address),
            },
        ],
    };

    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.balanceOf".to_string()),
            address:      token_contract_address,
            message:      OwnedParameter::from_serial(&balance_of_params)
                .expect("BalanceOf params"),
        })
        .expect("Invoke balanceOf");

    invoke.parse_return_value().expect("BalanceOf return value")
}

/// Setup auction and chain.
fn initialize_chain_and_auction() -> (Chain, AccountKeys, ContractAddress, ContractAddress) {
    let mut chain = Chain::builder().build().expect("Should be able to build chain");

    // Create keys for ALICE.
    let rng = &mut rand::thread_rng();

    let keypairs_alice = AccountKeys::singleton(rng);

    let balance = AccountBalance {
        total:  ACC_INITIAL_BALANCE,
        staked: Amount::zero(),
        locked: Amount::zero(),
    };

    // Create some accounts on the chain.
    chain.create_account(Account::new_with_keys(ALICE, balance, (&keypairs_alice).into()));
    chain.create_account(Account::new(BOB, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(CAROL, ACC_INITIAL_BALANCE));

    // Load and deploy the cis2 token module.
    let module =
        module_load_v1("../cis2-multi/concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, CAROL, module).expect("Deploy valid module");

    // Initialize the cis2 token contract.
    let token = chain
        .contract_init(SIGNER, CAROL, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_cis2_multi".to_string()),
            param:     OwnedParameter::from_serial(&TokenAmountU64(100u64))
                .expect("Serialize parameter"),
        })
        .expect("Initialize cis2 token contract");

    // Load and deploy the auction module.
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

    (chain, keypairs_alice, init_auction.contract_address, token.contract_address)
}
