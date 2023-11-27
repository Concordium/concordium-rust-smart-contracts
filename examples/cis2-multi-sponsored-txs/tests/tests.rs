//! Tests for the `cis2_multi` contract.
use cis2_multi_sponsored_txs::{ContractBalanceOfQueryParams, ContractBalanceOfQueryResponse, *};
use concordium_cis2::*;
use concordium_smart_contract_testing::*;
use concordium_std::{
    collections::BTreeMap, AccountPublicKeys, AccountSignatures, CredentialSignatures, HashSha2256,
    SignatureEd25519, Timestamp,
};

/// The tests accounts.
const ALICE: AccountAddress = AccountAddress([0; 32]);
const ALICE_ADDR: Address = Address::Account(ALICE);
const BOB: AccountAddress = AccountAddress([1; 32]);
const BOB_ADDR: Address = Address::Account(BOB);
const NON_EXISTING_ACCOUNT: AccountAddress = AccountAddress([2u8; 32]);

/// Token IDs.
const TOKEN_0: ContractTokenId = TokenIdU8(2);
const TOKEN_1: ContractTokenId = TokenIdU8(42);

/// Initial balance of the accounts.
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

/// A signer for all the transactions.
const SIGNER: Signer = Signer::with_one_key();

const DUMMY_SIGNATURE: SignatureEd25519 = SignatureEd25519([
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
]);

/// Test minting succeeds and the tokens are owned by the given address and
/// the appropriate events are logged.
#[test]
fn test_minting() {
    let (chain, _keypairs, contract_address, update) = initialize_contract_with_alice_tokens();

    // Invoke the view entrypoint and check that the tokens are owned by Alice.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.view".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");

    // Check that the tokens are owned by Alice.
    let rv: ViewState = invoke.parse_return_value().expect("ViewState return value");
    assert_eq!(rv.tokens[..], [TOKEN_0, TOKEN_1]);
    assert_eq!(rv.state, vec![(ALICE_ADDR, ViewAddressState {
        balances:  vec![(TOKEN_0, 100.into()), (TOKEN_1, 100.into())],
        operators: Vec::new(),
    })]);

    // Check that the events are logged.
    let events = update.events().flat_map(|(_addr, events)| events);

    let events: Vec<Cis2Event<ContractTokenId, ContractTokenAmount>> =
        events.map(|e| e.parse().expect("Deserialize event")).collect();

    assert_eq!(events, [
        Cis2Event::Mint(MintEvent {
            token_id: TokenIdU8(42),
            amount:   TokenAmountU64(100),
            owner:    ALICE_ADDR,
        }),
        Cis2Event::TokenMetadata(TokenMetadataEvent {
            token_id:     TokenIdU8(42),
            metadata_url: MetadataUrl {
                url:  "https://some.example/token/2A".to_string(),
                hash: None,
            },
        }),
    ]);
}

/// Test regular transfer where sender is the owner.
#[test]
fn test_account_transfer() {
    let (mut chain, _keypairs, contract_address, _update) = initialize_contract_with_alice_tokens();

    // Transfer one token from Alice to Bob.
    let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::Account(BOB),
        token_id: TOKEN_0,
        amount:   TokenAmountU64(1),
        data:     AdditionalData::empty(),
    }]);

    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.transfer".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect("Transfer tokens");

    // Check that Bob has 1 `TOKEN_0` and Alice has 399. Also check that Alice still
    // has 1 `TOKEN_1`.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.view".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");
    let rv: ViewState = invoke.parse_return_value().expect("ViewState return value");
    assert_eq!(rv.state, vec![
        (ALICE_ADDR, ViewAddressState {
            balances:  vec![(TOKEN_0, 99.into()), (TOKEN_1, 100.into())],
            operators: Vec::new(),
        }),
        (BOB_ADDR, ViewAddressState {
            balances:  vec![(TOKEN_0, 1.into())],
            operators: Vec::new(),
        }),
    ]);

    // Check that the events are logged.
    let events = update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect::<Vec<Cis2Event<_, _>>>();

    assert_eq!(events, [Cis2Event::Transfer(TransferEvent {
        token_id: TOKEN_0,
        amount:   TokenAmountU64(1),
        from:     ALICE_ADDR,
        to:       BOB_ADDR,
    }),]);
}

/// Test that you can add an operator.
/// Initialize the contract with two tokens owned by Alice.
/// Then add Bob as an operator for Alice.
#[test]
fn test_add_operator() {
    let (mut chain, _keypairs, contract_address, _update) = initialize_contract_with_alice_tokens();

    // Add Bob as an operator for Alice.
    let params = UpdateOperatorParams(vec![UpdateOperator {
        update:   OperatorUpdate::Add,
        operator: BOB_ADDR,
    }]);

    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.updateOperator".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&params).expect("UpdateOperator params"),
        })
        .expect("Update operator");

    // Check that an operator event occurred.
    let events = update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect::<Vec<Cis2Event<ContractTokenId, ContractTokenAmount>>>();
    assert_eq!(events, [Cis2Event::UpdateOperator(UpdateOperatorEvent {
        operator: BOB_ADDR,
        owner:    ALICE_ADDR,
        update:   OperatorUpdate::Add,
    }),]);

    // Construct a query parameter to check whether Bob is an operator for Alice.
    let query_params = OperatorOfQueryParams {
        queries: vec![OperatorOfQuery {
            owner:   ALICE_ADDR,
            address: BOB_ADDR,
        }],
    };

    // Invoke the operatorOf view entrypoint and check that Bob is an operator for
    // Alice.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.operatorOf".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&query_params).expect("OperatorOf params"),
        })
        .expect("Invoke view");

    let rv: OperatorOfQueryResponse = invoke.parse_return_value().expect("OperatorOf return value");
    assert_eq!(rv, OperatorOfQueryResponse(vec![true]));
}

/// Test that a transfer fails when the sender is neither an operator or the
/// owner. In particular, Bob will attempt to transfer some of Alice's tokens to
/// himself.
#[test]
fn test_unauthorized_sender() {
    let (mut chain, _keypairs, contract_address, _update) = initialize_contract_with_alice_tokens();

    // Construct a transfer of `TOKEN_0` from Alice to Bob, which will be submitted
    // by Bob.
    let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::Account(BOB),
        token_id: TOKEN_0,
        amount:   TokenAmountU64(1),
        data:     AdditionalData::empty(),
    }]);

    // Notice that Bob is the sender/invoker.
    let update = chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.transfer".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect_err("Transfer tokens");

    // Check that the correct error is returned.
    let rv: ContractError = update.parse_return_value().expect("ContractError return value");
    assert_eq!(rv, ContractError::Unauthorized);
}

/// Test that an operator can make a transfer.
#[test]
fn test_operator_can_transfer() {
    let (mut chain, _keypairs, contract_address, _update) = initialize_contract_with_alice_tokens();

    // Add Bob as an operator for Alice.
    let params = UpdateOperatorParams(vec![UpdateOperator {
        update:   OperatorUpdate::Add,
        operator: BOB_ADDR,
    }]);
    chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.updateOperator".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&params).expect("UpdateOperator params"),
        })
        .expect("Update operator");

    // Let Bob make a transfer to himself on behalf of Alice.
    let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::Account(BOB),
        token_id: TOKEN_0,
        amount:   TokenAmountU64(1),
        data:     AdditionalData::empty(),
    }]);

    chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.transfer".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect("Transfer tokens");

    // Check that Bob now has 1 of `TOKEN_0` and Alice has 399. Also check that
    // Alice still has 1 `TOKEN_1`.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.view".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");
    let rv: ViewState = invoke.parse_return_value().expect("ViewState return value");
    assert_eq!(rv.state, vec![
        (ALICE_ADDR, ViewAddressState {
            balances:  vec![(TOKEN_0, 99.into()), (TOKEN_1, 100.into())],
            operators: vec![BOB_ADDR],
        }),
        (BOB_ADDR, ViewAddressState {
            balances:  vec![(TOKEN_0, 1.into())],
            operators: Vec::new(),
        }),
    ]);
}

/// Test permit update operator function. The signature is generated in the test
/// case. ALICE adds BOB as an operator.
#[test]
fn test_inside_signature_permit_update_operator() {
    let (mut chain, keypairs, contract_address, _update) = initialize_contract_with_alice_tokens();

    // Check operator in state
    let bob_is_operator_of_alice = operator_of(&chain, contract_address);

    assert_eq!(bob_is_operator_of_alice, OperatorOfQueryResponse(vec![false]));

    // Create input parameters for the `permit` updateOperator function.
    let update_operator = UpdateOperator {
        update:   OperatorUpdate::Add,
        operator: BOB_ADDR,
    };
    let payload = UpdateOperatorParams(vec![update_operator]);

    // The `viewMessageHash` function uses the same input parameter `PermitParam` as
    // the `permit` function. The `PermitParam` type includes a `signature` and
    // a `signer`. Because these two values (`signature` and `signer`) are not
    // read in the `viewMessageHash` function, any value can be used and we choose
    // to use `DUMMY_SIGNATURE` and `ALICE` in the test case below.
    let signature_map = BTreeMap::from([(0u8, CredentialSignatures {
        sigs: BTreeMap::from([(0u8, concordium_std::Signature::Ed25519(DUMMY_SIGNATURE))]),
    })]);

    let mut permit_update_operator_param = PermitParam {
        signature: AccountSignatures {
            sigs: signature_map,
        },
        signer:    ALICE,
        message:   PermitMessage {
            timestamp:        Timestamp::from_timestamp_millis(10_000_000_000),
            contract_address: ContractAddress::new(0, 0),
            entry_point:      OwnedEntrypointName::new_unchecked("updateOperator".into()),
            nonce:            0,
            payload:          to_bytes(&payload),
        },
    };

    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.viewMessageHash".to_string(),
            ),
            message:      OwnedParameter::from_serial(&permit_update_operator_param)
                .expect("Should be a valid inut parameter"),
        })
        .expect("Should be able to query viewMessageHash");

    let message_hash: HashSha2256 =
        from_bytes(&invoke.return_value).expect("Should return a valid result");

    permit_update_operator_param.signature = keypairs.sign_message(&to_bytes(&message_hash));

    // Update operator with the permit function.
    let update = chain
        .contract_update(
            Signer::with_one_key(),
            BOB,
            Address::Account(BOB),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "cis2_multi_sponsored_txs.permit".to_string(),
                ),
                message:      OwnedParameter::from_serial(&permit_update_operator_param)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to update operator with permit");

    // Check that the correct events occurred.
    let events = update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect::<Vec<Event>>();

    assert_eq!(events, [
        Event::Cis2Event(Cis2Event::UpdateOperator(UpdateOperatorEvent {
            update:   OperatorUpdate::Add,
            owner:    ALICE_ADDR,
            operator: BOB_ADDR,
        })),
        Event::Nonce(NonceEvent {
            account: ALICE,
            nonce:   0,
        })
    ]);

    // Check operator in state
    let bob_is_operator_of_alice = operator_of(&chain, contract_address);

    assert_eq!(bob_is_operator_of_alice, OperatorOfQueryResponse(vec![true]));
}

/// Test permit transfer function. The signature is generated in the test case.
/// TOKEN_1 is transferred from Alice to Bob.
#[test]
fn test_inside_signature_permit_transfer() {
    let (mut chain, keypairs, contract_address, _update) = initialize_contract_with_alice_tokens();

    // Check balances in state.
    let balance_of_alice_and_bob = get_balances(&chain, contract_address);

    assert_eq!(balance_of_alice_and_bob.0, [TokenAmountU64(100), TokenAmountU64(0)]);

    // Create input parameters for the `permit` transfer function.
    let transfer = concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::from_account(BOB),
        token_id: TOKEN_1,
        amount:   ContractTokenAmount::from(1),
        data:     AdditionalData::empty(),
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
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.viewMessageHash".to_string(),
            ),
            message:      OwnedParameter::from_serial(&permit_transfer_param)
                .expect("Should be a valid inut parameter"),
        })
        .expect("Should be able to query viewMessageHash");

    let message_hash: HashSha2256 =
        from_bytes(&invoke.return_value).expect("Should return a valid result");

    permit_transfer_param.signature = keypairs.sign_message(&to_bytes(&message_hash));

    // Transfer token with the permit function.
    let update = chain
        .contract_update(
            Signer::with_one_key(),
            BOB,
            BOB_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "cis2_multi_sponsored_txs.permit".to_string(),
                ),
                message:      OwnedParameter::from_serial(&permit_transfer_param)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to transfer token with permit");

    // Check that the correct events occurred.
    let events = update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect::<Vec<Event>>();

    assert_eq!(events, [
        Event::Cis2Event(Cis2Event::Transfer(TransferEvent {
            token_id: TOKEN_1,
            amount:   ContractTokenAmount::from(1),
            from:     ALICE_ADDR,
            to:       BOB_ADDR,
        })),
        Event::Nonce(NonceEvent {
            account: ALICE,
            nonce:   0,
        })
    ]);

    // Check balances in state.
    let balance_of_alice_and_bob = get_balances(&chain, contract_address);

    assert_eq!(balance_of_alice_and_bob.0, [TokenAmountU64(99), TokenAmountU64(1)]);
}

// Test `nonceOf` query. We check that the nonce of `ALICE` is 1 when
/// the account already sent one sponsored transaction. We check that the nonce
/// of `BOB` is 0 when the account did not send any sponsored
/// transaction. We check that the nonce of `NON_EXISTING_ACCOUNT` is 0.
#[test]
fn test_nonce_of_query() {
    let (mut chain, keypairs, contract_address, _update) = initialize_contract_with_alice_tokens();

    // To increase the nonce of `ALICE's` account, we invoke the
    // `update_permit` function with a valid signature from ALICE account.

    // Create input parameters for the `permit` updateOperator function.
    let update_operator = UpdateOperator {
        update:   OperatorUpdate::Add,
        operator: BOB_ADDR,
    };
    let payload = UpdateOperatorParams(vec![update_operator]);

    let mut inner_signature_map = BTreeMap::new();

    // The `viewMessageHash` function uses the same input parameter `PermitParam` as
    // the `permit` function. The `PermitParam` type includes a `signature` and
    // a `signer`. Because these two values (`signature` and `signer`) are not
    // read in the `viewMessageHash` function, any value can be used and we choose
    // to use `DUMMY_SIGNATURE` and `ALICE` in the test case below.
    inner_signature_map.insert(0u8, concordium_std::Signature::Ed25519(DUMMY_SIGNATURE));

    let mut signature_map = BTreeMap::new();
    signature_map.insert(0u8, CredentialSignatures {
        sigs: inner_signature_map,
    });

    let mut permit_update_operator_param = PermitParam {
        signature: AccountSignatures {
            sigs: signature_map,
        },
        signer:    ALICE,
        message:   PermitMessage {
            timestamp:        Timestamp::from_timestamp_millis(10_000_000_000),
            contract_address: ContractAddress::new(0, 0),
            entry_point:      OwnedEntrypointName::new_unchecked("updateOperator".into()),
            nonce:            0,
            payload:          to_bytes(&payload),
        },
    };

    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.viewMessageHash".to_string(),
            ),
            message:      OwnedParameter::from_serial(&permit_update_operator_param)
                .expect("Should be a valid inut parameter"),
        })
        .expect("Should be able to query viewMessageHash");

    let message_hash: HashSha2256 =
        from_bytes(&invoke.return_value).expect("Should return a valid result");

    permit_update_operator_param.signature = keypairs.sign_message(&to_bytes(&message_hash));

    // Update operator with the permit function.
    let _update = chain
        .contract_update(
            Signer::with_one_key(),
            BOB,
            Address::Account(BOB),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "cis2_multi_sponsored_txs.permit".to_string(),
                ),
                message:      OwnedParameter::from_serial(&permit_update_operator_param)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to update operator with permit");

    // Check if correct nonces are returned by the `nonceOf` function.
    let nonce_query_vector = VecOfAccountAddresses {
        queries: vec![ALICE, BOB, NON_EXISTING_ACCOUNT],
    };

    let invoke = chain
        .contract_invoke(
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "cis2_multi_sponsored_txs.nonceOf".to_string(),
                ),
                message:      OwnedParameter::from_serial(&nonce_query_vector)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to query publicKeyOf");

    let nonces: NonceOfQueryResponse =
        from_bytes(&invoke.return_value).expect("Should return a valid result");

    assert_eq!(
        nonces.0[0], 1,
        "Nonce of ALICE should be 1 because the account already sent one sponsored transaction"
    );
    assert_eq!(
        nonces.0[1], 0,
        "Nonce of BOB should be 0 because the account did not send any sponsored transaction"
    );
    assert_eq!(nonces.0[2], 0, "Nonce of non-existing account should be 0");
}

/// Test `publicKeyOf` query. `ALICE` should have its correct keys
/// returned. `NON_EXISTING_ACCOUNT` should have `None` returned because it does
/// not exist on chain.
#[test]
fn test_public_key_of_query() {
    let (chain, keypairs, contract_address, _update) = initialize_contract_with_alice_tokens();

    let public_key_of_query_vector = VecOfAccountAddresses {
        queries: vec![ALICE, NON_EXISTING_ACCOUNT],
    };

    let invoke = chain
        .contract_invoke(
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "cis2_multi_sponsored_txs.publicKeyOf".to_string(),
                ),
                message:      OwnedParameter::from_serial(&public_key_of_query_vector)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to query publicKeyOf");

    let public_keys_of: PublicKeyOfQueryResponse =
        from_bytes(&invoke.return_value).expect("Should return a valid result");

    let account_public_keys: AccountPublicKeys = (keypairs).into();

    assert_eq!(
        public_keys_of.0[0],
        Some(account_public_keys),
        "An existing account should have correct public keys returned"
    );
    assert!(public_keys_of.0[1].is_none(), "Non existing account should have no public keys");
}

/// Check if Bob is an operator of Alice.
fn operator_of(chain: &Chain, contract_address: ContractAddress) -> OperatorOfQueryResponse {
    let operator_of_params = OperatorOfQueryParams {
        queries: vec![OperatorOfQuery {
            address: BOB_ADDR,
            owner:   ALICE_ADDR,
        }],
    };

    // Check operator in state
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.operatorOf".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&operator_of_params)
                .expect("OperatorOf params"),
        })
        .expect("Invoke operatorOf");
    let rv: OperatorOfQueryResponse = invoke.parse_return_value().expect("OperatorOf return value");
    rv
}

/// Get the `TOKEN_1` balances for Alice and Bob.
fn get_balances(
    chain: &Chain,
    contract_address: ContractAddress,
) -> ContractBalanceOfQueryResponse {
    let balance_of_params = ContractBalanceOfQueryParams {
        queries: vec![
            BalanceOfQuery {
                token_id: TOKEN_1,
                address:  ALICE_ADDR,
            },
            BalanceOfQuery {
                token_id: TOKEN_1,
                address:  BOB_ADDR,
            },
        ],
    };

    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.balanceOf".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&balance_of_params)
                .expect("BalanceOf params"),
        })
        .expect("Invoke balanceOf");
    let rv: ContractBalanceOfQueryResponse =
        invoke.parse_return_value().expect("BalanceOf return value");
    rv
}

/// Helper function that sets up the contract with two types of tokens minted to
/// Alice. She has 400 of `TOKEN_0` and 1 of `TOKEN_1`.
fn initialize_contract_with_alice_tokens(
) -> (Chain, AccountKeys, ContractAddress, ContractInvokeSuccess) {
    let (mut chain, keypairs, contract_address) = initialize_chain_and_contract();

    let mint_params = MintParams {
        owner:        ALICE_ADDR,
        token_id:     TOKEN_0,
        metadata_url: MetadataUrl {
            url:  "https://some.example/token/02".to_string(),
            hash: None,
        },
    };

    // Mint/airdrop TOKEN_0 to Alice as the owner.
    let _update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.mint".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&mint_params).expect("Mint params"),
        })
        .expect("Mint tokens");

    let mint_params = MintParams {
        owner:        ALICE_ADDR,
        token_id:     TOKEN_1,
        metadata_url: MetadataUrl {
            url:  "https://some.example/token/2A".to_string(),
            hash: None,
        },
    };

    // Mint/airdrop TOKEN_1 to Alice as the owner.
    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_sponsored_txs.mint".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&mint_params).expect("Mint params"),
        })
        .expect("Mint tokens");

    (chain, keypairs, contract_address, update)
}

/// Setup chain and contract.
///
/// Also creates the two accounts, Alice and Bob.
///
/// Alice is the owner of the contract.
fn initialize_chain_and_contract() -> (Chain, AccountKeys, ContractAddress) {
    let mut chain = Chain::new();

    let rng = &mut rand::thread_rng();

    let keypairs = AccountKeys::singleton(rng);

    let balance = AccountBalance {
        total:  ACC_INITIAL_BALANCE,
        staked: Amount::zero(),
        locked: Amount::zero(),
    };

    // Create some accounts accounts on the chain.
    chain.create_account(Account::new_with_keys(ALICE, balance, (&keypairs).into()));
    chain.create_account(Account::new(BOB, ACC_INITIAL_BALANCE));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, ALICE, module).expect("Deploy valid module");

    // Initialize the auction contract.
    let init = chain
        .contract_init(SIGNER, ALICE, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked(
                "init_cis2_multi_sponsored_txs".to_string(),
            ),
            param:     OwnedParameter::empty(),
        })
        .expect("Initialize contract");

    (chain, keypairs, init.contract_address)
}
