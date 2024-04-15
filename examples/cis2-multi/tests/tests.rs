//! Tests for the `cis2_multi` contract.
use cis2_multi::{ContractBalanceOfQueryParams, ContractBalanceOfQueryResponse, *};
use concordium_cis2::*;
use concordium_smart_contract_testing::*;
use concordium_std::{
    collections::BTreeMap, AccountPublicKeys, AccountSignatures, CredentialSignatures, HashSha2256,
    SignatureEd25519, Timestamp,
};
use concordium_std_derive::*;

/// The tests accounts.
const ALICE: AccountAddress =
    account_address!("2wkBET2rRgE8pahuaczxKbmv7ciehqsne57F9gtzf1PVdr2VP3");
const ALICE_ADDR: Address = Address::Account(ALICE);
const BOB: AccountAddress = account_address!("2xBpaHottqhwFZURMZW4uZduQvpxNDSy46iXMYs9kceNGaPpZX");
const BOB_CANONICAL: AccountAddress = BOB.get_alias_unchecked(0);
const BOB_CANONICAL_ADDR: Address = Address::Account(BOB_CANONICAL);
const BOB_ADDR: Address = Address::Account(BOB);
const UPGRADER: AccountAddress =
    account_address!("2xdTv8awN1BjgYEw8W1BVXVtiEwG2b29U8KoZQqJrDuEqddseE");
const UPGRADER_ADDR: Address = Address::Account(UPGRADER);
const BLACKLISTER: AccountAddress =
    account_address!("2y57FyMyqAfY7X1SuSWJ5VMt1Z3ZgxbKt9w5mGoTwqA7YcpbXr");
const BLACKLISTER_ADDR: Address = Address::Account(BLACKLISTER);
const PAUSER: AccountAddress =
    account_address!("2yWkbp92JL9LYVmxgP1QfTDsJs9sMLAWJBYMy8md3SQz5ErzEd");
const PAUSER_ADDR: Address = Address::Account(PAUSER);
const NON_EXISTING_ACCOUNT: AccountAddress =
    account_address!("3hWv6hv4nrgPTUgjHehCHx6ifXUoCfWZepKuPykXEBmsgjzni4");

/// Token IDs.
const TOKEN_0: ContractTokenId = TokenIdU8(2);
const TOKEN_1: ContractTokenId = TokenIdU8(42);

/// Initial balance of the accounts.
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

/// A signer with one key.
const SIGNER: Signer = Signer::with_one_key();

/// Dummy signature used as placeholder.
const DUMMY_SIGNATURE: SignatureEd25519 = signature_ed25519!("00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000");

/// Test minting succeeds and the tokens are owned by the given address and
/// the appropriate events are logged.
#[test]
fn test_minting() {
    let (chain, _keypairs, contract_address, update, _module_reference) =
        initialize_contract_with_alice_tokens();

    // Invoke the view entrypoint and check that the tokens are owned by Alice.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.view".to_string()),
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
    let (mut chain, _keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

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
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.transfer".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect("Transfer tokens");

    // Check that Bob has 1 `TOKEN_0` and Alice has 99. Also check that Alice still
    // has 100 `TOKEN_1`.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.view".to_string()),
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
    let (mut chain, _keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

    // Add Bob as an operator for Alice.
    let params = UpdateOperatorParams(vec![UpdateOperator {
        update:   OperatorUpdate::Add,
        operator: BOB_ADDR,
    }]);

    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.updateOperator".to_string()),
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

    // Invoke the operatorOf entrypoint and check that Bob is an operator for
    // Alice.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.operatorOf".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&query_params).expect("OperatorOf params"),
        })
        .expect("Invoke opeatorOf");

    let rv: OperatorOfQueryResponse = invoke.parse_return_value().expect("OperatorOf return value");
    assert_eq!(rv, OperatorOfQueryResponse(vec![true]));
}

/// Test that a transfer fails when the sender is neither an operator or the
/// owner. In particular, Bob will attempt to transfer some of Alice's tokens to
/// himself.
#[test]
fn test_unauthorized_sender() {
    let (mut chain, _keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

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
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.transfer".to_string()),
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
    let (mut chain, _keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

    // Add Bob as an operator for Alice.
    let params = UpdateOperatorParams(vec![UpdateOperator {
        update:   OperatorUpdate::Add,
        operator: BOB_ADDR,
    }]);
    chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.updateOperator".to_string()),
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
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.transfer".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect("Transfer tokens");

    // Check that Bob now has 1 of `TOKEN_0` and Alice has 99. Also check that
    // Alice still has 100 `TOKEN_1`.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.view".to_string()),
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

/// Test permit mint function. The signature is generated in the test
/// case. ALICE mints tokens to her account.
#[test]
fn test_permit_mint() {
    let (mut chain, keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

    // Check balances in state.
    let balance_of_alice_and_bob = get_balances(&chain, contract_address);

    assert_eq!(balance_of_alice_and_bob.0, [TokenAmountU64(100), TokenAmountU64(0)]);

    // Create input parameters for the `mint` function.
    let payload = MintParams {
        owner:        ALICE_ADDR,
        metadata_url: MetadataUrl {
            url:  "https://some.example/token/2A".to_string(),
            hash: None,
        },
        token_id:     TOKEN_1,
    };

    let update =
        permit(&mut chain, contract_address, to_bytes(&payload), "mint".to_string(), keypairs);

    // Check that the correct events occurred.
    let events = update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect::<Vec<Event>>();

    assert_eq!(events, [
        Event::Cis2Event(Cis2Event::Mint(MintEvent {
            token_id: TOKEN_1,
            amount:   TokenAmountU64(100),
            owner:    ALICE_ADDR,
        })),
        Event::Cis2Event(Cis2Event::TokenMetadata(TokenMetadataEvent {
            token_id:     TOKEN_1,
            metadata_url: MetadataUrl {
                url:  "https://some.example/token/2A".to_string(),
                hash: None,
            },
        })),
        Event::Nonce(NonceEvent {
            account: ALICE,
            nonce:   0,
        })
    ]);

    // Check balances in state.
    let balance_of_alice_and_bob = get_balances(&chain, contract_address);

    assert_eq!(balance_of_alice_and_bob.0, [TokenAmountU64(200), TokenAmountU64(0)]);
}

/// Test permit burn function. The signature is generated in the test
/// case. ALICE burns tokens from her account.
#[test]
fn test_permit_burn() {
    let (mut chain, keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

    // Check balances in state.
    let balance_of_alice_and_bob = get_balances(&chain, contract_address);

    assert_eq!(balance_of_alice_and_bob.0, [TokenAmountU64(100), TokenAmountU64(0)]);

    // Create input parameters for the `burn` function.
    let payload = BurnParams {
        owner:    ALICE_ADDR,
        amount:   TokenAmountU64(1),
        token_id: TOKEN_1,
    };

    let update =
        permit(&mut chain, contract_address, to_bytes(&payload), "burn".to_string(), keypairs);

    // Check that the correct events occurred.
    let events = update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect::<Vec<Event>>();

    assert_eq!(events, [
        Event::Cis2Event(Cis2Event::Burn(BurnEvent {
            token_id: TOKEN_1,
            amount:   TokenAmountU64(1),
            owner:    ALICE_ADDR,
        })),
        Event::Nonce(NonceEvent {
            account: ALICE,
            nonce:   0,
        })
    ]);

    // Check balances in state.
    let balance_of_alice_and_bob = get_balances(&chain, contract_address);

    assert_eq!(balance_of_alice_and_bob.0, [TokenAmountU64(99), TokenAmountU64(0)]);
}

/// Test permit update operator function. The signature is generated in the test
/// case. ALICE adds BOB as an operator.
#[test]
fn test_permit_update_operator() {
    let (mut chain, keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

    // Check operator in state
    let bob_is_operator_of_alice = operator_of(&chain, contract_address);

    assert_eq!(bob_is_operator_of_alice, OperatorOfQueryResponse(vec![false]));

    // Create input parameters for the `permit` updateOperator function.
    let update_operator = UpdateOperator {
        update:   OperatorUpdate::Add,
        operator: BOB_ADDR,
    };
    let payload = UpdateOperatorParams(vec![update_operator]);

    let update = permit(
        &mut chain,
        contract_address,
        to_bytes(&payload),
        "updateOperator".to_string(),
        keypairs,
    );

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
fn test_permit_transfer() {
    let (mut chain, keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

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

    let update =
        permit(&mut chain, contract_address, to_bytes(&payload), "transfer".to_string(), keypairs);

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
    let (mut chain, keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

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
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.viewMessageHash".to_string()),
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
                receive_name: OwnedReceiveName::new_unchecked("cis2_multi.permit".to_string()),
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
                receive_name: OwnedReceiveName::new_unchecked("cis2_multi.nonceOf".to_string()),
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
    let (chain, keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

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
                receive_name: OwnedReceiveName::new_unchecked("cis2_multi.publicKeyOf".to_string()),
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

/// Test burning tokens.
#[test]
fn test_burning_tokens() {
    let (mut chain, _keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

    // Create input parameters to burn one of Alice's tokens.
    let burn_params = BurnParams {
        owner:    ALICE_ADDR,
        amount:   TokenAmountU64(1),
        token_id: TOKEN_1,
    };

    // Burn one of Alice's tokens.
    let update = chain
        .contract_update(
            Signer::with_one_key(),
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis2_multi.burn".to_string()),
                message:      OwnedParameter::from_serial(&burn_params)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to burn tokens");

    // Check that the event is logged.
    let events = update.events().flat_map(|(_addr, events)| events);

    let events: Vec<Cis2Event<ContractTokenId, ContractTokenAmount>> =
        events.map(|e| e.parse().expect("Deserialize event")).collect();

    assert_eq!(events, [Cis2Event::Burn(BurnEvent {
        owner:    ALICE_ADDR,
        amount:   TokenAmountU64(1),
        token_id: TOKEN_1,
    })]);

    // Check balances in state.
    let balance_of_alice_and_bob = get_balances(&chain, contract_address);

    assert_eq!(balance_of_alice_and_bob.0, [TokenAmountU64(99), TokenAmountU64(0)]);
}

/// Test adding and removing from blacklist works.
#[test]
fn test_adding_to_blacklist() {
    let (mut chain, _keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

    // Check that Alice and Bob are not blacklisted.
    let rv: Vec<bool> = is_blacklisted(&chain, contract_address);
    assert_eq!(rv, [false, false]);

    // Create input parameters to add Bob to the blacklist.
    let update_blacklist = UpdateBlacklist {
        update:  BlacklistUpdate::Add,
        address: BOB_ADDR,
    };
    let update_blacklist_params = UpdateBlacklistParams(vec![update_blacklist]);

    // Update blacklist.
    let update = chain
        .contract_update(
            Signer::with_one_key(),
            BLACKLISTER,
            BLACKLISTER_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "cis2_multi.updateBlacklist".to_string(),
                ),
                message:      OwnedParameter::from_serial(&update_blacklist_params)
                    .expect("Update blacklist params"),
            },
        )
        .expect("Should be able to update blacklist");

    // Check that the correct events occurred.
    let events = update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect::<Vec<Event>>();

    assert_eq!(events, [Event::UpdateBlacklist(UpdateBlacklistEvent {
        address: BOB_CANONICAL_ADDR,
        update:  BlacklistUpdate::Add,
    })]);

    // Check that Alice is not blacklisted and Bob is blacklisted.
    let rv: Vec<bool> = is_blacklisted(&chain, contract_address);
    assert_eq!(rv, [false, true]);

    // Create input parameters to remove Bob from the blacklist.
    let update_blacklist = UpdateBlacklist {
        update:  BlacklistUpdate::Remove,
        address: BOB_ADDR,
    };
    let update_blacklist_params = UpdateBlacklistParams(vec![update_blacklist]);

    // Update blacklist.
    let update = chain
        .contract_update(
            Signer::with_one_key(),
            BLACKLISTER,
            BLACKLISTER_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "cis2_multi.updateBlacklist".to_string(),
                ),
                message:      OwnedParameter::from_serial(&update_blacklist_params)
                    .expect("Update blacklist params"),
            },
        )
        .expect("Should be able to update blacklist");

    // Check that the correct events occurred.
    let events = update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect::<Vec<Event>>();

    assert_eq!(events, [Event::UpdateBlacklist(UpdateBlacklistEvent {
        address: BOB_CANONICAL_ADDR,
        update:  BlacklistUpdate::Remove,
    })]);

    // Check that Alice and Bob are not blacklisted.
    let rv: Vec<bool> = is_blacklisted(&chain, contract_address);
    assert_eq!(rv, [false, false]);
}

/// Test blacklisted address cannot receive tokens, send tokens, or burn tokens.
#[test]
fn test_token_balance_of_blacklisted_address_can_not_change() {
    let (mut chain, _keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

    // Send some tokens to Bob.
    let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::Account(BOB),
        token_id: TOKEN_0,
        amount:   TokenAmountU64(1),
        data:     AdditionalData::empty(),
    }]);

    let _update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.transfer".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect("Transfer tokens");

    // Create input parameters to add Bob to the blacklist.
    let update_blacklist = UpdateBlacklist {
        update:  BlacklistUpdate::Add,
        address: BOB_ADDR,
    };
    let update_blacklist_params = UpdateBlacklistParams(vec![update_blacklist]);

    // Update blacklist with BOB's address.
    let _update = chain
        .contract_update(
            Signer::with_one_key(),
            BLACKLISTER,
            BLACKLISTER_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "cis2_multi.updateBlacklist".to_string(),
                ),
                message:      OwnedParameter::from_serial(&update_blacklist_params)
                    .expect("Update blacklist params"),
            },
        )
        .expect("Should be able to update blacklist");

    // Bob cannot receive tokens via `transfer`.
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
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.transfer".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect_err("Transfer tokens");

    // Check that the correct error is returned.
    let rv: ContractError = update.parse_return_value().expect("ContractError return value");
    assert_eq!(rv, CustomContractError::Blacklisted.into());

    // Bob cannot transfer tokens via `transfer`.
    let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     BOB_ADDR,
        to:       Receiver::Account(ALICE),
        token_id: TOKEN_0,
        amount:   TokenAmountU64(1),
        data:     AdditionalData::empty(),
    }]);

    let update = chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.transfer".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect_err("Transfer tokens");

    // Check that the correct error is returned.
    let rv: ContractError = update.parse_return_value().expect("ContractError return value");
    assert_eq!(rv, CustomContractError::Blacklisted.into());

    // Bob cannot mint tokens to its address.
    let mint_params = MintParams {
        owner:        BOB_ADDR,
        token_id:     TOKEN_0,
        metadata_url: MetadataUrl {
            url:  "https://some.example/token/02".to_string(),
            hash: None,
        },
    };

    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.mint".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&mint_params).expect("Mint params"),
        })
        .expect_err("Mint tokens");

    // Check that the correct error is returned.
    let rv: ContractError = update.parse_return_value().expect("ContractError return value");
    assert_eq!(rv, CustomContractError::Blacklisted.into());

    // Bob cannot burn tokens from its address.
    let burn_params = BurnParams {
        owner:    BOB_ADDR,
        amount:   TokenAmountU64(1),
        token_id: TOKEN_1,
    };

    // Burn one of Alice's tokens.
    let update = chain
        .contract_update(
            Signer::with_one_key(),
            BOB,
            BOB_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis2_multi.burn".to_string()),
                message:      OwnedParameter::from_serial(&burn_params)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect_err("Burn tokens");

    // Check that the correct error is returned.
    let rv: ContractError = update.parse_return_value().expect("ContractError return value");
    assert_eq!(rv, CustomContractError::Blacklisted.into());
}

/// Upgrade the contract to itself without invoking a migration function.
#[test]
fn test_upgrade_without_migration_function() {
    let (mut chain, _keypairs, contract_address, _update, module_reference) =
        initialize_contract_with_alice_tokens();

    let input_parameter = UpgradeParams {
        module:  module_reference,
        migrate: None,
    };

    // Upgrade `contract_version1` to `contract_version2`.
    let update = chain.contract_update(
        Signer::with_one_key(),
        UPGRADER,
        UPGRADER_ADDR,
        Energy::from(10000),
        UpdateContractPayload {
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.upgrade".into()),
            message:      OwnedParameter::from_serial(&input_parameter)
                .expect("`UpgradeParams` should be a valid inut parameter"),
            amount:       Amount::from_ccd(0),
        },
    );

    assert!(
        !update.expect("Upgrade should succeed").state_changed,
        "State should not be changed because no `migration` function was called"
    );

    // Invoke the view entrypoint and check that the state of the contract can be
    // read.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.view".to_string()),
            address:      contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");

    // Check that the tokens (as set up in the
    // `initialize_contract_with_alice_tokens` function) are owned by Alice.
    let rv: ViewState = invoke.parse_return_value().expect("ViewState return value");
    assert_eq!(rv.tokens[..], [TOKEN_0, TOKEN_1]);
    assert_eq!(rv.state, vec![(ALICE_ADDR, ViewAddressState {
        balances:  vec![(TOKEN_0, 100.into()), (TOKEN_1, 100.into())],
        operators: Vec::new(),
    })]);
}

/// Test that the pause/unpause entrypoints correctly sets the pause value in
/// the state.
#[test]
fn test_pause_functionality() {
    let (mut chain, _keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

    // Pause the contract.
    chain
        .contract_update(SIGNER, PAUSER, PAUSER_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.setPaused".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&true).expect("Pause params"),
        })
        .expect("Pause");

    // Check that the contract is now paused.
    assert_eq!(invoke_view(&mut chain, contract_address).paused, true);

    // Unpause the contract.
    chain
        .contract_update(SIGNER, PAUSER, PAUSER_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.setPaused".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&false).expect("Unpause params"),
        })
        .expect("Unpause");
    // Check that the contract is now unpaused.
    assert_eq!(invoke_view(&mut chain, contract_address).paused, false);
}

/// Test that only the PAUSER can pause/unpause the contract.
#[test]
fn test_pause_unpause_unauthorized() {
    let (mut chain, _keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

    // Pause the contract as Bob, who is not the PAUSER.
    let update = chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.setPaused".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&true).expect("Pause params"),
        })
        .expect_err("Pause");

    // Check that the correct error is returned.
    let rv: ContractError = update.parse_return_value().expect("ContractError return value");
    assert_eq!(rv, ContractError::Unauthorized);
}

/// Test that one can NOT call non-admin state-mutative functions (burn,
/// mint, transfer, updateOperator) when the contract is paused.
#[test]
fn test_no_execution_of_state_mutative_functions_when_paused() {
    let (mut chain, _keypairs, contract_address, _update, _module_reference) =
        initialize_contract_with_alice_tokens();

    // Pause the contract.
    chain
        .contract_update(SIGNER, PAUSER, PAUSER_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.setPaused".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&true).expect("Pause params"),
        })
        .expect("Pause");

    // Try to transfer 1 token from Alice to Bob.
    let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::Account(BOB),
        token_id: TOKEN_0,
        amount:   TokenAmountU64(1),
        data:     AdditionalData::empty(),
    }]);
    let update_transfer = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.transfer".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect_err("Transfer tokens");
    assert_contract_paused_error(&update_transfer);

    // Try to add Bob as an operator for Alice.
    let params = UpdateOperatorParams(vec![UpdateOperator {
        update:   OperatorUpdate::Add,
        operator: BOB_ADDR,
    }]);
    let update_operator = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.updateOperator".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&params).expect("UpdateOperator params"),
        })
        .expect_err("Update operator");
    assert_contract_paused_error(&update_operator);

    // Try to mint tokens.
    let params = MintParams {
        owner:        ALICE_ADDR,
        metadata_url: MetadataUrl {
            url:  "https://some.example/token/02".to_string(),
            hash: None,
        },
        token_id:     TOKEN_0,
    };

    let update_operator = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.mint".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&params).expect("Mint params"),
        })
        .expect_err("Update operator");
    assert_contract_paused_error(&update_operator);

    // Try to burn tokens.
    let params = BurnParams {
        owner:    ALICE_ADDR,
        amount:   TokenAmountU64(1),
        token_id: TOKEN_0,
    };

    let update_operator = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.burn".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&params).expect("Burn params"),
        })
        .expect_err("Update operator");
    assert_contract_paused_error(&update_operator);
}

/// Check that the returned error is `ContractPaused`.
fn assert_contract_paused_error(update: &ContractInvokeError) {
    let rv: ContractError = update.parse_return_value().expect("ContractError return value");
    assert_eq!(rv, ContractError::Custom(CustomContractError::Paused));
}

/// Get the result of the view entrypoint.
fn invoke_view(chain: &mut Chain, contract_address: ContractAddress) -> ViewState {
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.view".to_string()),
            address:      contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");
    invoke.parse_return_value().expect("Return value")
}

/// Execute a permit function invoke
fn permit(
    chain: &mut Chain,
    contract_address: ContractAddress,
    payload: Vec<u8>,
    entrypoint_name: String,
    keypairs: AccountKeys,
) -> ContractInvokeSuccess {
    // The `viewMessageHash` function uses the same input parameter `PermitParam` as
    // the `permit` function. The `PermitParam` type includes a `signature` and
    // a `signer`. Because these two values (`signature` and `signer`) are not
    // read in the `viewMessageHash` function, any value can be used and we choose
    // to use `DUMMY_SIGNATURE` and `ALICE` in the test case below.
    let signature_map = BTreeMap::from([(0u8, CredentialSignatures {
        sigs: BTreeMap::from([(0u8, concordium_std::Signature::Ed25519(DUMMY_SIGNATURE))]),
    })]);

    let mut param = PermitParam {
        signature: AccountSignatures {
            sigs: signature_map,
        },
        signer:    ALICE,
        message:   PermitMessage {
            timestamp: Timestamp::from_timestamp_millis(10_000_000_000),
            contract_address: ContractAddress::new(0, 0),
            entry_point: OwnedEntrypointName::new_unchecked(entrypoint_name),
            nonce: 0,
            payload,
        },
    };

    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.viewMessageHash".to_string()),
            message:      OwnedParameter::from_serial(&param)
                .expect("Should be a valid inut parameter"),
        })
        .expect("Should be able to query viewMessageHash");

    let message_hash: HashSha2256 =
        from_bytes(&invoke.return_value).expect("Should return a valid result");

    param.signature = keypairs.sign_message(&to_bytes(&message_hash));

    // Execute permit function.
    chain
        .contract_update(
            Signer::with_one_key(),
            BOB,
            BOB_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis2_multi.permit".to_string()),
                message:      OwnedParameter::from_serial(&param)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to exit permit token with permit")
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
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.operatorOf".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&operator_of_params)
                .expect("OperatorOf params"),
        })
        .expect("Invoke operatorOf");
    let rv: OperatorOfQueryResponse = invoke.parse_return_value().expect("OperatorOf return value");
    rv
}

/// Check if Alice and Bob are blacklisted.
fn is_blacklisted(chain: &Chain, contract_address: ContractAddress) -> Vec<bool> {
    let addresses_query_vector = VecOfAddresses {
        queries: vec![ALICE_ADDR, BOB_ADDR],
    };

    // Invoke the isBlacklisted entrypoint.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.isBlacklisted".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&addresses_query_vector)
                .expect("Should be a valid inut parameter"),
        })
        .expect("Invoke isBlacklisted");

    let rv: Vec<bool> = invoke.parse_return_value().expect("Vec<bool> return value");
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
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.balanceOf".to_string()),
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
/// Alice. She has 100 of `TOKEN_0` and 100 of `TOKEN_1`.
/// Alice's account is created with keys.
/// Hence, Alice's account signature can be checked in the test cases.
fn initialize_contract_with_alice_tokens(
) -> (Chain, AccountKeys, ContractAddress, ContractInvokeSuccess, ModuleReference) {
    let (mut chain, keypairs, contract_address, module_reference) = initialize_chain_and_contract();

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
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.mint".to_string()),
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
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.mint".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&mint_params).expect("Mint params"),
        })
        .expect("Mint tokens");

    (chain, keypairs, contract_address, update, module_reference)
}

/// Setup chain and contract.
/// The function creates the five accounts: ALICE, BOB, UPGRADER, PAUSER, and
/// BLACKLISTER. The function grants ALICE the ADMIN role, the UPGRADER the
/// UPGRADE role, and the BLACKLISTER the BLACKLISTE role.
fn initialize_chain_and_contract() -> (Chain, AccountKeys, ContractAddress, ModuleReference) {
    let mut chain = Chain::new();

    let rng = &mut rand::thread_rng();

    let keypairs = AccountKeys::singleton(rng);

    let balance = AccountBalance {
        total:  ACC_INITIAL_BALANCE,
        staked: Amount::zero(),
        locked: Amount::zero(),
    };

    // Create some accounts on the chain.
    chain.create_account(Account::new_with_keys(ALICE, balance, (&keypairs).into()));
    chain.create_account(Account::new(BOB, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(UPGRADER, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(BLACKLISTER, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(PAUSER, ACC_INITIAL_BALANCE));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, ALICE, module).expect("Deploy valid module");

    // Initialize the auction contract.
    let init = chain
        .contract_init(SIGNER, ALICE, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_cis2_multi".to_string()),
            param:     OwnedParameter::from_serial(&TokenAmountU64(100)).expect("Init params"),
        })
        .expect("Initialize contract");

    // Grant UPGRADER role
    let grant_role_params = GrantRoleParams {
        address: UPGRADER_ADDR,
        role:    Roles::UPGRADER,
    };

    let _update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.grantRole".to_string()),
            address:      init.contract_address,
            message:      OwnedParameter::from_serial(&grant_role_params)
                .expect("GrantRole params"),
        })
        .expect("UPGRADER should be granted role");

    // Grant PAUSER role
    let grant_role_params = GrantRoleParams {
        address: PAUSER_ADDR,
        role:    Roles::PAUSER,
    };

    let _update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.grantRole".to_string()),
            address:      init.contract_address,
            message:      OwnedParameter::from_serial(&grant_role_params)
                .expect("GrantRole params"),
        })
        .expect("PAUSER should be granted role");

    // Grant BLACKLISTER role
    let grant_role_params = GrantRoleParams {
        address: BLACKLISTER_ADDR,
        role:    Roles::BLACKLISTER,
    };

    let _update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.grantRole".to_string()),
            address:      init.contract_address,
            message:      OwnedParameter::from_serial(&grant_role_params)
                .expect("GrantRole params"),
        })
        .expect("BLACKLISTER should be granted role");

    (chain, keypairs, init.contract_address, deployment.module_reference)
}
