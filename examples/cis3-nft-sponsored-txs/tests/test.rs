//! This module contains integration tests for the cis3-sponsored-transaction
//! contract. To run them, use `cargo test`.
use cis3_nft_sponsored_txs::{
    ContractTokenAmount, ContractTokenId, MintParams, NonceEvent, NonceOfQueryResponse,
    PermitMessage, PermitParam, PublicKeyOfQueryResponse, VecOfAccountAddresses, NONCE_EVENT_TAG,
};
use concordium_cis2::{TokenIdU32, *};
use concordium_smart_contract_testing::{AccountAccessStructure, *};
use concordium_std::{
    AccountPublicKeys, AccountSignatures, CredentialSignatures, PublicKey, SignatureEd25519,
    Timestamp,
};
use std::collections::BTreeMap;

const ACC_ADDR_OWNER: AccountAddress = AccountAddress([0u8; 32]);
const ADDR_OWNER: Address = Address::Account(ACC_ADDR_OWNER);
const ACC_ADDR_OTHER: AccountAddress = AccountAddress([1u8; 32]);
const ADDR_OTHER: Address = Address::Account(ACC_ADDR_OTHER);
const NON_EXISTING_ACCOUNT: AccountAddress = AccountAddress([2u8; 32]);
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(1000);

const TOKEN_1: TokenIdU32 = TokenIdU32(1);

// Private key: 8ECA45107A878FB879B84401084B55AD4919FC0F7D14E8915D8A5989B1AE1C01
const PUBLIC_KEY: [u8; 32] = [
    120, 154, 141, 6, 248, 239, 77, 224, 80, 62, 139, 136, 211, 204, 105, 208, 26, 11, 2, 208, 195,
    253, 29, 192, 126, 199, 208, 39, 69, 4, 246, 32,
];

const SIGNATURE_TRANSFER: SignatureEd25519 = SignatureEd25519([
    46, 96, 133, 143, 232, 24, 149, 54, 217, 245, 162, 135, 64, 125, 32, 61, 209, 147, 240, 151,
    19, 244, 137, 244, 91, 59, 120, 202, 39, 201, 82, 39, 64, 210, 250, 183, 187, 27, 147, 50, 31,
    88, 78, 79, 78, 135, 192, 72, 38, 234, 90, 226, 89, 75, 124, 86, 1, 190, 196, 195, 248, 19,
    181, 11,
]);

const SIGNATURE_UPDATE_OPERATOR: SignatureEd25519 = SignatureEd25519([
    50, 83, 36, 119, 75, 223, 109, 182, 152, 68, 46, 46, 249, 11, 169, 109, 51, 211, 47, 56, 60,
    155, 62, 59, 70, 8, 107, 72, 147, 141, 226, 153, 43, 234, 82, 164, 168, 43, 202, 244, 213, 95,
    101, 101, 155, 226, 130, 77, 47, 243, 161, 219, 100, 208, 106, 109, 102, 189, 171, 159, 22,
    179, 148, 0,
]);

/// A helper method for setting up:
///  - The chain,
///  - The two accounts `ACC_ADDR_OWNER` and `ACC_ADDR_OTHER`, both with
///    `ACC_INITIAL_BALANCE` CCD. `ACC_ADDR_OTHER` will be set up with valid
///    public keys so it can generate signatures.
///  - The deployed and initialized contract.
fn setup_chain_and_contract() -> (Chain, ContractInitSuccess) {
    let mut chain = Chain::new();

    let balance = AccountBalance {
        total:  ACC_INITIAL_BALANCE,
        staked: Amount::zero(),
        locked: Amount::zero(),
    };

    let mut inner_key_map: BTreeMap<KeyIndex, VerifyKey> = BTreeMap::new();

    inner_key_map.insert(
        KeyIndex(0u8),
        VerifyKey::Ed25519VerifyKey(
            ed25519_dalek::PublicKey::from_bytes(&PUBLIC_KEY)
                .expect("Should be able to create public key"),
        ),
    );

    let credential_public_keys = CredentialPublicKeys {
        keys:      inner_key_map,
        threshold: SignatureThreshold::ONE,
    };

    let mut key_map: BTreeMap<CredentialIndex, CredentialPublicKeys> = BTreeMap::new();
    key_map.insert(
        CredentialIndex {
            index: 0u8,
        },
        credential_public_keys,
    );

    let keys = AccountAccessStructure {
        keys:      key_map,
        threshold: AccountThreshold::ONE,
    };
    chain.create_account(Account::new_with_keys(ACC_ADDR_OTHER, balance, keys));
    chain.create_account(Account::new(ACC_ADDR_OWNER, ACC_INITIAL_BALANCE));

    let module = module_load_v1("contract.wasm.v1").expect("Module exists and is valid");
    let deployment = chain
        .module_deploy_v1(Signer::with_one_key(), ACC_ADDR_OWNER, module)
        .expect("Deploying valid module should succeed");

    let initialization = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_ADDR_OWNER,
            Energy::from(10000),
            InitContractPayload {
                amount:    Amount::zero(),
                mod_ref:   deployment.module_reference,
                init_name: OwnedContractName::new_unchecked("init_cis3_nft".to_string()),
                param:     OwnedParameter::empty(),
            },
        )
        .expect("Initialization should always succeed");

    (chain, initialization)
}

/// Test that initializing the contract works and that its balance can be
/// queried afterwards.
#[test]
fn test_init() {
    let (chain, initialization) = setup_chain_and_contract();
    assert_eq!(
        chain.contract_balance(initialization.contract_address),
        Some(Amount::zero()),
        "Contract should be initilized with 0 CCD"
    );
}

/// Test `nonceOf` query. We check that the nonce of `ACC_ADDR_OTHER` is 1 when
/// the account already sent one sponsored transaction. We check that the nonce
/// of `ACC_ADDR_OWNER` is 0 when the account did not send any sponsored
/// transaction. We check that the nonce of `NON_EXISTING_ACCOUNT` is 0.
#[test]
fn test_nonce_of_query() {
    let (mut chain, initialization) = setup_chain_and_contract();

    // To increase the nonce of account `ACC_ADDR_OTHER`, we invoke the
    // `update_permit` function with a valid signature from account
    // `ACC_ADDR_OTHER`.

    // Create input parematers for the `permit` updateOperator function.
    let update_operator = UpdateOperator {
        update:   OperatorUpdate::Add,
        operator: ADDR_OWNER,
    };
    let payload = UpdateOperatorParams(vec![update_operator]);

    let mut inner_signature_map = BTreeMap::new();
    inner_signature_map.insert(0u8, concordium_std::Signature::Ed25519(SIGNATURE_UPDATE_OPERATOR));

    let mut signature_map = BTreeMap::new();
    signature_map.insert(0u8, CredentialSignatures {
        sigs: inner_signature_map,
    });

    let permit_update_operator_param = PermitParam {
        signature: AccountSignatures {
            sigs: signature_map,
        },
        signer:    ACC_ADDR_OTHER,
        message:   PermitMessage {
            timestamp:        Timestamp::from_timestamp_millis(10000000000),
            contract_address: ContractAddress {
                index:    0,
                subindex: 0,
            },
            entry_point:      OwnedEntrypointName::new_unchecked("updateOperator".into()),
            nonce:            0,
            payload:          to_bytes(&payload),
        },
    };

    // Update operator with the permit function.
    let _ = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis3_nft.permit".to_string()),
                message:      OwnedParameter::from_serial(&permit_update_operator_param)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to update operator with permit");

    // Check if correct nonces are returned by the `nonceOf` function.
    let nonce_query_vector = VecOfAccountAddresses {
        queries: vec![ACC_ADDR_OTHER, ACC_ADDR_OWNER, NON_EXISTING_ACCOUNT],
    };

    let invoke = chain
        .contract_invoke(
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis3_nft.nonceOf".to_string()),
                message:      OwnedParameter::from_serial(&nonce_query_vector)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to query publicKeyOf");

    let nonces: NonceOfQueryResponse =
        from_bytes(&invoke.return_value).expect("Should return a valid result");

    assert_eq!(
        nonces.0[0], 1,
        "Nonce of ACC_ADDR_OTHER should be 1 because the account already sent one sponsored \
         transaction"
    );
    assert_eq!(
        nonces.0[1], 0,
        "Nonce of ACC_ADDR_OWNER should be 0 because the account did not send any sponsored \
         transaction"
    );
    assert_eq!(nonces.0[2], 0, "Nonce of non-existing account should be 0");
}

/// Test `publicKeyOf` query. `ACC_ADDR_OTHER` should have its correct keys
/// returned. `NON_EXISTING_ACCOUNT` should have `None` returned because it does
/// not exist on chain.
#[test]
fn test_public_key_of_query() {
    let (chain, initialization) = setup_chain_and_contract();

    let public_key_of_query_vector = VecOfAccountAddresses {
        queries: vec![ACC_ADDR_OTHER, NON_EXISTING_ACCOUNT],
    };

    let invoke = chain
        .contract_invoke(
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis3_nft.publicKeyOf".to_string()),
                message:      OwnedParameter::from_serial(&public_key_of_query_vector)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to query publicKeyOf");

    let public_keys_of: PublicKeyOfQueryResponse =
        from_bytes(&invoke.return_value).expect("Should return a valid result");

    let mut inner_key_map: BTreeMap<u8, PublicKey> = BTreeMap::new();

    inner_key_map.insert(0u8, PublicKey::Ed25519(concordium_std::PublicKeyEd25519(PUBLIC_KEY)));

    let credential_public_keys = concordium_std::CredentialPublicKeys {
        keys:      inner_key_map,
        threshold: SignatureThreshold::ONE,
    };

    let mut key_map: BTreeMap<u8, concordium_std::CredentialPublicKeys> = BTreeMap::new();
    key_map.insert(0u8, credential_public_keys);

    let account_public_keys: AccountPublicKeys = AccountPublicKeys {
        keys:      key_map,
        threshold: AccountThreshold::ONE,
    };

    assert_eq!(
        public_keys_of.0[0],
        Some(account_public_keys),
        "An existing account should have correct public keys returned"
    );
    assert!(public_keys_of.0[1].is_none(), "Non existing account should have no public keys");
}

/// Permit transfer function.
#[test]
fn test_permit_transfer() {
    let (mut chain, initialization) = setup_chain_and_contract();

    // Owner of the newly minted token.
    let mint_param = MintParams {
        owner: ADDR_OTHER,
    };

    // Mint token.
    let _ = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis3_nft.mint".to_string()),
                message:      OwnedParameter::from_serial(&mint_param)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to mint token");

    // Check balances in state.
    let balance_of_query = BalanceOfQuery {
        token_id: TOKEN_1,
        address:  ADDR_OWNER,
    };
    let balance_of_query2 = BalanceOfQuery {
        token_id: TOKEN_1,
        address:  ADDR_OTHER,
    };

    let balance_of_query_vector = BalanceOfQueryParams {
        queries: vec![balance_of_query, balance_of_query2],
    };

    let invoke = chain
        .contract_invoke(
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis3_nft.balanceOf".to_string()),
                message:      OwnedParameter::from_serial(&balance_of_query_vector)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to query balanceOf");

    let balance_of: BalanceOfQueryResponse<ContractTokenAmount> =
        from_bytes(&invoke.return_value).expect("Should return a valid result");

    assert_eq!(balance_of.0, [TokenAmountU8(0), TokenAmountU8(1)]);

    let transfer = concordium_cis2::Transfer {
        from:     ADDR_OTHER,
        to:       Receiver::from_account(ACC_ADDR_OWNER),
        token_id: TOKEN_1,
        amount:   ContractTokenAmount::from(1),
        data:     AdditionalData::empty(),
    };
    let payload = TransferParams::from(vec![transfer]);

    let mut inner_signature_map = BTreeMap::new();
    inner_signature_map.insert(0u8, concordium_std::Signature::Ed25519(SIGNATURE_TRANSFER));

    let mut signature_map = BTreeMap::new();
    signature_map.insert(0u8, CredentialSignatures {
        sigs: inner_signature_map,
    });

    let permit_transfer_param = PermitParam {
        signature: AccountSignatures {
            sigs: signature_map,
        },
        signer:    ACC_ADDR_OTHER,
        message:   PermitMessage {
            timestamp:        Timestamp::from_timestamp_millis(10000000000),
            contract_address: ContractAddress {
                index:    0,
                subindex: 0,
            },
            entry_point:      OwnedEntrypointName::new_unchecked("transfer".into()),
            nonce:            0,
            payload:          to_bytes(&payload),
        },
    };

    // Transfer token with the permit function.
    let update = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis3_nft.permit".to_string()),
                message:      OwnedParameter::from_serial(&permit_transfer_param)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to transfer token with permit");

    // Check logged events.
    let events: Vec<(ContractAddress, &[ContractEvent])> = update.events().collect();

    // Check transfer event.
    let transfer_event = &events[0].1[0];

    // Check event tag.
    assert_eq!(transfer_event.as_ref()[0], TRANSFER_EVENT_TAG, "Transfer event tag is wrong");

    // We remove the tag byte at the beginning of the event.
    let transfer_event_type: TransferEvent<ContractTokenId, ContractTokenAmount> =
        from_bytes(&transfer_event.as_ref()[1..]).expect("Tag removal should work");

    assert_eq!(
        transfer_event_type,
        TransferEvent {
            token_id: TOKEN_1,
            amount:   ContractTokenAmount::from(1),
            from:     ADDR_OTHER,
            to:       ADDR_OWNER,
        },
        "Transfer event is wrong"
    );

    // Check nonce event.
    let nonce_event = &events[0].1[1];

    // Check event tag.
    assert_eq!(nonce_event.as_ref()[0], NONCE_EVENT_TAG, "Nonce event tag is wrong");

    // We remove the tag byte at the beginning of the event.
    let nonce_event_type: NonceEvent =
        from_bytes(&nonce_event.as_ref()[1..]).expect("Tag removal should work");

    assert_eq!(
        nonce_event_type,
        NonceEvent {
            account: ACC_ADDR_OTHER,
            nonce:   0,
        },
        "Nonce event is wrong"
    );

    // Check balances in state
    let balance_of_query_owner = BalanceOfQuery {
        token_id: TOKEN_1,
        address:  ADDR_OWNER,
    };
    let balance_of_query_other = BalanceOfQuery {
        token_id: TOKEN_1,
        address:  ADDR_OTHER,
    };

    let balance_of_query_vector = BalanceOfQueryParams {
        queries: vec![balance_of_query_owner, balance_of_query_other],
    };

    let invoke = chain
        .contract_invoke(
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis3_nft.balanceOf".to_string()),
                message:      OwnedParameter::from_serial(&balance_of_query_vector)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to query balanceOf");

    let balance_of: BalanceOfQueryResponse<ContractTokenAmount> =
        from_bytes(&invoke.return_value).expect("Should return a valid result");

    assert_eq!(balance_of.0, [TokenAmountU8(1), TokenAmountU8(0)]);
}

/// Permit update operator function.
#[test]
fn test_update_operator() {
    let (mut chain, initialization) = setup_chain_and_contract();

    // Check operator in state
    let operator_of_query = OperatorOfQuery {
        address: ADDR_OWNER,
        owner:   ADDR_OTHER,
    };

    let operator_of_query_vector = OperatorOfQueryParams {
        queries: vec![operator_of_query],
    };

    // Check operator in state
    let invoke = chain
        .contract_invoke(
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis3_nft.operatorOf".to_string()),
                message:      OwnedParameter::from_serial(&operator_of_query_vector)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to query operatorOf");

    let is_operator_of: OperatorOfQueryResponse =
        from_bytes(&invoke.return_value).expect("Should return a valid result");

    assert_eq!(is_operator_of.0, [false]);

    // Create input parematers for the `permit` updateOperator function.
    let update_operator = UpdateOperator {
        update:   OperatorUpdate::Add,
        operator: ADDR_OWNER,
    };
    let payload = UpdateOperatorParams(vec![update_operator]);

    let mut inner_signature_map = BTreeMap::new();
    inner_signature_map.insert(0u8, concordium_std::Signature::Ed25519(SIGNATURE_UPDATE_OPERATOR));

    let mut signature_map = BTreeMap::new();
    signature_map.insert(0u8, CredentialSignatures {
        sigs: inner_signature_map,
    });

    let permit_update_operator_param = PermitParam {
        signature: AccountSignatures {
            sigs: signature_map,
        },
        signer:    ACC_ADDR_OTHER,
        message:   PermitMessage {
            timestamp:        Timestamp::from_timestamp_millis(10000000000),
            contract_address: ContractAddress {
                index:    0,
                subindex: 0,
            },
            entry_point:      OwnedEntrypointName::new_unchecked("updateOperator".into()),
            nonce:            0,
            payload:          to_bytes(&payload),
        },
    };

    // Update operator with the permit function.
    let update = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis3_nft.permit".to_string()),
                message:      OwnedParameter::from_serial(&permit_update_operator_param)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to update operator with permit");

    // Check logged events.
    let events: Vec<(ContractAddress, &[ContractEvent])> = update.events().collect();

    // Check update operator event.
    let update_operator_event = &events[0].1[0];

    // Check event tag.
    assert_eq!(
        update_operator_event.as_ref()[0],
        UPDATE_OPERATOR_EVENT_TAG,
        "Update operator event tag is wrong"
    );

    // We remove the tag byte at the beginning of the event.
    let update_operator_event_type: UpdateOperatorEvent =
        from_bytes(&update_operator_event.as_ref()[1..]).expect("Tag removal should work");

    assert_eq!(
        update_operator_event_type,
        UpdateOperatorEvent {
            update:   OperatorUpdate::Add,
            owner:    ADDR_OTHER,
            operator: ADDR_OWNER,
        },
        "Update operator event is wrong"
    );

    // Check nonce event.
    let nonce_event = &events[0].1[1];

    // Check event tag.
    assert_eq!(nonce_event.as_ref()[0], NONCE_EVENT_TAG, "Nonce event tag is wrong");

    // We remove the tag byte at the beginning of the event.
    let nonce_event_type: NonceEvent =
        from_bytes(&nonce_event.as_ref()[1..]).expect("Tag removal should work");

    assert_eq!(
        nonce_event_type,
        NonceEvent {
            account: ACC_ADDR_OTHER,
            nonce:   0,
        },
        "Nonce event is wrong"
    );

    // Check operator in state
    let operator_of_query = OperatorOfQuery {
        address: ADDR_OWNER,
        owner:   ADDR_OTHER,
    };

    let operator_of_query_vector = OperatorOfQueryParams {
        queries: vec![operator_of_query],
    };

    // Check operator in state
    let invoke = chain
        .contract_invoke(
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("cis3_nft.operatorOf".to_string()),
                message:      OwnedParameter::from_serial(&operator_of_query_vector)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to query operatorOf");

    let is_operator_of: OperatorOfQueryResponse =
        from_bytes(&invoke.return_value).expect("Should return a valid result");

    assert_eq!(is_operator_of.0, [true])
}
