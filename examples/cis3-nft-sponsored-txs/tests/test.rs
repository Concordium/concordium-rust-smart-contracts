//! This module contains integration tests for the cis3-sponsored-transaction
//! contract. To run them, use `cargo test`.
use cis3_nft_sponsored_txs::{MintParams, PermitMessage, PermitParam};
use concordium_cis2::{TokenIdU32, *};
use concordium_smart_contract_testing::{
    AccountAccessStructure, AccountBalance, AccountThreshold, CredentialIndex,
    CredentialPublicKeys, KeyIndex, SignatureThreshold, VerifyKey, *,
};
use concordium_std::{AccountSignatures, CredentialSignatures, SignatureEd25519, Timestamp};
use std::collections::BTreeMap;

const ACC_ADDR_OWNER: AccountAddress = AccountAddress([0u8; 32]);
const ACC_ADDR_OTHER: AccountAddress = AccountAddress([1u8; 32]);
const ADDR_OTHER: Address = Address::Account(ACC_ADDR_OTHER);
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

/// A helper method for setting up:
///  - The chain,
///  - The two accounts `ACC_ADDR_OWNER` and `ACC_ADDR_OTHER`, both with
///    `ACC_INITIAL_BALANCE` CCD. `ACC_ADDR_OTHER` will be set up with valid public
///    keys so it can generate signatures.
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
        VerifyKey::Ed25519VerifyKey(ed25519_dalek::PublicKey::from_bytes(&PUBLIC_KEY).unwrap()),
    );

    let credential_public_keys = CredentialPublicKeys {
        keys:      inner_key_map,
        threshold: SignatureThreshold {
            threshold: 1,
            kind:      std::marker::PhantomData,
        },
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
        threshold: AccountThreshold {
            threshold: 1,
            kind:      std::marker::PhantomData,
        },
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

/// Permit transfer function.
#[test]
fn test_permit_transfer() {
    type ContractTokenAmount = TokenAmountU8;

    let (mut chain, initialization) = setup_chain_and_contract();

    // Owner of the newly minted token.
    let mint_param = MintParams {
        owner: ADDR_OTHER,
    };

    // Mint token.
    let update = chain.contract_update(
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
    );

    assert!(update.is_ok());

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
    let update = chain.contract_update(
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
    );

    assert!(update.is_ok());
}
