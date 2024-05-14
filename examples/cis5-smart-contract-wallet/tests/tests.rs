//! Tests for the `smart_contract_wallet` contract.
use cis2_multi::{ContractBalanceOfQueryParams, ContractBalanceOfQueryResponse, MintParams};
use concordium_cis2::*;
use concordium_smart_contract_testing::*;
use concordium_std::{PublicKeyEd25519, SignatureEd25519};
use smart_contract_wallet as cis5;
use smart_contract_wallet::*;

/// The tests accounts.
const ALICE: AccountAddress = AccountAddress([0; 32]);
const ALICE_ADDR: Address = Address::Account(ALICE);
const BOB: AccountAddress = AccountAddress([1; 32]);
const BOB_ADDR: Address = Address::Account(BOB);
const CHARLIE: AccountAddress = AccountAddress([2; 32]);
const CHARLIE_ADDR: Address = Address::Account(CHARLIE);

const ALICE_PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([7; 32]);
const BOB_PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([8; 32]);
const SERVICE_FEE_RECIPIENT_KEY: PublicKeyEd25519 = PublicKeyEd25519([9; 32]);

/// Initial balance of the accounts.
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

const TOKEN_ID: TokenIdU8 = TokenIdU8(4);

const AIRDROP_TOKEN_AMOUNT: TokenAmountU64 = TokenAmountU64(100);
const AIRDROP_CCD_AMOUNT: Amount = Amount::from_micro_ccd(200);

const DUMMY_SIGNATURE: SignatureEd25519 = SignatureEd25519([
    68, 134, 96, 171, 184, 199, 1, 93, 76, 87, 144, 68, 55, 180, 93, 56, 107, 95, 127, 112, 24, 55,
    162, 131, 165, 91, 133, 104, 2, 5, 78, 224, 214, 21, 66, 0, 44, 108, 52, 4, 108, 10, 123, 75,
    21, 68, 42, 79, 106, 106, 87, 125, 122, 77, 154, 114, 208, 145, 171, 47, 108, 96, 221, 13,
]);

/// A signer for all the transactions.
const SIGNER: Signer = Signer::with_one_key();

/// Test depositing of CCD.
#[test]
fn test_deposit_ccd() {
    let (mut chain, smart_contract_wallet, _cis2_token_contract_address) =
        initialize_chain_and_contract();

    alice_deposits_ccd(&mut chain, smart_contract_wallet, ALICE_PUBLIC_KEY);
}

/// Test depositing of cis2 tokens.
#[test]
fn test_deposit_cis2_tokens() {
    let (mut chain, smart_contract_wallet, cis2_token_contract_address) =
        initialize_chain_and_contract();

    alice_deposits_cis2_tokens(
        &mut chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        ALICE_PUBLIC_KEY,
    );
}

/// Test withdrawing of CCD.
#[test]
fn test_withdraw_ccd() {
    let (mut chain, smart_contract_wallet, _cis2_token_contract_address) =
        initialize_chain_and_contract();

    use ed25519_dalek::{Signer, SigningKey};

    let rng = &mut rand::thread_rng();

    // Construct signing key.
    let signing_key = SigningKey::generate(rng);
    let alice_public_key = PublicKeyEd25519(signing_key.verifying_key().to_bytes());

    alice_deposits_ccd(&mut chain, smart_contract_wallet, alice_public_key);

    let service_fee_amount: Amount = Amount::from_micro_ccd(1);
    let withdraw_amount: Amount = Amount::from_micro_ccd(5);

    let message = WithdrawMessage {
        entry_point: OwnedEntrypointName::new_unchecked("withdrawCcd".to_string()),
        expiry_time: Timestamp::now(),
        nonce: 0u64,
        service_fee_recipient: SERVICE_FEE_RECIPIENT_KEY,
        simple_withdraws: vec![Withdraw {
            to: Receiver::Account(BOB),
            withdraw_amount,
            data: AdditionalData::empty(),
        }],
        service_fee_amount,
    };

    let mut withdraw = WithdrawBatch {
        signer:    alice_public_key,
        signature: DUMMY_SIGNATURE,
        message:   message.clone(),
    };

    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      smart_contract_wallet,
            receive_name: OwnedReceiveName::new_unchecked(
                "smart_contract_wallet.getCcdWithdrawMessageHash".to_string(),
            ),
            message:      OwnedParameter::from_serial(&message)
                .expect("Should be a valid inut parameter"),
        })
        .expect("Should be able to query getCcdWithdrawMessageHash");

    let signature = signing_key.sign(&invoke.return_value);

    withdraw.signature = SignatureEd25519(signature.to_bytes());

    let withdraw_param = WithdrawParameter {
        withdraws: vec![withdraw],
    };

    let ccd_balance_bob_before =
        chain.account_balance(BOB).expect("Bob should have a balance").total;

    let update = chain
        .contract_update(
            SIGNER,
            CHARLIE,
            CHARLIE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_wallet.withdrawCcd".to_string(),
                ),
                address:      smart_contract_wallet,
                message:      OwnedParameter::from_serial(&withdraw_param)
                    .expect("Withdraw CCD params"),
            },
        )
        .expect("Should be able to withdraw CCD");

    // Check that Alice now has `AIRDROP_CCD_AMOUNT - withdraw_amount -
    // service_fee_amount` CCD, Bob has 0 CCD, and service_fee_recipient has
    // `service_fee_amount` CCD on their public keys.
    let balances = get_ccd_balance_from_alice_and_bob_and_service_fee_recipient(
        &chain,
        smart_contract_wallet,
        alice_public_key,
    );
    assert_eq!(balances.0, [
        AIRDROP_CCD_AMOUNT - withdraw_amount - service_fee_amount,
        Amount::zero(),
        service_fee_amount
    ]);

    assert_eq!(
        chain.account_balance(BOB).expect("Bob should have a balance").total,
        ccd_balance_bob_before.checked_add(withdraw_amount).expect("Expect no overflow"),
    );

    // Check that the logs are correct.
    let events = deserialize_update_events_of_specified_contract(&update, smart_contract_wallet);

    assert_eq!(events, [
        Event::TransferCcd(TransferCcdEvent {
            ccd_amount: service_fee_amount,
            from:       alice_public_key,
            to:         SERVICE_FEE_RECIPIENT_KEY,
        }),
        Event::WithdrawCcd(WithdrawCcdEvent {
            ccd_amount: withdraw_amount,
            from:       alice_public_key,
            to:         BOB_ADDR,
        }),
        Event::Nonce(NonceEvent {
            nonce:      0,
            public_key: alice_public_key,
        })
    ]);
}

/// Test withdrawing of cis2 tokens.
#[test]
fn test_withdraw_cis2_tokens() {
    let (mut chain, smart_contract_wallet, cis2_token_contract_address) =
        initialize_chain_and_contract();

    use ed25519_dalek::{Signer, SigningKey};

    let rng = &mut rand::thread_rng();

    // Construct signing key.
    let signing_key = SigningKey::generate(rng);
    let alice_public_key = PublicKeyEd25519(signing_key.verifying_key().to_bytes());

    alice_deposits_cis2_tokens(
        &mut chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
    );

    let service_fee_amount: TokenAmountU256 = TokenAmountU256(1.into());
    let withdraw_amount: TokenAmountU256 = TokenAmountU256(5.into());
    let contract_token_id: TokenIdVec = TokenIdVec(vec![TOKEN_ID.0]);

    let message = WithdrawMessage {
        entry_point:           OwnedEntrypointName::new_unchecked("withdrawCis2Tokens".to_string()),
        expiry_time:           Timestamp::now(),
        nonce:                 0u64,
        service_fee_recipient: SERVICE_FEE_RECIPIENT_KEY,
        simple_withdraws:      vec![Withdraw {
            to:              Receiver::Account(BOB),
            withdraw_amount: TokenAmount {
                token_amount: withdraw_amount,
                token_id: contract_token_id.clone(),
                cis2_token_contract_address,
            },
            data:            AdditionalData::empty(),
        }],
        service_fee_amount:    TokenAmount {
            token_amount: service_fee_amount,
            token_id: contract_token_id.clone(),
            cis2_token_contract_address,
        },
    };

    let mut withdraw = WithdrawBatch {
        signer:    alice_public_key,
        signature: DUMMY_SIGNATURE,
        message:   message.clone(),
    };

    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      smart_contract_wallet,
            receive_name: OwnedReceiveName::new_unchecked(
                "smart_contract_wallet.getCis2WithdrawMessageHash".to_string(),
            ),
            message:      OwnedParameter::from_serial(&message)
                .expect("Should be a valid inut parameter"),
        })
        .expect("Should be able to query getCis2WithdrawMessageHash");

    let signature = signing_key.sign(&invoke.return_value);

    withdraw.signature = SignatureEd25519(signature.to_bytes());

    let withdraw_param = WithdrawParameter {
        withdraws: vec![withdraw],
    };

    let token_balance_of_bob_before = get_balances(&chain, cis2_token_contract_address);

    assert_eq!(token_balance_of_bob_before.0, [TokenAmountU64(0u64)]);

    let update = chain
        .contract_update(
            SIGNER,
            CHARLIE,
            CHARLIE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_wallet.withdrawCis2Tokens".to_string(),
                ),
                address:      smart_contract_wallet,
                message:      OwnedParameter::from_serial(&withdraw_param)
                    .expect("Withdraw cis2 tokens params"),
            },
        )
        .expect("Should be able to withdraw cis2 tokens");

    // Check that Alice now has `AIRDROP_TOKEN_AMOUNT - withdraw_amount -
    // service_fee_amount` tokens, Bob has 0 tokens, and service_fee_recipient has
    // `service_fee_amount` tokens on their public keys.
    let balances = get_cis2_token_balances_from_alice_and_bob_and_service_fee_recipient(
        &chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
    );
    assert_eq!(balances.0, [
        TokenAmountU256(AIRDROP_TOKEN_AMOUNT.0.into()) - withdraw_amount - service_fee_amount,
        TokenAmountU256(0.into()),
        TokenAmountU256(service_fee_amount.into())
    ]);

    // Check balances in state.
    let token_balance_of_bob_after = get_balances(&chain, cis2_token_contract_address);

    assert_eq!(token_balance_of_bob_after.0, [TokenAmountU64(withdraw_amount.0.as_u64())]);

    // Check that the logs are correct.
    let events = deserialize_update_events_of_specified_contract(&update, smart_contract_wallet);

    assert_eq!(events, [
        Event::TransferCis2Tokens(TransferCis2TokensEvent {
            token_amount: service_fee_amount,
            token_id: contract_token_id.clone(),
            cis2_token_contract_address,
            from: alice_public_key,
            to: SERVICE_FEE_RECIPIENT_KEY
        }),
        Event::WithdrawCis2Tokens(WithdrawCis2TokensEvent {
            token_amount: withdraw_amount,
            token_id: contract_token_id,
            cis2_token_contract_address,
            from: alice_public_key,
            to: BOB_ADDR
        }),
        Event::Nonce(NonceEvent {
            nonce:      0,
            public_key: alice_public_key,
        })
    ]);
}

/// Test transfer of ccd.
#[test]
fn test_transfer_ccd() {
    let (mut chain, smart_contract_wallet, _cis2_token_contract_address) =
        initialize_chain_and_contract();

    use ed25519_dalek::{Signer, SigningKey};

    let rng = &mut rand::thread_rng();

    // Construct signing key.
    let signing_key = SigningKey::generate(rng);
    let alice_public_key = PublicKeyEd25519(signing_key.verifying_key().to_bytes());

    alice_deposits_ccd(&mut chain, smart_contract_wallet, alice_public_key);

    let service_fee_amount: Amount = Amount::from_micro_ccd(1);
    let transfer_amount: Amount = Amount::from_micro_ccd(5);

    let message = TransferMessage {
        entry_point: OwnedEntrypointName::new_unchecked("transferCcd".to_string()),
        expiry_time: Timestamp::now(),
        nonce: 0u64,
        service_fee_recipient: SERVICE_FEE_RECIPIENT_KEY,
        simple_transfers: vec![cis5::Transfer {
            to: BOB_PUBLIC_KEY,
            transfer_amount,
        }],
        service_fee_amount,
    };

    let mut transfer = TransferBatch {
        signer:    alice_public_key,
        signature: DUMMY_SIGNATURE,
        message:   message.clone(),
    };

    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      smart_contract_wallet,
            receive_name: OwnedReceiveName::new_unchecked(
                "smart_contract_wallet.getCcdTransferMessageHash".to_string(),
            ),
            message:      OwnedParameter::from_serial(&message)
                .expect("Should be a valid inut parameter"),
        })
        .expect("Should be able to query getCcdTransferMessageHash");

    let signature = signing_key.sign(&invoke.return_value);

    transfer.signature = SignatureEd25519(signature.to_bytes());

    let transfer_param = TransferParameter {
        transfers: vec![transfer],
    };

    let update = chain
        .contract_update(
            SIGNER,
            CHARLIE,
            CHARLIE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_wallet.transferCcd".to_string(),
                ),
                address:      smart_contract_wallet,
                message:      OwnedParameter::from_serial(&transfer_param)
                    .expect("Transfer CCD params"),
            },
        )
        .expect("Should be able to transfer CCD");

    // Check that Alice now has `AIRDROP_CCD_AMOUNT - transfer_amount -
    // service_fee_amount` CCD and Bob has `transfer_amount` CCD, and
    // service_fee_recipient has `service_fee_amount` CCD on their public keys.
    let balances = get_ccd_balance_from_alice_and_bob_and_service_fee_recipient(
        &chain,
        smart_contract_wallet,
        alice_public_key,
    );
    assert_eq!(balances.0, [
        AIRDROP_CCD_AMOUNT - transfer_amount - service_fee_amount,
        transfer_amount,
        service_fee_amount
    ]);

    // Check that the logs are correct.
    let events = deserialize_update_events_of_specified_contract(&update, smart_contract_wallet);

    assert_eq!(events, [
        Event::TransferCcd(TransferCcdEvent {
            ccd_amount: service_fee_amount,
            from:       alice_public_key,
            to:         SERVICE_FEE_RECIPIENT_KEY,
        }),
        Event::TransferCcd(TransferCcdEvent {
            ccd_amount: transfer_amount,
            from:       alice_public_key,
            to:         BOB_PUBLIC_KEY,
        }),
        Event::Nonce(NonceEvent {
            nonce:      0,
            public_key: alice_public_key,
        })
    ]);
}

/// Test transfer of cis2 tokens.
#[test]
fn test_transfer_cis2_tokens() {
    let (mut chain, smart_contract_wallet, cis2_token_contract_address) =
        initialize_chain_and_contract();

    use ed25519_dalek::{Signer, SigningKey};

    let rng = &mut rand::thread_rng();

    // Construct signing key.
    let signing_key = SigningKey::generate(rng);
    let alice_public_key = PublicKeyEd25519(signing_key.verifying_key().to_bytes());

    alice_deposits_cis2_tokens(
        &mut chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
    );

    let service_fee_amount: TokenAmountU256 = TokenAmountU256(1.into());
    let transfer_amount: TokenAmountU256 = TokenAmountU256(5.into());
    let contract_token_id: TokenIdVec = TokenIdVec(vec![TOKEN_ID.0]);

    let message = TransferMessage {
        entry_point:           OwnedEntrypointName::new_unchecked("transferCis2Tokens".to_string()),
        expiry_time:           Timestamp::now(),
        nonce:                 0u64,
        service_fee_recipient: SERVICE_FEE_RECIPIENT_KEY,
        service_fee_amount:    TokenAmount {
            token_amount: service_fee_amount,
            token_id: contract_token_id.clone(),
            cis2_token_contract_address,
        },
        simple_transfers:      vec![cis5::Transfer {
            to:              BOB_PUBLIC_KEY,
            transfer_amount: TokenAmount {
                token_amount: transfer_amount,
                token_id: contract_token_id.clone(),
                cis2_token_contract_address,
            },
        }],
    };

    let mut transfer = TransferBatch {
        signer:    alice_public_key,
        signature: DUMMY_SIGNATURE,
        message:   message.clone(),
    };

    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      smart_contract_wallet,
            receive_name: OwnedReceiveName::new_unchecked(
                "smart_contract_wallet.getCis2TransferMessageHash".to_string(),
            ),
            message:      OwnedParameter::from_serial(&message)
                .expect("Should be a valid inut parameter"),
        })
        .expect("Should be able to query getCis2TransferMessageHash");

    let signature = signing_key.sign(&invoke.return_value);

    transfer.signature = SignatureEd25519(signature.to_bytes());

    let transfer_param = TransferParameter {
        transfers: vec![transfer],
    };

    let update = chain
        .contract_update(
            SIGNER,
            CHARLIE,
            CHARLIE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_wallet.transferCis2Tokens".to_string(),
                ),
                address:      smart_contract_wallet,
                message:      OwnedParameter::from_serial(&transfer_param)
                    .expect("Transfer cis2 tokens params"),
            },
        )
        .expect("Should be able to transfer cis2 tokens");

    // Check that Alice now has `AIRDROP_TOKEN_AMOUNT - transfer_amount -
    // service_fee_amount` tokens, Bob has `transfer_amount` tokens, and
    // service_fee_recipient has `service_fee_amount` tokens on their public
    // keys.
    let balances = get_cis2_token_balances_from_alice_and_bob_and_service_fee_recipient(
        &chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
    );
    assert_eq!(balances.0, [
        TokenAmountU256(AIRDROP_TOKEN_AMOUNT.0.into()) - transfer_amount - service_fee_amount,
        TokenAmountU256(transfer_amount.into()),
        TokenAmountU256(service_fee_amount.into())
    ]);

    // Check that the logs are correct.
    let events = deserialize_update_events_of_specified_contract(&update, smart_contract_wallet);

    assert_eq!(events, [
        Event::TransferCis2Tokens(TransferCis2TokensEvent {
            token_amount: service_fee_amount,
            token_id: contract_token_id.clone(),
            cis2_token_contract_address,
            from: alice_public_key,
            to: SERVICE_FEE_RECIPIENT_KEY
        }),
        Event::TransferCis2Tokens(TransferCis2TokensEvent {
            token_amount: transfer_amount,
            token_id: contract_token_id,
            cis2_token_contract_address,
            from: alice_public_key,
            to: BOB_PUBLIC_KEY
        }),
        Event::Nonce(NonceEvent {
            nonce:      0,
            public_key: alice_public_key,
        })
    ]);
}

// Helpers:

/// Setup chain and contract.
///
/// Also creates the three accounts, Alice, Bob, and Charlie.
///
/// Alice is the owner of the contract.
fn initialize_chain_and_contract() -> (Chain, ContractAddress, ContractAddress) {
    let mut chain = Chain::new();

    // Create some accounts on the chain.
    chain.create_account(Account::new(ALICE, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(BOB, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(CHARLIE, ACC_INITIAL_BALANCE));

    // Load and deploy cis2 token module.
    let module =
        module_load_v1("../cis2-multi/concordium-out/module.wasm.v1").expect("Module exists");
    let deployment =
        chain.module_deploy_v1_debug(SIGNER, ALICE, module, true).expect("Deploy valid module");

    // Initialize the token contract.
    let cis2_token_contract_init = chain
        .contract_init(SIGNER, ALICE, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_cis2_multi".to_string()),
            param:     OwnedParameter::from_serial(&AIRDROP_TOKEN_AMOUNT)
                .expect("Token amount params"),
        })
        .expect("Initialize contract");

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment =
        chain.module_deploy_v1_debug(SIGNER, ALICE, module, true).expect("Deploy valid module");

    // Initialize the smart contract wallet.
    let smart_contract_wallet_init = chain
        .contract_init(SIGNER, ALICE, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_smart_contract_wallet".to_string()),
            param:     OwnedParameter::empty(),
        })
        .expect("Initialize contract");

    (chain, smart_contract_wallet_init.contract_address, cis2_token_contract_init.contract_address)
}

/// Get the token balances for Alice, Bob, and the service_fee_recipient.
fn get_cis2_token_balances_from_alice_and_bob_and_service_fee_recipient(
    chain: &Chain,
    smart_contract_wallet: ContractAddress,
    cis2_token_contract_address: ContractAddress,
    alice_public_key: PublicKeyEd25519,
) -> Cis2BalanceOfResponse {
    let balance_of_params = Cis2BalanceOfParameter {
        queries: vec![
            Cis2BalanceOfQuery {
                token_id: TokenIdVec(vec![TOKEN_ID.0]),
                cis2_token_contract_address,
                public_key: alice_public_key,
            },
            Cis2BalanceOfQuery {
                token_id: TokenIdVec(vec![TOKEN_ID.0]),
                cis2_token_contract_address,
                public_key: BOB_PUBLIC_KEY,
            },
            Cis2BalanceOfQuery {
                token_id: TokenIdVec(vec![TOKEN_ID.0]),
                cis2_token_contract_address,
                public_key: SERVICE_FEE_RECIPIENT_KEY,
            },
        ],
    };
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "smart_contract_wallet.cis2BalanceOf".to_string(),
            ),
            address:      smart_contract_wallet,
            message:      OwnedParameter::from_serial(&balance_of_params)
                .expect("CIS-2 BalanceOf params"),
        })
        .expect("Invoke CIS-2 BalanceOf");
    let rv: Cis2BalanceOfResponse =
        invoke.parse_return_value().expect("CIS-2 BalanceOf return value");
    rv
}

/// Get the CCD balances for Alice, Bob, and the
/// service_fee_recipient.
fn get_ccd_balance_from_alice_and_bob_and_service_fee_recipient(
    chain: &Chain,
    smart_contract_wallet: ContractAddress,
    alice_public_key: PublicKeyEd25519,
) -> CcdBalanceOfResponse {
    let balance_of_params = CcdBalanceOfParameter {
        queries: vec![alice_public_key, BOB_PUBLIC_KEY, SERVICE_FEE_RECIPIENT_KEY],
    };
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "smart_contract_wallet.ccdBalanceOf".to_string(),
            ),
            address:      smart_contract_wallet,
            message:      OwnedParameter::from_serial(&balance_of_params)
                .expect("CCD BalanceOf params"),
        })
        .expect("Invoke CCD balanceOf");
    let rv: CcdBalanceOfResponse = invoke.parse_return_value().expect("CCD BalanceOf return value");
    rv
}

/// Alice deposits cis2 tokens into the smart contract wallet.
fn alice_deposits_cis2_tokens(
    chain: &mut Chain,
    smart_contract_wallet: ContractAddress,
    cis2_token_contract_address: ContractAddress,
    alice_public_key: PublicKeyEd25519,
) {
    let new_metadata_url = "https://new-url.com".to_string();

    let mint_param: MintParams = MintParams {
        to:           Receiver::Contract(
            smart_contract_wallet,
            OwnedEntrypointName::new_unchecked("depositCis2Tokens".to_string()),
        ),
        metadata_url: MetadataUrl {
            url:  new_metadata_url.clone(),
            hash: None,
        },
        token_id:     TOKEN_ID,
        data:         AdditionalData::from(to_bytes(&alice_public_key)),
    };

    // Check that Alice has 0 tokens, Bob has 0 tokens, and the
    // service_fee_recipient has 0 tokens on their public keys.
    let balances = get_cis2_token_balances_from_alice_and_bob_and_service_fee_recipient(
        &chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
    );
    assert_eq!(balances.0, [
        TokenAmountU256(0u8.into()),
        TokenAmountU256(0u8.into()),
        TokenAmountU256(0u8.into())
    ]);

    // Deposit tokens.
    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.mint".to_string()),
            address:      cis2_token_contract_address,
            message:      OwnedParameter::from_serial(&mint_param)
                .expect("Mint cis2 tokens params"),
        })
        .expect("Should be able to deposit cis2 tokens");

    // Check that Alice now has AIRDROP_TOKEN_AMOUNT tokens, Bob has 0 tokens, and
    // the service_fee_recipient has 0 tokens on their public keys.
    let balances = get_cis2_token_balances_from_alice_and_bob_and_service_fee_recipient(
        &chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
    );
    assert_eq!(balances.0, [
        TokenAmountU256(AIRDROP_TOKEN_AMOUNT.0.into()),
        TokenAmountU256(0u8.into()),
        TokenAmountU256(0u8.into())
    ]);

    // Check that the logs are correct.
    let events = deserialize_update_events_of_specified_contract(&update, smart_contract_wallet);

    assert_eq!(events, [Event::DepositCis2Tokens(DepositCis2TokensEvent {
        token_amount: TokenAmountU256(AIRDROP_TOKEN_AMOUNT.0.into()),
        token_id: TokenIdVec(vec![TOKEN_ID.0]),
        cis2_token_contract_address,
        from: Address::Contract(smart_contract_wallet),
        to: alice_public_key
    })]);
}

/// Alice deposits CCD into the smart contract wallet.
fn alice_deposits_ccd(
    chain: &mut Chain,
    smart_contract_wallet: ContractAddress,
    alice_public_key: PublicKeyEd25519,
) {
    // Check that Alice has 0 CCD, Bob has 0 CCD, and the service_fee_recipient has
    // 0 CCD on their public keys.
    let balances = get_ccd_balance_from_alice_and_bob_and_service_fee_recipient(
        &chain,
        smart_contract_wallet,
        alice_public_key,
    );
    assert_eq!(balances.0, [Amount::zero(), Amount::zero(), Amount::zero()]);

    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       AIRDROP_CCD_AMOUNT,
            receive_name: OwnedReceiveName::new_unchecked(
                "smart_contract_wallet.depositCcd".to_string(),
            ),
            address:      smart_contract_wallet,
            message:      OwnedParameter::from_serial(&alice_public_key)
                .expect("Deposit CCD params"),
        })
        .expect("Should be able to deposit CCD");

    // Check that Alice now has AIRDROP_CCD_AMOUNT CCD, Bob has 0 CCD, and the
    // service_fee_recipient has 0 CCD on their public keys.
    let balances = get_ccd_balance_from_alice_and_bob_and_service_fee_recipient(
        &chain,
        smart_contract_wallet,
        alice_public_key,
    );
    assert_eq!(balances.0, [AIRDROP_CCD_AMOUNT, Amount::zero(), Amount::zero()]);

    // Check that the logs are correct.
    let events = deserialize_update_events_of_specified_contract(&update, smart_contract_wallet);

    assert_eq!(events, [Event::DepositCcd(DepositCcdEvent {
        ccd_amount: AIRDROP_CCD_AMOUNT,
        from:       ALICE_ADDR,
        to:         alice_public_key,
    })]);
}

/// Deserialize the events from an update.
fn deserialize_update_events_of_specified_contract(
    update: &ContractInvokeSuccess,
    smart_contract_wallet: ContractAddress,
) -> Vec<Event> {
    update
        .events()
        .flat_map(|(addr, events)| {
            if addr == smart_contract_wallet {
                Some(events.iter().map(|e| e.parse().expect("Deserialize event")))
            } else {
                None
            }
        })
        .flatten()
        .collect()
}

/// Get the `TOKEN_ID` balance for Bob.
fn get_balances(
    chain: &Chain,
    contract_address: ContractAddress,
) -> ContractBalanceOfQueryResponse {
    let balance_of_params = ContractBalanceOfQueryParams {
        queries: vec![BalanceOfQuery {
            token_id: TOKEN_ID,
            address:  BOB_ADDR,
        }],
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
