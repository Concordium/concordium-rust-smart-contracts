//! Tests for the `cis2_wCCD` contract.
use cis2_multi::MintParams;
use concordium_cis2::*;
use concordium_smart_contract_testing::*;
use concordium_std::{PublicKeyEd25519, SignatureEd25519};
use smart_contract_wallet::*;

/// The tests accounts.
const ALICE: AccountAddress = AccountAddress([0; 32]);
const ALICE_ADDR: Address = Address::Account(ALICE);
const BOB: AccountAddress = AccountAddress([1; 32]);
const CHARLIE: AccountAddress = AccountAddress([2; 32]);
const CHARLIE_ADDR: Address = Address::Account(CHARLIE);

const ALICE_PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([8; 32]);
const BOB_PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([9; 32]);
const SERVICE_FEE_RECIPIENT_KEY: PublicKeyEd25519 = PublicKeyEd25519([4; 32]);

const SIGNATURE: SignatureEd25519 = SignatureEd25519([
    68, 134, 96, 171, 184, 199, 1, 93, 76, 87, 144, 68, 55, 180, 93, 56, 107, 95, 127, 112, 24, 55,
    162, 131, 165, 91, 133, 104, 2, 5, 78, 224, 214, 21, 66, 0, 44, 108, 52, 4, 108, 10, 123, 75,
    21, 68, 42, 79, 106, 106, 87, 125, 122, 77, 154, 114, 208, 145, 171, 47, 108, 96, 221, 13,
]);

const TOKEN_ID: TokenIdU8 = TokenIdU8(4);

/// Initial balance of the accounts.
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

const AIRDROP_TOKEN_AMOUNT: TokenAmountU64 = TokenAmountU64(100);

/// A signer for all the transactions.
const SIGNER: Signer = Signer::with_one_key();

/// Test that init produces the correct logs.
#[test]
fn test_init() {
    let (_chain, _smart_contract_wallet, _cis2_token_contract_address) =
        initialize_chain_and_contract();
}

/// Test depositing of native currency.
#[test]
fn test_deposit_native_currency() {
    let (mut chain, smart_contract_wallet, _cis2_token_contract_address) =
        initialize_chain_and_contract();

    // Check that Alice has 0 CCD and Bob has 0 CCD on their public keys.
    let balances = get_native_currency_balance_from_alice_and_bob(&chain, smart_contract_wallet);
    assert_eq!(balances.0, [Amount::zero(), Amount::zero()]);

    let send_amount = Amount::from_micro_ccd(100);
    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       send_amount,
            receive_name: OwnedReceiveName::new_unchecked(
                "smart_contract_wallet.depositNativeCurrency".to_string(),
            ),
            address:      smart_contract_wallet,
            message:      OwnedParameter::from_serial(&ALICE_PUBLIC_KEY)
                .expect("Deposit native currency params"),
        })
        .expect("Should be able to deposit CCD");

    // Check that Alice now has 100 CCD and Bob has 0 CCD on their public keys.
    let balances = get_native_currency_balance_from_alice_and_bob(&chain, smart_contract_wallet);
    assert_eq!(balances.0, [send_amount, Amount::zero()]);

    // Check that the logs are correct.
    let events = deserialize_update_events_of_specified_contract(&update, smart_contract_wallet);

    assert_eq!(events, [Event::DepositNativeCurrency(DepositNativeCurrencyEvent {
        ccd_amount: send_amount,
        from:       ALICE_ADDR,
        to:         ALICE_PUBLIC_KEY,
    })]);
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

/// Test internal transfer of cis2 tokens.
#[test]
fn test_internal_transfer_cis2_tokens() {
    let (mut chain, smart_contract_wallet, cis2_token_contract_address) =
        initialize_chain_and_contract();

    use ed25519_dalek::{Signer, SigningKey};

    let rng = &mut rand::thread_rng();

    // Construct message, verifying_key, and signature.
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

    let mut internal_transfer_param = Cis2TokensInternalTransfer {
        signer: alice_public_key,
        signature: SIGNATURE,
        entry_point: OwnedEntrypointName::new_unchecked("internalTransferCis2Tokens".to_string()),
        expiry_time: Timestamp::now(),
        nonce: 0u64,
        service_fee_recipient: SERVICE_FEE_RECIPIENT_KEY,
        simple_transfers: vec![Cis2TokensInternalTransferBatch {
            to: BOB_PUBLIC_KEY,
            token_amount: transfer_amount,
            token_id: contract_token_id.clone(),
            cis2_token_contract_address,
        }],
        service_fee_token_amount: service_fee_amount,
        service_fee_token_id: contract_token_id.clone(),
        service_fee_cis2_token_contract_address: cis2_token_contract_address,
    };

    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      smart_contract_wallet,
            receive_name: OwnedReceiveName::new_unchecked(
                "smart_contract_wallet.viewMessageHash".to_string(),
            ),
            message:      OwnedParameter::from_serial(&internal_transfer_param)
                .expect("Should be a valid inut parameter"),
        })
        .expect("Should be able to query viewMessageHash");

    let signature = signing_key.sign(&invoke.return_value);

    internal_transfer_param.signature = SignatureEd25519(signature.to_bytes());

    let internal_transfer_param = Cis2TokensInternalTransferParameter {
        transfers: vec![internal_transfer_param.clone()],
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
                    "smart_contract_wallet.internalTransferCis2Tokens".to_string(),
                ),
                address:      smart_contract_wallet,
                message:      OwnedParameter::from_serial(&internal_transfer_param)
                    .expect("Internal transfer cis2 tokens params"),
            },
        )
        .print_emitted_events()
        .expect("Should be able to internally transfer cis2 tokens");

    // Check that Alice now has 100 tokens and Bob has 0 tokens on their public
    // keys.
    let balances = get_cis2_tokens_balances_from_alice_and_bob_and_service_fee_recipient(
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
        Event::InternalCis2TokensTransfer(InternalCis2TokensTransferEvent {
            token_amount: service_fee_amount,
            token_id: contract_token_id.clone(),
            cis2_token_contract_address,
            from: alice_public_key,
            to: SERVICE_FEE_RECIPIENT_KEY
        }),
        Event::InternalCis2TokensTransfer(InternalCis2TokensTransferEvent {
            token_amount: transfer_amount,
            token_id: contract_token_id,
            cis2_token_contract_address,
            from: alice_public_key,
            to: BOB_PUBLIC_KEY
        })
    ]);
}

// Helpers:

/// Setup chain and contract.
///
/// Also creates the two accounts, Alice and Bob.
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

    // Initialize the auction contract.
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

    // Initialize the auction contract.
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

/// Get the token balances for Alice and Bob.
fn get_cis2_tokens_balances_from_alice_and_bob_and_service_fee_recipient(
    chain: &Chain,
    smart_contract_wallet: ContractAddress,
    cis2_token_contract_address: ContractAddress,
    alice_public_key: PublicKeyEd25519,
) -> Cis2TokensBalanceOfResponse {
    let balance_of_params = Cis2TokensBalanceOfParameter {
        queries: vec![
            Cis2TokensBalanceOfQuery {
                token_id: TokenIdVec(vec![TOKEN_ID.0]),
                cis2_token_contract_address,
                public_key: alice_public_key,
            },
            Cis2TokensBalanceOfQuery {
                token_id: TokenIdVec(vec![TOKEN_ID.0]),
                cis2_token_contract_address,
                public_key: BOB_PUBLIC_KEY,
            },
            Cis2TokensBalanceOfQuery {
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
                "smart_contract_wallet.balanceOfCis2Tokens".to_string(),
            ),
            address:      smart_contract_wallet,
            message:      OwnedParameter::from_serial(&balance_of_params)
                .expect("BalanceOf params"),
        })
        .expect("Invoke balanceOf");
    let rv: Cis2TokensBalanceOfResponse =
        invoke.parse_return_value().expect("BalanceOf return value");
    rv
}

/// Get the native currency balances for Alice and Bob.
fn get_native_currency_balance_from_alice_and_bob(
    chain: &Chain,
    smart_contract_wallet: ContractAddress,
) -> NativeCurrencyBalanceOfResponse {
    let balance_of_params = NativeCurrencyBalanceOfParameter {
        queries: vec![
            NativeCurrencyBalanceOfQuery {
                public_key: ALICE_PUBLIC_KEY,
            },
            NativeCurrencyBalanceOfQuery {
                public_key: BOB_PUBLIC_KEY,
            },
        ],
    };
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "smart_contract_wallet.balanceOfNativeCurrency".to_string(),
            ),
            address:      smart_contract_wallet,
            message:      OwnedParameter::from_serial(&balance_of_params)
                .expect("BalanceOf native currency params"),
        })
        .expect("Invoke balanceOf native currency");
    let rv: NativeCurrencyBalanceOfResponse =
        invoke.parse_return_value().expect("BalanceOf native currency return value");
    rv
}

/// Get the token balances for Alice and Bob.
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

    // Check that Alice has 0 tokens and Bob has 0 tokens on their public keys.
    let balances = get_cis2_tokens_balances_from_alice_and_bob_and_service_fee_recipient(
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

    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.mint".to_string()),
            address:      cis2_token_contract_address,
            message:      OwnedParameter::from_serial(&mint_param)
                .expect("Mint cis2 tokens params"),
        })
        .expect("Should be able to deposit cis2 tokens");

    // Check that Alice now has 100 tokens and Bob has 0 tokens on their public
    // keys.
    let balances = get_cis2_tokens_balances_from_alice_and_bob_and_service_fee_recipient(
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
        from: Address::Contract(cis2_token_contract_address),
        to: alice_public_key
    })]);
}

// /// Deserialize the events from an update.
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
