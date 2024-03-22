//! Tests for the `cis2_wCCD` contract.
use account_abstracted_smart_contract_wallet::*;
use cis2_multi::MintParams;
use concordium_cis2::*;
use concordium_smart_contract_testing::*;
use concordium_std::PublicKeyEd25519;

/// The tests accounts.
const ALICE: AccountAddress = AccountAddress([0; 32]);
const ALICE_ADDR: Address = Address::Account(ALICE);
const BOB: AccountAddress = AccountAddress([1; 32]);

const ALICE_PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([8; 32]);
const BOB_PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([9; 32]);

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
        data:         AdditionalData::from(to_bytes(&ALICE_PUBLIC_KEY)),
    };

    // Check that Alice has 0 tokens and Bob has 0 tokens on their public keys.
    let balances = get_cis2_tokens_balances_from_alice_and_bob(
        &chain,
        smart_contract_wallet,
        cis2_token_contract_address,
    );
    assert_eq!(balances.0, [TokenAmountU256(0u8.into()), TokenAmountU256(0u8.into())]);

    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.mint".to_string()),
            address:      cis2_token_contract_address,
            message:      OwnedParameter::from_serial(&mint_param)
                .expect("Mint cis2 tokens params"),
        })
        .expect("Should be able to deposit CCD");

    // Check that Alice now has 100 tokens and Bob has 0 tokens on their public
    // keys.
    let balances = get_cis2_tokens_balances_from_alice_and_bob(
        &chain,
        smart_contract_wallet,
        cis2_token_contract_address,
    );
    assert_eq!(balances.0, [
        TokenAmountU256(AIRDROP_TOKEN_AMOUNT.0.into()),
        TokenAmountU256(0u8.into())
    ]);

    // Check that the logs are correct.
    let events = deserialize_update_events_of_specified_contract(&update, smart_contract_wallet);

    assert_eq!(events, [Event::DepositCis2Tokens(DepositCis2TokensEvent {
        token_amount: TokenAmountU256(AIRDROP_TOKEN_AMOUNT.0.into()),
        token_id: TokenIdVec(vec![TOKEN_ID.0]),
        cis2_token_contract_address,
        from: Address::Contract(cis2_token_contract_address),
        to: ALICE_PUBLIC_KEY
    })]);
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

    // Load and deploy cis2 token module.
    let module =
        module_load_v1("../cis2-multi/concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, ALICE, module).expect("Deploy valid module");

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
    let deployment = chain.module_deploy_v1(SIGNER, ALICE, module).expect("Deploy valid module");

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
fn get_cis2_tokens_balances_from_alice_and_bob(
    chain: &Chain,
    contract_address: ContractAddress,
    cis2_token_contract_address: ContractAddress,
) -> Cis2TokensBalanceOfResponse {
    let balance_of_params = Cis2TokensBalanceOfParameter {
        queries: vec![
            Cis2TokensBalanceOfQuery {
                token_id: TokenIdVec(vec![TOKEN_ID.0]),
                cis2_token_contract_address,
                public_key: ALICE_PUBLIC_KEY,
            },
            Cis2TokensBalanceOfQuery {
                token_id: TokenIdVec(vec![TOKEN_ID.0]),
                cis2_token_contract_address,
                public_key: BOB_PUBLIC_KEY,
            },
        ],
    };
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "smart_contract_wallet.balanceOfCis2Tokens".to_string(),
            ),
            address:      contract_address,
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
    contract_address: ContractAddress,
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
            address:      contract_address,
            message:      OwnedParameter::from_serial(&balance_of_params)
                .expect("BalanceOf native currency params"),
        })
        .expect("Invoke balanceOf native currency");
    let rv: NativeCurrencyBalanceOfResponse =
        invoke.parse_return_value().expect("BalanceOf native currency return value");
    rv
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
