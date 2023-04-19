//! This module contains tests that test various basic things, such as state
//! reentry and energy usage and amounts charged.
use concordium_smart_contract_testing::*;

const ACC_0: AccountAddress = AccountAddress([0; 32]);
const WASM_TEST_FOLDER: &str = "../concordium-base/smart-contracts/testdata/contracts/v1";

#[test]
fn fib_reentry_and_cost_test() {
    let mut chain = Chain::new_with_time_and_rates(
        SlotTime::from_timestamp_millis(0),
        // Set a specific value, taken from testnet, to compare the exact amounts charged.
        ExchangeRate::new_unchecked(3127635127520773120, 24857286553),
        ExchangeRate::new_unchecked(1, 50000),
    )
    .expect("Values known to be in range.");

    let initial_balance = Amount::from_ccd(100_000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    let deployment = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/fib.wasm", WASM_TEST_FOLDER))
                .expect("Module should exist."),
        )
        .expect("Deploying valid module should work");

    let init = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                amount:    Amount::zero(),
                mod_ref:   deployment.module_reference,
                init_name: OwnedContractName::new_unchecked("init_fib".into()),
                param:     OwnedParameter::empty(),
            },
        )
        .expect("Initializing valid contract should work");

    let update = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(100000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("fib.receive".into()),
                message:      OwnedParameter::from_serial(&6u64).expect("Parameter has valid size"),
            },
        )
        .expect("Updating valid contract should work");

    let view = chain
        .contract_invoke(
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("fib.view".into()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect("Invoking get should work");

    // Check the state and return values.
    assert!(chain.get_contract(init.contract_address).is_some());
    assert!(update.state_changed);
    let expected_res = u64::to_le_bytes(13);
    assert_eq!(update.return_value, expected_res);
    // Assert that the updated state is persisted.
    assert_eq!(view.return_value, expected_res);

    // Check that the account was correctly charged for all transactions.
    // This also asserts that the account wasn't charged for the invoke.
    assert_eq!(
        chain.account_balance_available(ACC_0),
        Some(
            initial_balance
                - deployment.transaction_fee
                - init.transaction_fee
                - update.transaction_fee
        )
    );

    // Check that the energy usage matches the node.
    assert_eq!(deployment.energy_used, 1067.into());
    assert_eq!(init.energy_used, 771.into());
    assert_eq!(update.energy_used, 8198.into());
    assert_eq!(view.energy_used, 316.into());

    // Check that the amounts charged matches the node.
    assert_eq!(
        deployment.transaction_fee,
        Amount::from_micro_ccd(2_685_078)
    );
    assert_eq!(init.transaction_fee, Amount::from_micro_ccd(1_940_202));
    assert_eq!(update.transaction_fee, Amount::from_micro_ccd(20_630_050));
}
