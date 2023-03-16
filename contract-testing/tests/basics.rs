//! This module contains tests for the basic functionality of the testing
//! library.
use concordium_smart_contract_testing::*;

const ACC_0: AccountAddress = AccountAddress([0; 32]);
const ACC_1: AccountAddress = AccountAddress([1; 32]);

#[test]
fn deploying_valid_module_works() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res = chain
        .module_deploy_v1(
            ACC_0,
            Chain::module_load_v1(
                "../../concordium-rust-smart-contracts/examples/icecream/a.wasm.v1",
            )
            .expect("module should exist"),
        )
        .expect("Deploying valid module should work.");

    assert_eq!(chain.modules.len(), 1);
    assert_eq!(
        chain.account_balance_available(ACC_0),
        Some(initial_balance - res.transaction_fee)
    );
}

#[test]
fn initializing_valid_contract_works() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            ACC_0,
            Chain::module_load_v1(
                "../../concordium-rust-smart-contracts/examples/icecream/a.wasm.v1",
            )
            .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_weather"),
            OwnedParameter::try_from(vec![0u8]).expect("Parameter has valid size."),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");
    assert_eq!(
        chain.account_balance_available(ACC_0),
        Some(initial_balance - res_deploy.transaction_fee - res_init.transaction_fee)
    );
    assert_eq!(chain.contracts.len(), 1);
}

#[test]
fn initializing_with_invalid_parameter_fails() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            ACC_0,
            Chain::module_load_v1(
                "../../concordium-rust-smart-contracts/examples/icecream/a.wasm.v1",
            )
            .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_weather"),
            OwnedParameter::try_from(vec![99u8]).expect("Parameter has valid size."), // Invalid param
            Amount::zero(),
            Energy::from(10000),
        )
        .expect_err("Initializing with invalid params should fail");

    let transaction_fee = res_init.transaction_fee;
    match res_init.kind {
        // Failed in the right way and account is still charged.
        ContractInitErrorKind::ExecutionError {
            failure_kind: InitFailure::Reject { .. },
        } => assert_eq!(
            chain.account_balance_available(ACC_0),
            Some(initial_balance - res_deploy.transaction_fee - transaction_fee)
        ),
        _ => panic!("Expected valid chain error."),
    };
}

#[test]
fn updating_valid_contract_works() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            ACC_0,
            Chain::module_load_v1(
                "../../concordium-rust-smart-contracts/examples/icecream/a.wasm.v1",
            )
            .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_weather"),
            OwnedParameter::try_from(vec![0u8]).expect("Parameter has valid size."), // Starts as 0
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");

    let res_update = chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("set"),
            OwnedParameter::try_from(vec![1u8]).expect("Parameter has valid size."), // Updated to 1
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Updating valid contract should work");

    let res_invoke_get = chain
        .contract_invoke(
            ACC_0,
            Address::Contract(res_init.contract_address), // Invoke with a contract as sender.
            res_init.contract_address,
            EntrypointName::new_unchecked("get"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Invoking get should work");

    // This also asserts that the account wasn't charged for the invoke.
    assert_eq!(
        chain.account_balance_available(ACC_0),
        Some(
            initial_balance
                - res_deploy.transaction_fee
                - res_init.transaction_fee
                - res_update.transaction_fee
        )
    );
    assert_eq!(chain.contracts.len(), 1);
    assert!(res_update.state_changed);
    // Assert that the updated state is persisted.
    assert_eq!(res_invoke_get.return_value, [1u8]);
}

/// Test that updates and invocations where the sender is missing fail.
#[test]
fn updating_and_invoking_with_missing_sender_fails() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let missing_account = Address::Account(ACC_1);
    let missing_contract = Address::Contract(ContractAddress::new(100, 0));

    let res_deploy = chain
        .module_deploy_v1(
            ACC_0,
            Chain::module_load_v1(
                "../../concordium-rust-smart-contracts/examples/icecream/a.wasm.v1",
            )
            .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_weather"),
            OwnedParameter::try_from(vec![0u8]).expect("Parameter has valid size."), // Starts as 0
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");

    let res_update_acc = chain
        .contract_update(
            ACC_0,
            missing_account,
            res_init.contract_address,
            EntrypointName::new_unchecked("get"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect_err("should fail");

    let res_invoke_acc = chain
        .contract_invoke(
            ACC_0,
            missing_account,
            res_init.contract_address,
            EntrypointName::new_unchecked("get"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect_err("should fail");

    let res_update_contr = chain
        .contract_update(
            ACC_0,
            missing_contract,
            res_init.contract_address,
            EntrypointName::new_unchecked("get"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect_err("should fail");

    let res_invoke_contr = chain
        .contract_invoke(
            ACC_0,
            missing_contract,
            res_init.contract_address,
            EntrypointName::new_unchecked("get"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect_err("should fail");

    assert!(matches!(
            res_update_acc.kind,
            ContractInvocationErrorKind::SenderDoesNotExist(addr) if addr == missing_account));
    assert!(matches!(
            res_invoke_acc.kind,
            ContractInvocationErrorKind::SenderDoesNotExist(addr) if addr == missing_account));
    assert!(matches!(
            res_update_contr.kind,
            ContractInvocationErrorKind::SenderDoesNotExist(addr) if addr == missing_contract));
    assert!(matches!(
            res_invoke_contr.kind,
            ContractInvocationErrorKind::SenderDoesNotExist(addr) if addr == missing_contract));
}

#[test]
fn init_with_less_energy_than_module_lookup() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            ACC_0,
            Chain::module_load_v1("../../concordium-rust-smart-contracts/examples/fib/a.wasm.v1")
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let reserved_energy = Energy::from(10);

    let res_init = chain.contract_init(
        ACC_0,
        res_deploy.module_reference,
        ContractName::new_unchecked("init_fib"),
        OwnedParameter::empty(),
        Amount::zero(),
        reserved_energy,
    );
    match res_init {
        Err(ContractInitError {
            kind: ContractInitErrorKind::OutOfEnergy,
            ..
        }) => (),
        _ => panic!("Expected to fail with out of energy."),
    }
}

#[test]
fn update_with_fib_reentry_works() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            ACC_0,
            Chain::module_load_v1("../../concordium-rust-smart-contracts/examples/fib/a.wasm.v1")
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_fib"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");

    let res_update = chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("receive"),
            OwnedParameter::from_serial(&6u64).expect("Parameter has valid size"),
            Amount::zero(),
            Energy::from(100000),
        )
        .expect("Updating valid contract should work");

    let res_view = chain
        .contract_invoke(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("view"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Invoking get should work");

    // This also asserts that the account wasn't charged for the invoke.
    assert_eq!(
        chain.account_balance_available(ACC_0),
        Some(
            initial_balance
                - res_deploy.transaction_fee
                - res_init.transaction_fee
                - res_update.transaction_fee
        )
    );
    assert_eq!(chain.contracts.len(), 1);
    assert!(res_update.state_changed);
    let expected_res = u64::to_le_bytes(13);
    assert_eq!(res_update.return_value, expected_res);
    // Assert that the updated state is persisted.
    assert_eq!(res_view.return_value, expected_res);
}
