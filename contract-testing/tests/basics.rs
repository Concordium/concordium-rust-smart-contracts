//! This module contains tests for the basic functionality of the testing
//! library.
use concordium_smart_contract_testing::*;

const ACC_0: AccountAddress = AccountAddress([0; 32]);
const ACC_1: AccountAddress = AccountAddress([1; 32]);

#[test]
fn deploying_valid_module_works() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(ACC_0, AccountInfo::new(initial_balance));

    let res = chain
        .module_deploy_v1(ACC_0, "examples/icecream/icecream.wasm.v1")
        .expect("Deploying valid module should work.");

    assert_eq!(chain.modules.len(), 1);
    assert_eq!(
        chain.persistence_account_balance(ACC_0),
        Some(initial_balance - res.transaction_fee)
    );
}

#[test]
fn initializing_valid_contract_works() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(ACC_0, AccountInfo::new(initial_balance));

    let res_deploy = chain
        .module_deploy_v1(ACC_0, "examples/icecream/icecream.wasm.v1")
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_weather"),
            OwnedParameter::from_bytes(vec![0u8]),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");
    assert_eq!(
        chain.persistence_account_balance(ACC_0),
        Some(initial_balance - res_deploy.transaction_fee - res_init.transaction_fee)
    );
    assert_eq!(chain.contracts.len(), 1);
}

#[test]
fn initializing_with_invalid_parameter_fails() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(ACC_0, AccountInfo::new(initial_balance));

    let res_deploy = chain
        .module_deploy_v1(ACC_0, "examples/icecream/icecream.wasm.v1")
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_weather"),
            OwnedParameter::from_bytes(vec![99u8]), // Invalid param
            Amount::zero(),
            Energy::from(10000),
        )
        .expect_err("Initializing with invalid params should fail");

    assert!(matches!(res_init, ContractInitError::ValidChainError(_)));
    match res_init {
        // Failed in the right way and account is still charged.
        ContractInitError::ValidChainError(FailedContractInteraction::Reject {
            transaction_fee,
            ..
        }) => assert_eq!(
            chain.persistence_account_balance(ACC_0),
            Some(initial_balance - res_deploy.transaction_fee - transaction_fee)
        ),
        _ => panic!("Expected valid chain error."),
    };
}

#[test]
fn updating_valid_contract_works() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(ACC_0, AccountInfo::new(initial_balance));

    let res_deploy = chain
        .module_deploy_v1(ACC_0, "examples/icecream/icecream.wasm.v1")
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_weather"),
            OwnedParameter::from_bytes(vec![0u8]), // Starts as 0
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
            OwnedParameter::from_bytes(vec![1u8]), // Updated to 1
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
        chain.persistence_account_balance(ACC_0),
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
    chain.create_account(ACC_0, AccountInfo::new(initial_balance));

    let missing_account = Address::Account(ACC_1);
    let missing_contract = Address::Contract(ContractAddress::new(100, 0));

    let res_deploy = chain
        .module_deploy_v1(ACC_0, "examples/icecream/icecream.wasm.v1")
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_weather"),
            OwnedParameter::from_bytes(vec![0u8]), // Starts as 0
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");

    let res_update_acc = chain.contract_update(
        ACC_0,
        missing_account,
        res_init.contract_address,
        EntrypointName::new_unchecked("get"),
        OwnedParameter::empty(),
        Amount::zero(),
        Energy::from(10000),
    );

    let res_invoke_acc = chain.contract_invoke(
        ACC_0,
        missing_account,
        res_init.contract_address,
        EntrypointName::new_unchecked("get"),
        OwnedParameter::empty(),
        Amount::zero(),
        Energy::from(10000),
    );

    let res_update_contr = chain.contract_update(
        ACC_0,
        missing_contract,
        res_init.contract_address,
        EntrypointName::new_unchecked("get"),
        OwnedParameter::empty(),
        Amount::zero(),
        Energy::from(10000),
    );

    let res_invoke_contr = chain.contract_invoke(
        ACC_0,
        missing_contract,
        res_init.contract_address,
        EntrypointName::new_unchecked("get"),
        OwnedParameter::empty(),
        Amount::zero(),
        Energy::from(10000),
    );

    assert!(matches!(
            res_update_acc,
            Err(ContractUpdateError::SenderDoesNotExist(addr)) if addr == missing_account));
    assert!(matches!(
            res_invoke_acc,
            Err(ContractUpdateError::SenderDoesNotExist(addr)) if addr == missing_account));
    assert!(matches!(
            res_update_contr,
            Err(ContractUpdateError::SenderDoesNotExist(addr)) if addr == missing_contract));
    assert!(matches!(
            res_invoke_contr,
            Err(ContractUpdateError::SenderDoesNotExist(addr)) if addr == missing_contract));
}

/// Tests using the integrate contract defined in
/// concordium-rust-smart-contract on the 'kb/sc-integration-testing'
/// branch.
mod integrate_contract {
    use super::*;

    #[test]
    fn update_with_account_transfer_works() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        let transfer_amount = Amount::from_ccd(1);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));
        chain.create_account(ACC_1, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy_v1(ACC_0, "examples/integrate/a.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_integrate"),
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
                OwnedParameter::new(&ACC_1),
                transfer_amount,
                Energy::from(10000),
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
            chain.persistence_account_balance(ACC_0),
            Some(
                initial_balance
                    - res_deploy.transaction_fee
                    - res_init.transaction_fee
                    - res_update.transaction_fee
                    - transfer_amount
            )
        );
        assert_eq!(
            chain.persistence_account_balance(ACC_1),
            Some(initial_balance + transfer_amount)
        );
        assert_eq!(res_update.transfers(), [Transfer {
            from:   res_init.contract_address,
            amount: transfer_amount,
            to:     ACC_1,
        }]);
        assert_eq!(chain.contracts.len(), 1);
        assert!(res_update.state_changed);
        assert_eq!(res_update.return_value, [2, 0, 0, 0]);
        // Assert that the updated state is persisted.
        assert_eq!(res_view.return_value, [2, 0, 0, 0]);
    }

    #[test]
    fn update_with_account_transfer_to_missing_account_fails() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        let transfer_amount = Amount::from_ccd(1);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy_v1(ACC_0, "examples/integrate/a.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_integrate"),
                OwnedParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");

        let res_update = chain.contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("receive"),
            OwnedParameter::new(&ACC_1), // We haven't created ACC_1.
            transfer_amount,
            Energy::from(100000),
        );

        match res_update {
            Err(ContractUpdateError::ExecutionError {
                failure_kind: InvokeFailure::ContractReject { code, .. },
                transaction_fee,
                ..
            }) => {
                assert_eq!(code, -3); // The custom contract error code for missing account.
                assert_eq!(
                    chain.persistence_account_balance(ACC_0),
                    Some(
                        initial_balance
                            - res_deploy.transaction_fee
                            - res_init.transaction_fee
                            - transaction_fee
                    )
                );
            }
            _ => panic!("Expected contract update to fail"),
        }
    }

    #[test]
    fn update_with_integrate_reentry_works() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy_v1(ACC_0, "examples/integrate/a.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_integrate"),
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
                EntrypointName::new_unchecked("recurse"),
                OwnedParameter::new(&10u32),
                Amount::zero(),
                Energy::from(1000000),
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
            chain.persistence_account_balance(ACC_0),
            Some(
                initial_balance
                    - res_deploy.transaction_fee
                    - res_init.transaction_fee
                    - res_update.transaction_fee
            )
        );
        assert_eq!(chain.contracts.len(), 1);
        assert!(res_update.state_changed);
        let expected_res = 10 + 7 + 11 + 3 + 7 + 11;
        assert_eq!(res_update.return_value, u32::to_le_bytes(expected_res));
        // Assert that the updated state is persisted.
        assert_eq!(res_view.return_value, u32::to_le_bytes(expected_res));
    }

    #[test]
    fn update_with_rollback_and_reentry_works() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(1000000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy_v1(ACC_0, "examples/integrate/a.wasm.v1")
            .expect("Deploying valid module should work");

        let input_param: u32 = 8;

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_integrate"),
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
                EntrypointName::new_unchecked("inc-fail-on-zero"),
                OwnedParameter::new(&input_param),
                Amount::zero(),
                Energy::from(100000000),
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

        assert_eq!(
            chain.persistence_account_balance(ACC_0),
            Some(
                initial_balance
                    - res_deploy.transaction_fee
                    - res_init.transaction_fee
                    - res_update.transaction_fee
            )
        );
        assert!(res_update.state_changed);
        let expected_res = 2u32.pow(input_param) - 1;
        assert_eq!(res_update.return_value, u32::to_le_bytes(expected_res));
        // Assert that the updated state is persisted.
        assert_eq!(res_view.return_value, u32::to_le_bytes(expected_res));
    }

    #[test]
    fn rollback_of_account_balances_after_failed_contract_invoke() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        let transfer_amount = Amount::from_ccd(2);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));
        chain.create_account(ACC_1, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy_v1(ACC_0, "examples/integrate/a.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init_0 = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_integrate"),
                OwnedParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");

        let res_init_1 = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_integrate_other"),
                OwnedParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");

        let param = (res_init_1.contract_address, initial_balance, ACC_1);

        chain
            .contract_update(
                ACC_0,
                Address::Account(ACC_0),
                res_init_0.contract_address,
                EntrypointName::new_unchecked("mutate_and_forward"),
                OwnedParameter::new(&param),
                transfer_amount,
                Energy::from(100000),
            )
            .expect("Update should succeed");
    }
}

#[test]
fn update_with_fib_reentry_works() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(ACC_0, AccountInfo::new(initial_balance));

    let res_deploy = chain
        .module_deploy_v1(ACC_0, "examples/fib/a.wasm.v1")
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
            OwnedParameter::new(&6u64),
            Amount::zero(),
            Energy::from(4000000),
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
        chain.persistence_account_balance(ACC_0),
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
