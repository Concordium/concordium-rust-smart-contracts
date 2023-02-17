//! This module contains tests for the native smart contract upgrade
//! functionality.
use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../../concordium-node/concordium-consensus/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);

/// Test a basic upgrade, ensuring that the new module is in place by
/// checking the available entrypoints.
#[test]
fn test() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    // Deploy the two modules `upgrading_0`, `upgrading_1`
    let res_deploy_0 = chain
        .module_deploy_wasm_v1(ACC_0, format!("{}/upgrading_0.wasm", WASM_TEST_FOLDER))
        .expect("Deploying valid module should work");

    let res_deploy_1 = chain
        .module_deploy_wasm_v1(ACC_0, format!("{}/upgrading_1.wasm", WASM_TEST_FOLDER))
        .expect("Deploying valid module should work");

    // Initialize `upgrading_0`.
    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy_0.module_reference,
            ContractName::new_unchecked("init_a"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");

    // Upgrade the contract to the `upgrading_1` module by calling the `bump`
    // entrypoint.
    let res_update_upgrade = chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("bump"),
            OwnedParameter::new(&res_deploy_1.module_reference),
            Amount::zero(),
            Energy::from(100000),
        )
        .expect("Updating valid contract should work");

    // Call the `newfun` entrypoint which only exists in `upgrading_1`.
    let res_update_new = chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("newfun"),
            OwnedParameter::new(&res_deploy_1.module_reference),
            Amount::zero(),
            Energy::from(100000),
        )
        .expect("Updating the `newfun` from the `upgrading_1` module should work");

    assert!(matches!(res_update_upgrade.chain_events[..], [
                ChainEvent::Interrupted { .. },
                ChainEvent::Upgraded { from, to, .. },
                ChainEvent::Resumed { .. },
                ChainEvent::Updated { .. },
            ] if from == res_deploy_0.module_reference && to == res_deploy_1.module_reference));
    assert!(matches!(res_update_new.chain_events[..], [
        ChainEvent::Updated { .. }
    ]));
}

/// The contract in this test, triggers an upgrade and then in the same
/// invocation, calls a function in the upgraded module.
/// Checking the new module is being used.
#[test]
fn test_self_invoke() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy_0 = chain
        .module_deploy_wasm_v1(
            ACC_0,
            format!("{}/upgrading-self-invoke0.wasm", WASM_TEST_FOLDER),
        )
        .expect("Deploying valid module should work");
    let res_deploy_1 = chain
        .module_deploy_wasm_v1(
            ACC_0,
            format!("{}/upgrading-self-invoke1.wasm", WASM_TEST_FOLDER),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy_0.module_reference,
            ContractName::new_unchecked("init_contract"),
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
            EntrypointName::new_unchecked("upgrade"),
            OwnedParameter::new(&res_deploy_1.module_reference),
            Amount::zero(),
            Energy::from(100000),
        )
        .expect("Updating valid contract should work");

    assert!(matches!(res_update.chain_events[..], [
        // Invoking `contract.name`
        ChainEvent::Interrupted { .. },
        ChainEvent::Updated { .. },
        ChainEvent::Resumed { .. },
        // Making the upgrade
        ChainEvent::Interrupted { .. },
        ChainEvent::Upgraded { .. },
        ChainEvent::Resumed { .. },
        // Invoking contract.name again
        ChainEvent::Interrupted { .. },
        ChainEvent::Updated { .. },
        ChainEvent::Resumed { .. },
        // The successful update
        ChainEvent::Updated { .. },
    ]));
}

/// Test upgrading to a module that doesn't exist (it uses module
/// `[0u8;32]` inside the contract). The contract checks whether
/// the expected error is returned.
#[test]
fn test_missing_module() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy = chain
        .module_deploy_wasm_v1(
            ACC_0,
            format!("{}/upgrading-missing-module.wasm", WASM_TEST_FOLDER),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_contract"),
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
            EntrypointName::new_unchecked("upgrade"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(100000),
        )
        .expect("Updating valid contract should work");

    assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Interrupted { .. },
                // No upgrade event, as it is supposed to fail.
                ChainEvent::Resumed { success, .. },
                ChainEvent::Updated { .. },
            ] if success == false));
}

/// Test upgrading to a module where there isn't a matching contract
/// name. The contract checks whether the expected error is
/// returned.
#[test]
fn test_missing_contract() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy_0 = chain
        .module_deploy_wasm_v1(
            ACC_0,
            format!("{}/upgrading-missing-contract0.wasm", WASM_TEST_FOLDER),
        )
        .expect("Deploying valid module should work");

    let res_deploy_1 = chain
        .module_deploy_wasm_v1(
            ACC_0,
            format!("{}/upgrading-missing-contract1.wasm", WASM_TEST_FOLDER),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy_0.module_reference,
            ContractName::new_unchecked("init_contract"),
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
            EntrypointName::new_unchecked("upgrade"),
            OwnedParameter::new(&res_deploy_1.module_reference),
            Amount::zero(),
            Energy::from(100000),
        )
        .expect("Updating valid contract should work");

    assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Interrupted { .. },
                // No upgrade event, as it is supposed to fail.
                ChainEvent::Resumed { success, .. },
                ChainEvent::Updated { .. },
            ] if success == false));
}

/// Test upgrading twice in the same transaction. The effect of the
/// second upgrade should be in effect at the end.
#[test]
fn test_twice_in_one_transaction() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy_0 = chain
        .module_deploy_wasm_v1(ACC_0, format!("{}/upgrading-twice0.wasm", WASM_TEST_FOLDER))
        .expect("Deploying valid module should work");

    let res_deploy_1 = chain
        .module_deploy_wasm_v1(ACC_0, format!("{}/upgrading-twice1.wasm", WASM_TEST_FOLDER))
        .expect("Deploying valid module should work");

    let res_deploy_2 = chain
        .module_deploy_wasm_v1(ACC_0, format!("{}/upgrading-twice2.wasm", WASM_TEST_FOLDER))
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy_0.module_reference,
            ContractName::new_unchecked("init_contract"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");

    let input_param = (res_deploy_1.module_reference, res_deploy_2.module_reference);

    let res_update = chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("upgrade"),
            OwnedParameter::new(&input_param),
            Amount::zero(),
            Energy::from(100000),
        )
        .expect("Updating valid contract should work");

    assert!(matches!(res_update.chain_events[..], [
                // Invoke the contract itself to check the name entrypoint return value.
                ChainEvent::Interrupted { .. },
                ChainEvent::Updated { .. },
                ChainEvent::Resumed { .. },
                // Upgrade from module 0 to 1
                ChainEvent::Interrupted { .. },
                ChainEvent::Upgraded { from: first_from, to: first_to, .. },
                ChainEvent::Resumed { .. },
                // Invoke the contract itself to check the name again.
                ChainEvent::Interrupted { .. },
                ChainEvent::Updated { .. },
                ChainEvent::Resumed { .. },
                // Upgrade again
                ChainEvent::Interrupted { .. },
                ChainEvent::Upgraded { from: second_from, to: second_to, .. },
                ChainEvent::Resumed { .. },
                // Invoke itself again to check name a final time.
                ChainEvent::Interrupted { .. },
                ChainEvent::Updated { .. },
                ChainEvent::Resumed { .. },
                // Final update event
                ChainEvent::Updated { .. },
            ] if first_from == res_deploy_0.module_reference
                && first_to == res_deploy_1.module_reference
                && second_from == res_deploy_1.module_reference
                && second_to == res_deploy_2.module_reference));
}

/// Test upgrading to a module where there isn't a matching contract
/// name. The contract checks whether the expected error is
/// returned.
#[test]
fn test_chained_contract() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy = chain
        .module_deploy_wasm_v1(
            ACC_0,
            format!("{}/upgrading-chained0.wasm", WASM_TEST_FOLDER),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_contract"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");

    let number_of_upgrades: u32 = 82; // TODO: Stack will overflow if larger than 82.
    let input_param = (number_of_upgrades, res_deploy.module_reference);

    let res_update = chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("upgrade"),
            OwnedParameter::new(&input_param),
            Amount::zero(),
            Energy::from(1000000),
        )
        .expect("Updating valid contract should work");

    // Per upgrade: 3 events for invoking itself + 3 events for the upgrade.
    // Ends with 4 extra events: 3 events for an upgrade and 1 event for succesful
    // update.
    assert_eq!(
        res_update.chain_events.len() as u32,
        6 * number_of_upgrades + 4
    )
}

/// Tests whether a contract which triggers a succesful upgrade,
/// but rejects the transaction from another cause, rollbacks the
/// upgrade as well.
#[test]
fn test_reject() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy_0 = chain
        .module_deploy_wasm_v1(
            ACC_0,
            format!("{}/upgrading-reject0.wasm", WASM_TEST_FOLDER),
        )
        .expect("Deploying valid module should work");

    let res_deploy_1 = chain
        .module_deploy_wasm_v1(
            ACC_0,
            format!("{}/upgrading-reject1.wasm", WASM_TEST_FOLDER),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy_0.module_reference,
            ContractName::new_unchecked("init_contract"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");

    let res_update_upgrade = chain.contract_update(
        ACC_0,
        Address::Account(ACC_0),
        res_init.contract_address,
        EntrypointName::new_unchecked("upgrade"),
        OwnedParameter::new(&res_deploy_1.module_reference),
        Amount::zero(),
        Energy::from(1000000),
    );

    let res_update_new_feature = chain.contract_update(
        ACC_0,
        Address::Account(ACC_0),
        res_init.contract_address,
        EntrypointName::new_unchecked("new_feature"),
        OwnedParameter::empty(),
        Amount::zero(),
        Energy::from(1000000),
    );

    // Check the return value manually returned by the contract.
    match res_update_upgrade {
        Err(ContractUpdateError::ExecutionError { failure_kind, .. }) => match failure_kind {
            InvokeFailure::ContractReject { code, .. } if code == -1 => (),
            _ => panic!("Expected ContractReject with code == -1"),
        },
        _ => panic!("Expected Err(ContractUpdateError::ExecutionError)"),
    }

    // Assert that the new_feature entrypoint doesn't exist since the upgrade
    // failed.
    assert!(matches!(
        res_update_new_feature,
        Err(ContractUpdateError::ExecutionError {
            failure_kind:    InvokeFailure::NonExistentEntrypoint,
            energy_used:     _,
            transaction_fee: _,
        })
    ));
}

/// Tests calling an entrypoint introduced by an upgrade of the module
/// can be called and whether an entrypoint removed by an upgrade fail
/// with the appropriate reject reason.
#[test]
fn test_changing_entrypoint() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy_0 = chain
        .module_deploy_wasm_v1(
            ACC_0,
            format!("{}/upgrading-changing-entrypoints0.wasm", WASM_TEST_FOLDER),
        )
        .expect("Deploying valid module should work");

    let res_deploy_1 = chain
        .module_deploy_wasm_v1(
            ACC_0,
            format!("{}/upgrading-changing-entrypoints1.wasm", WASM_TEST_FOLDER),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy_0.module_reference,
            ContractName::new_unchecked("init_contract"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");

    let res_update_old_feature_0 = chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("old_feature"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(1000000),
        )
        .expect("Updating old_feature on old module should work.");

    let res_update_new_feature_0 = chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("new_feature"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(1000000),
        )
        .expect_err("Updating new_feature on old module should _not_ work");

    let res_update_upgrade = chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("upgrade"),
            OwnedParameter::new(&res_deploy_1.module_reference),
            Amount::zero(),
            Energy::from(1000000),
        )
        .expect("Upgrading contract should work.");

    let res_update_old_feature_1 = chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("old_feature"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(1000000),
        )
        .expect_err("Updating old_feature on _new_ module should _not_ work.");

    let res_update_new_feature_1 = chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("new_feature"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(1000000),
        )
        .expect("Updating new_feature on _new_ module should work");

    assert!(matches!(res_update_old_feature_0.chain_events[..], [
        ChainEvent::Updated { .. }
    ]));
    assert!(matches!(
        res_update_new_feature_0,
        ContractUpdateError::ExecutionError {
            failure_kind:    InvokeFailure::NonExistentEntrypoint,
            energy_used:     _,
            transaction_fee: _,
        }
    ));
    assert!(matches!(res_update_upgrade.chain_events[..], [
        ChainEvent::Interrupted { .. },
        ChainEvent::Upgraded { .. },
        ChainEvent::Resumed { .. },
        ChainEvent::Updated { .. },
    ]));
    assert!(matches!(
        res_update_old_feature_1,
        ContractUpdateError::ExecutionError {
            failure_kind:    InvokeFailure::NonExistentEntrypoint,
            energy_used:     _,
            transaction_fee: _,
        }
    ));
    assert!(matches!(res_update_new_feature_1.chain_events[..], [
        ChainEvent::Updated { .. }
    ]));
}
