//! This module contains tests for the native smart contract upgrade
//! functionality.
use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../concordium-base/smart-contracts/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);

/// Test a basic upgrade, ensuring that the new module is in place by
/// checking the available entrypoints.
#[test]
fn test() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    // Deploy the two modules `upgrading_0`, `upgrading_1`
    let res_deploy_0 = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/upgrading_0.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_deploy_1 = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/upgrading_1.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    // Initialize `upgrading_0`.
    let res_init = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                init_name: OwnedContractName::new_unchecked("init_a".into()),
                mod_ref:   res_deploy_0.module_reference,

                param:  OwnedParameter::empty(),
                amount: Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    // Upgrade the contract to the `upgrading_1` module by calling the `bump`
    // entrypoint.
    let res_update_upgrade = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(100000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("a.bump".into()),
                message:      OwnedParameter::from_serial(&res_deploy_1.module_reference)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating valid contract should work");

    // Call the `newfun` entrypoint which only exists in `upgrading_1`.
    let res_update_new = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(100000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("a.newfun".into()),
                message:      OwnedParameter::from_serial(&res_deploy_1.module_reference)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating the `newfun` from the `upgrading_1` module should work");

    assert!(
        matches!(res_update_upgrade.effective_trace_elements_cloned()[..], [
                ContractTraceElement::Interrupted { .. },
                ContractTraceElement::Upgraded { from, to, .. },
                ContractTraceElement::Resumed { .. },
                ContractTraceElement::Updated { .. },
            ] if from == res_deploy_0.module_reference && to == res_deploy_1.module_reference)
    );
    assert!(matches!(
        res_update_new.effective_trace_elements_cloned()[..],
        [ContractTraceElement::Updated { .. }]
    ));
}

/// The contract in this test, triggers an upgrade and then in the same
/// invocation, calls a function in the upgraded module.
/// Checking the new module is being used.
#[test]
fn test_self_invoke() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy_0 = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/upgrading-self-invoke0.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");
    let res_deploy_1 = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/upgrading-self-invoke1.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                init_name: OwnedContractName::new_unchecked("init_contract".into()),
                param:     OwnedParameter::empty(),
                mod_ref:   res_deploy_0.module_reference,
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let res_update = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(100000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract.upgrade".into()),
                message:      OwnedParameter::from_serial(&res_deploy_1.module_reference)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating valid contract should work");

    assert!(matches!(
        res_update.effective_trace_elements_cloned()[..],
        [
            // Invoking `contract.name`
            ContractTraceElement::Interrupted { .. },
            ContractTraceElement::Updated { .. },
            ContractTraceElement::Resumed { .. },
            // Making the upgrade
            ContractTraceElement::Interrupted { .. },
            ContractTraceElement::Upgraded { .. },
            ContractTraceElement::Resumed { .. },
            // Invoking contract.name again
            ContractTraceElement::Interrupted { .. },
            ContractTraceElement::Updated { .. },
            ContractTraceElement::Resumed { .. },
            // The successful update
            ContractTraceElement::Updated { .. },
        ]
    ));
}

/// Test upgrading to a module that doesn't exist (it uses module
/// `[0u8;32]` inside the contract). The contract checks whether
/// the expected error is returned.
#[test]
fn test_missing_module() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!(
                "{}/upgrading-missing-module.wasm",
                WASM_TEST_FOLDER
            ))
            .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                mod_ref:   res_deploy.module_reference,
                init_name: OwnedContractName::new_unchecked("init_contract".into()),
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let res_update = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(100000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract.upgrade".into()),
                message:      OwnedParameter::empty(),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating valid contract should work");

    assert!(matches!(res_update.effective_trace_elements_cloned()[..], [
                ContractTraceElement::Interrupted { .. },
                // No upgrade event, as it is supposed to fail.
                ContractTraceElement::Resumed { success, .. },
                ContractTraceElement::Updated { .. },
            ] if !success ));
}

/// Test upgrading to a module where there isn't a matching contract
/// name. The contract checks whether the expected error is
/// returned.
#[test]
fn test_missing_contract() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy_0 = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!(
                "{}/upgrading-missing-contract0.wasm",
                WASM_TEST_FOLDER
            ))
            .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_deploy_1 = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!(
                "{}/upgrading-missing-contract1.wasm",
                WASM_TEST_FOLDER
            ))
            .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                init_name: OwnedContractName::new_unchecked("init_contract".into()),
                param:     OwnedParameter::empty(),
                mod_ref:   res_deploy_0.module_reference,

                amount: Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let res_update = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(100000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract.upgrade".into()),
                message:      OwnedParameter::from_serial(&res_deploy_1.module_reference)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating valid contract should work");

    assert!(matches!(res_update.effective_trace_elements_cloned()[..], [
                ContractTraceElement::Interrupted { .. },
                // No upgrade event, as it is supposed to fail.
                ContractTraceElement::Resumed { success, .. },
                ContractTraceElement::Updated { .. },
            ] if !success ));
}

/// Test upgrading twice in the same transaction. The effect of the
/// second upgrade should be in effect at the end.
#[test]
fn test_twice_in_one_transaction() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy_0 = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/upgrading-twice0.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_deploy_1 = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/upgrading-twice1.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_deploy_2 = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/upgrading-twice2.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                init_name: OwnedContractName::new_unchecked("init_contract".into()),
                param:     OwnedParameter::empty(),
                mod_ref:   res_deploy_0.module_reference,

                amount: Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let input_param = (res_deploy_1.module_reference, res_deploy_2.module_reference);

    let res_update = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(100000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract.upgrade".into()),
                message:      OwnedParameter::from_serial(&input_param)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating valid contract should work");

    assert!(matches!(res_update.effective_trace_elements_cloned()[..], [
                // Invoke the contract itself to check the name entrypoint return value.
                ContractTraceElement::Interrupted { .. },
                ContractTraceElement::Updated { .. },
                ContractTraceElement::Resumed { .. },
                // Upgrade from module 0 to 1
                ContractTraceElement::Interrupted { .. },
                ContractTraceElement::Upgraded { from: first_from, to: first_to, .. },
                ContractTraceElement::Resumed { .. },
                // Invoke the contract itself to check the name again.
                ContractTraceElement::Interrupted { .. },
                ContractTraceElement::Updated { .. },
                ContractTraceElement::Resumed { .. },
                // Upgrade again
                ContractTraceElement::Interrupted { .. },
                ContractTraceElement::Upgraded { from: second_from, to: second_to, .. },
                ContractTraceElement::Resumed { .. },
                // Invoke itself again to check name a final time.
                ContractTraceElement::Interrupted { .. },
                ContractTraceElement::Updated { .. },
                ContractTraceElement::Resumed { .. },
                // Final update event
                ContractTraceElement::Updated { .. },
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
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/upgrading-chained0.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                mod_ref:   res_deploy.module_reference,
                init_name: OwnedContractName::new_unchecked("init_contract".into()),
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    // High number here tests we don't have stack overflows due to recursion or
    // other accidental stack usage.
    let number_of_upgrades: u32 = 1_000;
    let input_param = (number_of_upgrades, res_deploy.module_reference);

    let res_update = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(1_000_000_000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract.upgrade".into()),
                message:      OwnedParameter::from_serial(&input_param)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating valid contract should work");

    // Per upgrade: 3 events for invoking itself + 3 events for the upgrade.
    // Ends with 4 extra events: 3 events for an upgrade and 1 event for succesful
    // update.
    assert_eq!(
        res_update.effective_trace_elements_cloned().len() as u32,
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
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy_0 = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/upgrading-reject0.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_deploy_1 = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/upgrading-reject1.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                mod_ref:   res_deploy_0.module_reference,
                init_name: OwnedContractName::new_unchecked("init_contract".into()),
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let res_update_upgrade = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(1000000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract.upgrade".into()),
                message:      OwnedParameter::from_serial(&res_deploy_1.module_reference)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect_err("should fail");

    let res_update_new_feature = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(1000000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract.new_feature".into()),
                message:      OwnedParameter::empty(),
                amount:       Amount::zero(),
            },
        )
        .expect_err("should fail");

    // Check the return value manually returned by the contract.
    match res_update_upgrade.kind {
        ContractInvokeErrorKind::ExecutionError { failure_kind, .. } => match failure_kind {
            InvokeFailure::ContractReject { code, .. } if code == -1 => (),
            _ => panic!("Expected ContractReject with code == -1"),
        },
        _ => panic!("Expected Err(ContractUpdateError::ExecutionError)"),
    }

    // Assert that the new_feature entrypoint doesn't exist since the upgrade
    // failed.
    assert!(matches!(
        res_update_new_feature.kind,
        ContractInvokeErrorKind::ExecutionError {
            failure_kind: InvokeFailure::NonExistentEntrypoint,
        }
    ));
}

/// Tests calling an entrypoint introduced by an upgrade of the module
/// can be called and whether an entrypoint removed by an upgrade fail
/// with the appropriate reject reason.
#[test]
fn test_changing_entrypoint() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy_0 = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!(
                "{}/upgrading-changing-entrypoints0.wasm",
                WASM_TEST_FOLDER
            ))
            .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_deploy_1 = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!(
                "{}/upgrading-changing-entrypoints1.wasm",
                WASM_TEST_FOLDER
            ))
            .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                init_name: OwnedContractName::new_unchecked("init_contract".into()),
                param:     OwnedParameter::empty(),
                mod_ref:   res_deploy_0.module_reference,

                amount: Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let res_update_old_feature_0 = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(1000000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract.old_feature".into()),
                message:      OwnedParameter::empty(),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating old_feature on old module should work.");

    let res_update_new_feature_0 = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(1000000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract.new_feature".into()),
                message:      OwnedParameter::empty(),
                amount:       Amount::zero(),
            },
        )
        .expect_err("Updating new_feature on old module should _not_ work");

    let res_update_upgrade = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(1000000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract.upgrade".into()),
                message:      OwnedParameter::from_serial(&res_deploy_1.module_reference)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect("Upgrading contract should work.");

    let res_update_old_feature_1 = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(1000000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract.old_feature".into()),
                message:      OwnedParameter::empty(),
                amount:       Amount::zero(),
            },
        )
        .expect_err("Updating old_feature on _new_ module should _not_ work.");

    let res_update_new_feature_1 = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(1000000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract.new_feature".into()),
                message:      OwnedParameter::empty(),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating new_feature on _new_ module should work");

    assert!(matches!(
        res_update_old_feature_0.effective_trace_elements_cloned()[..],
        [ContractTraceElement::Updated { .. }]
    ));
    assert!(matches!(
        res_update_new_feature_0.kind,
        ContractInvokeErrorKind::ExecutionError {
            failure_kind: InvokeFailure::NonExistentEntrypoint,
        }
    ));
    assert!(matches!(
        res_update_upgrade.effective_trace_elements_cloned()[..],
        [
            ContractTraceElement::Interrupted { .. },
            ContractTraceElement::Upgraded { .. },
            ContractTraceElement::Resumed { .. },
            ContractTraceElement::Updated { .. },
        ]
    ));
    assert!(matches!(
        res_update_old_feature_1.kind,
        ContractInvokeErrorKind::ExecutionError {
            failure_kind: InvokeFailure::NonExistentEntrypoint,
        }
    ));
    assert!(matches!(
        res_update_new_feature_1.effective_trace_elements_cloned()[..],
        [ContractTraceElement::Updated { .. }]
    ));
}
