//! This module contains tests for smart contract module reference and name
//! queries. These tests match equivalent tests for the scheduler in the node.
use std::io::Write;

use concordium_smart_contract_testing::*;
mod helpers;

#[macro_export]
/// Macro for a pattern that matches a [ContractInvokeError] where the contract
/// rejects with the supplied error code.
macro_rules! ContractInvokeErrorCode {
    ($x:expr) => {
        ContractInvokeError {
            kind: ContractInvokeErrorKind::ExecutionError {
                failure_kind: InvokeFailure::ContractReject {
                    code: $x,
                    ..
                },
            },
            ..
        }
    };
}

#[test]
/// This test deploys three different smart contracts, from two different
/// modules. One of these contracts <0,0> has a function for checking if the
/// module reference matches an expected value. Another <2,0> has a function for
/// checking if the contract name matches an expected value. Both functions are
/// invoked for each instance, and for non-existant contract addresses, ensuring
/// the values are as expected.
///
/// The entrypoints are designed to succeed in the case of a match, fail with
/// code -1 if there is a mismatch, and fail with code -2 if the contract
/// address does not exist. If the protocol version does not support the
/// contract inspection functionality, then the call should fail with
/// a runtime exception.
fn test_module_ref_and_name() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(100);
    chain.create_account(Account::new(helpers::ACC_0, initial_balance));

    // We use two contract modules for this test.
    let mod_contract_inspection =
        module_load_v1_raw(helpers::wasm_test_file("queries-contract-inspection.wasm"))
            .expect("module should exist");
    let mod_account_balance =
        module_load_v1_raw(helpers::wasm_test_file("queries-account-balance.wasm"))
            .expect("module should exist");

    // Deploy the modules
    let res_deploy_contract_inspection = chain
        .module_deploy_v1(Signer::with_one_key(), helpers::ACC_0, mod_contract_inspection)
        .expect("Deploying valid module should work");
    let res_deploy_account_balance = chain
        .module_deploy_v1(Signer::with_one_key(), helpers::ACC_0, mod_account_balance)
        .expect("Deploying valid module should work");

    // Initialise three contracts.
    let res_init_0 = chain
        .contract_init(
            Signer::with_one_key(),
            helpers::ACC_0,
            Energy::from(100000),
            InitContractPayload {
                init_name: OwnedContractName::new_unchecked("init_contract".into()),
                mod_ref:   res_deploy_contract_inspection.module_reference,
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");
    let res_init_1 = chain
        .contract_init(
            Signer::with_one_key(),
            helpers::ACC_0,
            Energy::from(100000),
            InitContractPayload {
                init_name: OwnedContractName::new_unchecked("init_contract".into()),
                mod_ref:   res_deploy_account_balance.module_reference,
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");
    let res_init_2 = chain
        .contract_init(
            Signer::with_one_key(),
            helpers::ACC_0,
            Energy::from(100000),
            InitContractPayload {
                init_name: OwnedContractName::new_unchecked("init_contract2".into()),
                mod_ref:   res_deploy_contract_inspection.module_reference,
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    // Use contract 0 to check the module addresses of the contracts.
    let check_module_ref =
        |chain: &mut Chain, address: ContractAddress, mod_ref: ModuleReference| {
            let input_param = (address, mod_ref);
            chain.contract_update(
                Signer::with_one_key(),
                helpers::ACC_0,
                Address::Account(helpers::ACC_0),
                Energy::from(100000),
                UpdateContractPayload {
                    address:      res_init_0.contract_address,
                    receive_name: OwnedReceiveName::new_unchecked(
                        "contract.check_module_reference".into(),
                    ),
                    message:      OwnedParameter::from_serial(&input_param)
                        .expect("Parameter has valid size"),
                    amount:       Amount::zero(),
                },
            )
        };
    let res = check_module_ref(
        &mut chain,
        res_init_0.contract_address,
        res_deploy_contract_inspection.module_reference,
    );
    assert!(
        matches!(res, Ok(..)),
        "Contract 0 should match contract inspection contract, but result was: {:?}",
        res
    );
    let res = check_module_ref(
        &mut chain,
        res_init_1.contract_address,
        res_deploy_contract_inspection.module_reference,
    );
    assert!(
        matches!(res, Err(ContractInvokeErrorCode!(-1))),
        "Contract 1 should not match contract inspection contract, but result was: {:?}",
        res
    );
    let res = check_module_ref(
        &mut chain,
        res_init_2.contract_address,
        res_deploy_contract_inspection.module_reference,
    );
    assert!(
        matches!(res, Ok(..)),
        "Contract 0 should match contract inspection contract, but result was: {:?}",
        res
    );
    let res = check_module_ref(
        &mut chain,
        ContractAddress {
            index:    3,
            subindex: 0,
        },
        res_deploy_contract_inspection.module_reference,
    );
    assert!(
        matches!(res, Err(ContractInvokeErrorCode!(-2))),
        "Contract <3,0> should not exist, but result was: {:?}",
        res
    );
    let res = check_module_ref(
        &mut chain,
        ContractAddress {
            index:    0,
            subindex: 1,
        },
        res_deploy_contract_inspection.module_reference,
    );
    assert!(
        matches!(res, Err(ContractInvokeErrorCode!(-2))),
        "Contract <0,1> should not exist, but result was: {:?}",
        res
    );
    let res = check_module_ref(
        &mut chain,
        res_init_1.contract_address,
        res_deploy_account_balance.module_reference,
    );
    assert!(
        matches!(res, Ok(..)),
        "Contract 1 should match account balance contract, but result was: {:?}",
        res
    );

    // Use contract 2 to check the contract name of the contracts.
    let check_name = |chain: &mut Chain, address: ContractAddress, name: &str| {
        let mut input_param = Vec::with_capacity(16 + name.len());
        concordium_rust_sdk::base::contracts_common::Serial::serial(&address, &mut input_param)
            .unwrap();
        println!("{:?}", &input_param);
        input_param.write_all(name.as_bytes()).unwrap();
        let op = OwnedParameter::try_from(input_param);
        println!("{:?}", &op);
        chain.contract_update(
            Signer::with_one_key(),
            helpers::ACC_0,
            Address::Account(helpers::ACC_0),
            Energy::from(100000),
            UpdateContractPayload {
                address:      res_init_2.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract2.check_name".into()),
                message:      op.expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
    };
    let res = check_name(&mut chain, res_init_0.contract_address, "init_contract");
    assert!(
        matches!(res, Ok(..)),
        "Contract 0 should match 'init_contract', but result was: {:?}",
        res
    );
    let res = check_name(&mut chain, res_init_1.contract_address, "init_contract");
    assert!(
        matches!(res, Ok(..)),
        "Contract 1 should match 'init_contract', but result was: {:?}",
        res
    );
    let res = check_name(&mut chain, res_init_2.contract_address, "init_contract");
    assert!(
        matches!(res, Err(ContractInvokeErrorCode!(-1))),
        "Contract 2 should not match 'init_contract', but result was: {:?}",
        res
    );
    let res = check_name(&mut chain, res_init_2.contract_address, "init_contract2");
    assert!(
        matches!(res, Ok(..)),
        "Contract 2 should match 'init_contract2', but result was: {:?}",
        res
    );
    let res = check_name(
        &mut chain,
        ContractAddress {
            index:    3,
            subindex: 0,
        },
        "init_contract",
    );
    assert!(
        matches!(res, Err(ContractInvokeErrorCode!(-2))),
        "Contract <3,0> should not exist, but result was: {:?}",
        res
    );
    let res = check_name(&mut chain, res_init_0.contract_address, "init_contract2");
    assert!(
        matches!(res, Err(ContractInvokeErrorCode!(-1))),
        "Contract 0 should not match 'init_contract2', but result was: {:?}",
        res
    );
    let res = check_name(
        &mut chain,
        ContractAddress {
            index:    0,
            subindex: 1,
        },
        "init_contract2",
    );
    assert!(
        matches!(res, Err(ContractInvokeErrorCode!(-2))),
        "Contract <0,1> should not exist, but result was: {:?}",
        res
    );
}

#[test]
/// Test the interaction between upgrading a contract and querying the contract
/// module reference.
fn test_upgrade_module_ref() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(100);
    chain.create_account(Account::new(helpers::ACC_0, initial_balance));

    // We use two contract modules for this test.
    let mod_0 = module_load_v1_raw(helpers::wasm_test_file("upgrading-inspect-module0.wasm"))
        .expect("module should exist");
    let mod_1 = module_load_v1_raw(helpers::wasm_test_file("upgrading-inspect-module1.wasm"))
        .expect("module should exist");

    // Deploy the modules
    let res_deploy_0 = chain
        .module_deploy_v1(Signer::with_one_key(), helpers::ACC_0, mod_0)
        .expect("Deploying valid module should work");
    let res_deploy_1 = chain
        .module_deploy_v1(Signer::with_one_key(), helpers::ACC_0, mod_1)
        .expect("Deploying valid module should work");

    // Initialise three contracts.
    let res_init_0 = chain
        .contract_init(
            Signer::with_one_key(),
            helpers::ACC_0,
            Energy::from(100000),
            InitContractPayload {
                init_name: OwnedContractName::new_unchecked("init_contract".into()),
                mod_ref:   res_deploy_0.module_reference,
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let check_module_ref =
        |chain: &mut Chain, address: ContractAddress, mod_ref: ModuleReference| {
            let input_param = (address, mod_ref);
            let op = OwnedParameter::from_serial(&input_param);
            println!("{:?}", &op);
            chain.contract_update(
                Signer::with_one_key(),
                helpers::ACC_0,
                Address::Account(helpers::ACC_0),
                Energy::from(100000),
                UpdateContractPayload {
                    address:      res_init_0.contract_address,
                    receive_name: OwnedReceiveName::new_unchecked(
                        "contract.check_module_reference".into(),
                    ),
                    message:      OwnedParameter::from_serial(&input_param)
                        .expect("Parameter has valid size"),
                    amount:       Amount::zero(),
                },
            )
        };
    let res =
        check_module_ref(&mut chain, res_init_0.contract_address, res_deploy_0.module_reference);
    assert!(matches!(res, Ok(..)), "Contract 0 should match contract 0, but result was: {:?}", res);
    let res =
        check_module_ref(&mut chain, res_init_0.contract_address, res_deploy_1.module_reference);
    assert!(
        matches!(res, Err(ContractInvokeErrorCode!(-1))),
        "Contract 0 should not match contract 1, but result was: {:?}",
        res
    );
    // Upgrade the contract. This also checks that the module reference changes
    // after the upgrade.
    let res = chain.contract_update(
        Signer::with_one_key(),
        helpers::ACC_0,
        Address::Account(helpers::ACC_0),
        Energy::from(100000),
        UpdateContractPayload {
            address:      res_init_0.contract_address,
            receive_name: OwnedReceiveName::new_unchecked("contract.upgrade".into()),
            message:      OwnedParameter::from_serial(&res_deploy_1.module_reference)
                .expect("Parameter has valid size"),
            amount:       Amount::zero(),
        },
    );
    assert!(matches!(res, Ok(..)), "Contract upgrade should succeed, but result was: {:?}", res);

    // Check the module reference after the update.
    let res =
        check_module_ref(&mut chain, res_init_0.contract_address, res_deploy_1.module_reference);
    assert!(matches!(res, Ok(..)), "Contract 0 should match contract 1, but result was: {:?}", res);
    let res =
        check_module_ref(&mut chain, res_init_0.contract_address, res_deploy_0.module_reference);
    assert!(
        matches!(res, Err(ContractInvokeErrorCode!(-1))),
        "Contract 0 should not match contract 0, but result was: {:?}",
        res
    );
}
