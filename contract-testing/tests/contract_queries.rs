//! This module contains tests for smart contract module reference and name
//! queries. These tests match equivalent tests for the scheduler in the node.

use concordium_smart_contract_testing::*;
mod helpers;

#[test]
/// This test deploys three different smart contracts, from two different
/// modules.  One of these contracts <0,0> has a function that queries and logs
/// the module reference of a  specified contract address. Another <2,0> queries
/// and logs the contract name of a specified contract. Both functions are
/// invoked for each instance, and for non-existant contract addresses,
/// ensuring the values are as expected.
///
/// The entrypoints are designed to succeed in the case of a match, fail with
/// code -1 if there is a mismatch, and fail with code -2 if the contract
/// address does not exist. If the protocol version does not support the
/// contract inspection functionality, then the call should fail with
/// a runtime exception.
///
/// In addition to checking the results, this test also checks that the energy
/// used matches the expected value.
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

    // Use contract 0 to get the module references of the contracts.
    let get_module_ref = |chain: &mut Chain,
                          address: ContractAddress|
     -> Result<(ModuleReference, Energy), ContractInvokeError> {
        let success = chain.contract_update(
            Signer::with_one_key(),
            helpers::ACC_0,
            Address::Account(helpers::ACC_0),
            Energy::from(100000),
            UpdateContractPayload {
                address:      res_init_0.contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "contract.get_module_reference".into(),
                ),
                message:      OwnedParameter::from_serial(&address)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )?;
        let ev = success
            .events()
            .next()
            .expect("get_module_reference should produce an event on success");
        if let (_, [e]) = ev {
            Ok((e.parse().expect("event should parse"), success.energy_used))
        } else {
            panic!("get_module_reference should have a single event")
        }
    };
    let res = get_module_ref(&mut chain, res_init_0.contract_address)
        .expect("Contract 0 should be valid");
    assert_eq!(
        res.0, res_deploy_contract_inspection.module_reference,
        "Contract 0 should match contract inspection contract"
    );
    assert_eq!(res.1, 775.into(), "Expected energy to get module reference '{}'", res.0);
    let res = get_module_ref(&mut chain, res_init_1.contract_address)
        .expect("Contract 1 should be valid");
    assert_eq!(
        res.0, res_deploy_account_balance.module_reference,
        "Contract 1 should match contract inspection contract"
    );
    assert_eq!(res.1, 775.into(), "Expected energy to get module reference '{}'", res.0);
    let res = get_module_ref(&mut chain, res_init_2.contract_address)
        .expect("Contract 2 should be valid");
    assert_eq!(
        res.0, res_deploy_contract_inspection.module_reference,
        "Contract 2 should match contract inspection contract"
    );
    assert_eq!(res.1, 775.into(), "Expected energy to get module reference '{}'", res.0);
    let err = get_module_ref(&mut chain, ContractAddress {
        index:    3,
        subindex: 0,
    })
    .expect_err("Contract <3,0> should be invalid");
    assert_eq!(err.reject_code(), Some(-1), "Rejection code for get_module_ref on <3,0>");
    assert_eq!(err.energy_used, 743.into(), "Expected energy for failed get module ref.");
    let err = get_module_ref(&mut chain, ContractAddress {
        index:    1,
        subindex: 1,
    })
    .expect_err("Contract <0,1> should be invalid");
    assert_eq!(err.reject_code(), Some(-1), "Rejection code for get_module_ref on <0,1>");
    assert_eq!(err.energy_used, 743.into(), "Expected energy for failed get module ref.");

    // Use contract 2 to check the contract name of the contracts.
    let get_name = |chain: &mut Chain,
                    address: ContractAddress|
     -> Result<(OwnedContractName, Energy), ContractInvokeError> {
        let success = chain.contract_update(
            Signer::with_one_key(),
            helpers::ACC_0,
            Address::Account(helpers::ACC_0),
            Energy::from(100000),
            UpdateContractPayload {
                address:      res_init_2.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract2.get_contract_name".into()),
                message:      OwnedParameter::from_serial(&address)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )?;
        let ev =
            success.events().next().expect("get_contract_name should produce an event on success");
        if let (_, [e]) = ev {
            let name_str = std::str::from_utf8(e.as_ref()).expect("event should be utf8");
            let name = ContractName::new(name_str).expect("event should be a valid contract name");
            Ok((name.to_owned(), success.energy_used))
        } else {
            panic!("get_contract_name should have a single event")
        }
    };
    let res =
        get_name(&mut chain, res_init_0.contract_address).expect("Contract 0 should be valid");
    assert_eq!(
        res.0.as_contract_name(),
        ContractName::new_unchecked("init_contract"),
        "Contract 0 name"
    );
    assert_eq!(
        res.1,
        754.into(),
        "Expected energy for get_contract_name on {}",
        res.0.as_contract_name()
    );
    let res =
        get_name(&mut chain, res_init_1.contract_address).expect("Contract 1 should be valid");
    assert_eq!(
        res.0.as_contract_name(),
        ContractName::new_unchecked("init_contract"),
        "Contract 1 name"
    );
    assert_eq!(
        res.1,
        754.into(),
        "Expected energy for get_contract_name on {}",
        res.0.as_contract_name()
    );
    let res =
        get_name(&mut chain, res_init_2.contract_address).expect("Contract 0 should be valid");
    assert_eq!(
        res.0.as_contract_name(),
        ContractName::new_unchecked("init_contract2"),
        "Contract 2 name"
    );
    assert_eq!(
        res.1,
        755.into(),
        "Expected energy for get_contract_name on {}",
        res.0.as_contract_name()
    );
    let err = get_name(&mut chain, ContractAddress {
        index:    3,
        subindex: 0,
    })
    .expect_err("Contract <3,0> should be invalid");
    assert_eq!(err.reject_code(), Some(-1), "Rejection code for get_module_ref on <3,0>");
    assert_eq!(err.energy_used, 741.into(), "Expected energy for failed get_contract_name");
    let err = get_name(&mut chain, ContractAddress {
        index:    1,
        subindex: 1,
    })
    .expect_err("Contract <0,1> should be invalid");
    assert_eq!(err.reject_code(), Some(-1), "Rejection code for get_module_ref on <0,1>");
    assert_eq!(err.energy_used, 741.into(), "Expected energy for failed get_contract_name");
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

    // Initialise the contract.
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
    assert!(matches!(res, Ok(..)), "Contract 0 should match module 0, but result was: {:?}", res);
    let err =
        check_module_ref(&mut chain, res_init_0.contract_address, res_deploy_1.module_reference)
            .expect_err("Contract 0 should not match module 1");
    assert_eq!(
        err.reject_code(),
        Some(-1),
        "Should reject with code -1, but result was: {:?}",
        err
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
    assert!(matches!(res, Ok(..)), "Contract 0 should match module 1, but result was: {:?}", res);
    let err =
        check_module_ref(&mut chain, res_init_0.contract_address, res_deploy_0.module_reference)
            .expect_err("Contract 0 should not match module 1");
    assert_eq!(
        err.reject_code(),
        Some(-1),
        "Should reject with code -1, but result was: {:?}",
        err
    );
}
