//! Tests for the contract default method/fallback functionality.

use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../concordium-base/smart-contracts/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);

#[test]
fn test_fallback() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/fallback.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init_two = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                mod_ref:   res_deploy.module_reference,
                init_name: OwnedContractName::new_unchecked("init_two".into()),
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let res_init_one = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                mod_ref:   res_deploy.module_reference,
                init_name: OwnedContractName::new_unchecked("init_one".into()),
                param:     OwnedParameter::from_serial(&res_init_two.contract_address)
                    .expect("Parameter has valid size"), /* Pass in address of contract
                                                          * "two". */
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    // Invoke the fallback directly. This should fail with execution failure/trap
    // because it will redirect to "two." which does not exist. Hence this will fail
    // and the fallback will try to look up a non-existing return value.
    let res_invoke_1 = chain
        .contract_invoke(
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                address:      res_init_one.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("one.".into()),
                message:      OwnedParameter::empty(),
                amount:       Amount::zero(),
            },
        )
        .expect_err("should fail");
    match res_invoke_1.kind {
        ContractInvokeErrorKind::ExecutionError {
            failure_kind: InvokeFailure::RuntimeError,
            ..
        } => (),
        _ => panic!("Test failed, expected a runtime error."),
    }

    // Invoke "two.do" via "one.do" and the fallback.
    let parameter = OwnedParameter::from_serial(&"ASDF").expect("Parameter has valid size.");
    let res_invoke_2 = chain
        .contract_invoke(
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                address:      res_init_one.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("one.do".into()),
                message:      parameter.clone(),
                amount:       Amount::zero(),
            },
        )
        .expect("Invoke should succeed.");
    assert_eq!(res_invoke_2.return_value, parameter.as_ref()); // Parameter is
                                                               // returned
                                                               // via the fallback.
}
