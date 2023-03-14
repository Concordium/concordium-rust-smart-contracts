//! Tests for the contract default method/fallback functionality.

use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../concordium-base/smart-contracts/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);

#[test]
fn test_fallback() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy = chain
        .module_deploy_wasm_v1(ACC_0, format!("{}/fallback.wasm", WASM_TEST_FOLDER))
        .expect("Deploying valid module should work");

    let res_init_two = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_two"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");

    let res_init_one = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_one"),
            OwnedParameter::from_serial(&res_init_two.contract_address)
                .expect("Parameter has valid size"), /* Pass in address of contract
                                                      * "two". */
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");

    // Invoke the fallback directly. This should fail with execution failure/trap
    // because it will redirect to "two." which does not exist. Hence this will fail
    // and the fallback will try to look up a non-existing return value.
    let res_invoke_1 = chain
        .contract_invoke(
            ACC_0,
            Address::Account(ACC_0),
            res_init_one.contract_address,
            EntrypointName::new_unchecked(""),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect_err("should fail");
    match res_invoke_1.kind {
        ContractInvocationErrorKind::ExecutionError {
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
            res_init_one.contract_address,
            EntrypointName::new_unchecked("do"),
            parameter.clone(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Invoke should succeed.");
    assert_eq!(res_invoke_2.return_value, parameter.as_ref()); // Parameter is
                                                               // returned
                                                               // via the fallback.
}
