//! This module tests basic V1 state operations with the recorder contract.

use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../concordium-base/smart-contracts/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);

#[test]
fn test_recorder() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy = chain
        .module_deploy_wasm_v1(
            ACC_0,
            format!("{}/record-parameters.wasm", WASM_TEST_FOLDER),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_recorder"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");

    chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("record_u64"),
            OwnedParameter::from_serial(&20u64).expect("Parameter has valid size"),
            Amount::zero(),
            Energy::from(100000),
        )
        .expect("Update failed");
    chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("record_u64"),
            OwnedParameter::from_serial(&40u64).expect("Parameter has valid size"),
            Amount::zero(),
            Energy::from(100000),
        )
        .expect("Update failed");
    // Assert that all 60 values were inserted in the state.
    for key in 0..60u64 {
        assert!(chain
            .contract_state_lookup(res_init.contract_address, &u64::to_le_bytes(key))
            .is_some());
    }
}
