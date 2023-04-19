//! This module tests basic V1 state operations with the recorder contract.

use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../concordium-base/smart-contracts/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);

#[test]
fn test_recorder() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/record-parameters.wasm", WASM_TEST_FOLDER))
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
                init_name: OwnedContractName::new_unchecked("init_recorder".into()),
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(100000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("recorder.record_u64".into()),
                message:      OwnedParameter::from_serial(&20u64)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect("Update failed");
    chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(100000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("recorder.record_u64".into()),
                message:      OwnedParameter::from_serial(&40u64)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect("Update failed");
    // Assert that all 60 values were inserted in the state.
    for key in 0..60u64 {
        assert!(chain
            .contract_state_lookup(res_init.contract_address, &u64::to_le_bytes(key))
            .is_some());
    }
}
