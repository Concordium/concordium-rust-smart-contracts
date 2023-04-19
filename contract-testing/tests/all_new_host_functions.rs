//! This module tests that a module containing all the new V1 host functions is
//! accepted. It serves as a basic integration test. Individual functions either
//! have tests in wasm-chain-integration, or as part of other scheduler tests if
//! they require more complex interactions with the chain.

use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../concordium-base/smart-contracts/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);

#[test]
fn test_all_new_host_functions() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/all-new-host-functions.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");
}
