//! This module tests calling a contract which makes use of an iterator.
//! The checks are being performed in the contract itself so if invoking the
//! contract completes successfully then this implies that the tests have done
//! so as well. Note. as per above no checks are being performed in this file
//! wrt. the state etc. after execution etc.

use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../concordium-base/smart-contracts/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);

#[test]
fn test_iterator() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/iterator.wasm", WASM_TEST_FOLDER))
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
                init_name: OwnedContractName::new_unchecked("init_iterator".into()),
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
            Energy::from(10000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("iterator.iteratetest".into()),
                message:      OwnedParameter::empty(),
                amount:       Amount::zero(),
            },
        )
        .expect("Should succeed");
    chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("iterator.lockingtest".into()),
                message:      OwnedParameter::empty(),
                amount:       Amount::zero(),
            },
        )
        .expect("Should succeed.");
}
