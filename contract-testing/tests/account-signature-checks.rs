//! This module contains tests for checking account signatures, and retrieving
//! account's public keys.
use concordium_rust_sdk::base::{
    contracts_common::{self, AccountBalance, AccountThreshold, SignatureThreshold},
    id::types::AccountKeys,
    transactions::AccountAccessStructure,
};
use concordium_smart_contract_testing::*;
mod helpers;

/// Test that we can query the correct account keys.
#[test]
fn test() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    let mut csprng = rand::thread_rng();
    let acc_keys = AccountKeys::generate(
        AccountThreshold::TWO,
        &[
            (
                3.into(),
                SignatureThreshold::TWO,
                &[7.into(), 8.into(), 17.into()],
            ),
            (
                7.into(),
                SignatureThreshold::ONE,
                &[3.into(), 8.into(), 33.into()],
            ),
            (
                37.into(),
                SignatureThreshold::ONE,
                &[2.into(), 8.into(), 255.into()],
            ),
            (
                254.into(),
                SignatureThreshold::TWO,
                &[1.into(), 2.into(), 3.into()],
            ),
        ],
        &mut csprng,
    );
    let acc_structure: AccountAccessStructure = (&acc_keys).into();
    chain.create_account(Account::new_with_keys(
        helpers::ACC_0,
        AccountBalance {
            total: initial_balance,
            staked: Amount::zero(),
            locked: Amount::zero(),
        },
        acc_structure.clone(),
    ));

    let res_deploy = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            helpers::ACC_0,
            module_load_v1_raw(helpers::wasm_test_file("account-signature-checks.wasm"))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            Signer::with_one_key(),
            helpers::ACC_0,
            Energy::from(10000),
            InitContractPayload {
                init_name: OwnedContractName::new_unchecked("init_contract".into()),
                mod_ref: res_deploy.module_reference,

                param: OwnedParameter::empty(),
                amount: Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let res_invoke_get_keys = chain
        .contract_invoke(
            helpers::ACC_0,
            Address::Account(helpers::ACC_0),
            Energy::from(100000),
            UpdateContractPayload {
                address: res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract.get_keys".into()),
                message: OwnedParameter::from_serial(&helpers::ACC_0)
                    .expect("Parameter has valid size"),
                amount: Amount::zero(),
            },
        )
        .expect("Querying contract should work");
    let rv =
        contracts_common::from_bytes::<AccountAccessStructure>(&res_invoke_get_keys.return_value)
            .expect("Return value should be deserializable.");
    assert_eq!(
        rv, acc_structure,
        "Retrieved account structure does not match the expected one."
    );

    // Data is a serialization of a 30-element byte array with 4 byte length prefix
    // (in little endian).
    let data: [u8; 34] = [
        30, 0, 0, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 30, 31, 32, 33, 34,
    ];
    let signatures = AccountSignatures::from(acc_keys.sign_data(&data[4..]));

    let res_invoke_check_signature = chain
        .contract_invoke(
            helpers::ACC_0,
            Address::Account(helpers::ACC_0),
            Energy::from(100000),
            UpdateContractPayload {
                address: res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("contract.check_signature".into()),
                message: OwnedParameter::from_serial(&(helpers::ACC_0, data, &signatures))
                    .expect("Enough space."),
                amount: Amount::zero(),
            },
        )
        .expect("Querying contract should work");
    let rv = contracts_common::from_bytes::<u64>(&res_invoke_check_signature.return_value)
        .expect("Return value should be deserializable.");
    assert_eq!(
        rv, 0,
        "Signature check should succeed, the return value should be 0."
    );
}
