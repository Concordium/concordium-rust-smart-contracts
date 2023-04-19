//! This module tests that the correct self-balance is exposed to V1 contracts.
//! In essense that the self-balance is updated by the invoke.
//!
//! See more details about the specific test inside the `self-balance.wat` and
//! `self-blaance-nested.wat` files.
use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../concordium-base/smart-contracts/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);

/// Invoke an entrypoint and transfer to ourselves.
/// The before and after self-balances are the same.
#[test]
fn test_invoke_1() {
    let (mut chain, contract_address, _) = deploy_and_init("self-balance.wasm", "init_transfer");

    let parameter = (
        1u32, // instruction
        contract_address,
        OwnedParameter::empty(),
        EntrypointName::new_unchecked("accept"),
        Amount::from_micro_ccd(0),
    );
    let result = chain.contract_update(
        Signer::with_one_key(),
        ACC_0,
        Address::Account(ACC_0),
        Energy::from(10000),
        UpdateContractPayload {
            address:      contract_address,
            amount:       Amount::from_micro_ccd(123),
            receive_name: OwnedReceiveName::new_unchecked("transfer.forward".into()),
            message:      OwnedParameter::from_serial(&parameter)
                .expect("Parameter has valid size."),
        },
    );
    assert_success(
        result,
        Amount::from_micro_ccd(123),
        Amount::from_micro_ccd(123),
        "Self selfBalance",
    );
}

/// Invoke an entrypoint and transfer to another instance.
/// The before and after balances are different.
/// The key difference from `test_invoke_1` is that the contract address in the
/// parameter is different.
#[test]
fn test_invoke_2() {
    let (mut chain, self_address, mod_ref) = deploy_and_init("self-balance.wasm", "init_transfer");

    let res_init_another = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                mod_ref,
                init_name: OwnedContractName::new_unchecked("init_transfer".into()),
                param: OwnedParameter::empty(),
                amount: Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let parameter = (
        1u32,                              // instruction
        res_init_another.contract_address, // Transfer to another contract instance.
        OwnedParameter::empty(),
        EntrypointName::new_unchecked("accept"),
        Amount::from_micro_ccd(100),
    );
    let result = chain.contract_update(
        Signer::with_one_key(),
        ACC_0,
        Address::Account(ACC_0),
        Energy::from(10000),
        UpdateContractPayload {
            address:      self_address,
            receive_name: OwnedReceiveName::new_unchecked("transfer.forward".into()),
            message:      OwnedParameter::from_serial(&parameter)
                .expect("Parameter has valid size."),
            amount:       Amount::from_micro_ccd(123),
        },
    );
    assert_success(
        result,
        Amount::from_micro_ccd(123),
        Amount::from_micro_ccd(23),
        "Self selfBalance",
    );
}

/// Helper for deploying and initializing the provided contract.
fn deploy_and_init(
    file_name: &str,
    contract_name: &str,
) -> (Chain, ContractAddress, ModuleReference) {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/{}", WASM_TEST_FOLDER, file_name))
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
                init_name: OwnedContractName::new_unchecked(contract_name.into()),
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");
    (
        chain,
        res_init.contract_address,
        res_deploy.module_reference,
    )
}

/// Helper for asserting the success.
fn assert_success(
    result: Result<ContractInvokeSuccess, ContractInvokeError>,
    expected_before: Amount,
    expected_after: Amount,
    error_message: &str,
) {
    if let Ok(success) = result {
        assert_eq!(
            success.return_value,
            to_bytes(&(expected_before, expected_after))
        )
    } else {
        panic!("Test failed ( {} )", error_message)
    }
}
