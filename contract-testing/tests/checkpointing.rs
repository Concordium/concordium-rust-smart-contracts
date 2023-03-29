//! This module contains tests for the checkpointing/rollback functionality of
//! the library.
//!
//! When a contract entrypoint execution fails, any changes it has
//! made must be rolled back. That is also the case if a nested contract call
//! fails.
use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../concordium-base/smart-contracts/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);
const ACC_1: AccountAddress = AccountAddress([1; 32]);

/// This test has the following call pattern:
/// A
///  -->  B
///         --> A
///         <--
///       B(trap)
/// A <--
/// The state at A should be left unchanged by the changes of the
/// 'inner' invocation on contract A. A correctly perceives B's
/// trapping signal. Only V1 contracts are being used.
#[test]
fn test_case_1() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            Chain::module_load_v1_raw(format!("{}/checkpointing.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init_a = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                mod_ref:   res_deploy.module_reference,
                init_name: OwnedContractName::new_unchecked("init_a".into()),
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let res_init_b = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                mod_ref:   res_deploy.module_reference,
                init_name: OwnedContractName::new_unchecked("init_b".into()),
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let forward_parameter = (
        res_init_a.contract_address,
        0u16, // length of empty parameter
        EntrypointName::new_unchecked("a_modify"),
        Amount::zero(),
    );
    let forward_parameter_len = to_bytes(&forward_parameter).len();
    let parameter = (
        res_init_b.contract_address,
        forward_parameter_len as u16,
        forward_parameter,
        EntrypointName::new_unchecked("b_forward_crash"),
        Amount::zero(),
    );

    chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                address:      res_init_a.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("a.a_modify_proxy".into()),
                message:      OwnedParameter::from_serial(&parameter)
                    .expect("Parameter has valid size"),
                // We supply one microCCD as we expect a trap
                // (see contract for details).
                amount:       Amount::from_micro_ccd(1),
            },
        )
        .expect("Updating contract should succeed");
}

/// This test has the following call pattern:
/// A
///   -->  B
///          --> A (no modification, just lookup entry)
///          <--
///        B
/// A <--
///
/// The state at A should be left unchanged.
/// The iterator initialized at the outer A should point to the same
/// entry as before the call. That is, the iterator should not
/// be affected by the inner iterator. Only V1 contracts are
/// being used.
#[test]
fn test_case_2() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            Chain::module_load_v1_raw(format!("{}/checkpointing.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init_a = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                mod_ref:   res_deploy.module_reference,
                init_name: OwnedContractName::new_unchecked("init_a".into()),
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let res_init_b = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                mod_ref:   res_deploy.module_reference,
                init_name: OwnedContractName::new_unchecked("init_b".into()),
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let forward_parameter = (
        res_init_a.contract_address,
        0u16, // length of empty parameter
        EntrypointName::new_unchecked("a_no_modify"),
        Amount::zero(),
    );
    let forward_parameter_len = to_bytes(&forward_parameter).len();
    let parameter = (
        res_init_b.contract_address,
        forward_parameter_len as u16,
        forward_parameter,
        EntrypointName::new_unchecked("b_forward"),
        Amount::zero(),
    );

    chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                address:      res_init_a.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("a.a_modify_proxy".into()),
                message:      OwnedParameter::from_serial(&parameter)
                    .expect("Parameter has valid size"),
                // We supply zero microCCD as we're instructing the contract to not expect
                // state modifications. Also, the contract does not expect
                // errors, i.e., a trap signal from underlying invocations.
                // The 'inner' call to contract A does not modify the state.
                // See the contract for details.
                amount:       Amount::zero(),
            },
        )
        .expect("Updating contract should succeed");
}

/// This test has the following call pattern:
/// A
///   -->  Transfer
/// A <--
///
/// The state at A should be left unchanged.
/// The iterator initialized at A should after the call point to the
/// same entry as before the call. Only V1 contracts are being
/// used.
#[test]
fn test_case_3() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(Account::new(ACC_0, initial_balance));
    chain.create_account(Account::new(ACC_1, initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            Chain::module_load_v1_raw(format!("{}/checkpointing.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init_a = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                mod_ref:   res_deploy.module_reference,
                init_name: OwnedContractName::new_unchecked("init_a".into()),
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                mod_ref:   res_deploy.module_reference,
                init_name: OwnedContractName::new_unchecked("init_b".into()),
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
                address:      res_init_a.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("a.a_modify_proxy".into()),
                message:      OwnedParameter::from_serial(&ACC_1)
                    .expect("Parameter has valid size"),
                // We supply three micro CCDs as we're instructing the contract to carry out a
                // transfer instead of a call. See the contract for
                // details.
                amount:       Amount::from_micro_ccd(3),
            },
        )
        .expect("Updating contract should succeed");
}

/// This test has the following call pattern:
/// A
///   -->  B
///          --> A modify
///          <--
///        B
/// A <--
///
/// The state at A should have changed according to the 'inner'
/// invocation on contract A. Only V1 contracts are being used.
#[test]
fn test_case_4() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            Chain::module_load_v1_raw(format!("{}/checkpointing.wasm", WASM_TEST_FOLDER))
                .expect("module should exist"),
        )
        .expect("Deploying valid module should work");

    let res_init_a = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                mod_ref:   res_deploy.module_reference,
                init_name: OwnedContractName::new_unchecked("init_a".into()),
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let res_init_b = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                mod_ref:   res_deploy.module_reference,
                init_name: OwnedContractName::new_unchecked("init_b".into()),
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let forward_parameter = (
        res_init_a.contract_address,
        0u16, // length of empty parameter
        EntrypointName::new_unchecked("a_modify"),
        Amount::zero(),
    );
    let forward_parameter_len = to_bytes(&forward_parameter).len();
    let parameter = (
        res_init_b.contract_address,
        forward_parameter_len as u16,
        forward_parameter,
        EntrypointName::new_unchecked("b_forward"),
        Amount::zero(),
    );

    chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                address:      res_init_a.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("a.a_modify_proxy".into()),
                message:      OwnedParameter::from_serial(&parameter)
                    .expect("Parameter has valid size"),
                // We supply four CCDs as we're instructing the contract to expect state
                // modifications being made from the 'inner' contract A
                // call to be in effect when returned to the caller (a.a_modify_proxy).
                // See the contract for details.
                amount:       Amount::from_micro_ccd(4),
            },
        )
        .expect("Updating contract should succeed");
}
