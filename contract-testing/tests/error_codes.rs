//! This module tests invoking a V1 contract which invokes an operation which
//! fails. The test is to make sure error codes are correctly returned to the
//! contract.

use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../concordium-base/smart-contracts/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);

#[test]
fn test_error_codes() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/caller.wasm", WASM_TEST_FOLDER))
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
                init_name: OwnedContractName::new_unchecked("init_caller".into()),
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    // Invoke an entrypoint that calls the "fail" entrypoint.
    // The expected return code is
    // 0x0100_ffff_ffef
    // because
    // - the return value is pushed (hence 01)
    // - the call to "fail" fails with a "logic error" (hence the 00)
    // - the return value is -17 (which when converted with two's complement i32 is
    //   ffff_ffef)
    let parameter_0 = (
        1u32, // instruction
        res_init.contract_address,
        OwnedParameter::empty(),
        EntrypointName::new_unchecked("fail"),
        Amount::zero(),
    );
    let res_update_0 = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("caller.call".into()),
                message:      OwnedParameter::from_serial(&parameter_0)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating valid contract should work");
    assert_eq!(
        res_update_0.return_value,
        u64::to_le_bytes(0x0100_ffff_ffef)
    );

    // Invoke an entrypoint that tries to transfer an amount that it does not have
    // via contract invoke. The expected return code is
    // 0x0001_0000_0000
    // because
    // - there is no return value (hence 00)
    // - the call fails with "insufficient funds" (hence 01)
    // - the remaining is set to 0 since there is no logic error
    let parameter_1 = (
        1u32, // instruction
        res_init.contract_address,
        OwnedParameter::empty(),
        EntrypointName::new_unchecked("fail"),
        Amount::from_micro_ccd(10_000),
    );
    let res_update_1 = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("caller.call".into()),
                message:      OwnedParameter::from_serial(&parameter_1)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating valid contract should work");
    assert_eq!(
        res_update_1.return_value,
        u64::to_le_bytes(0x0001_0000_0000)
    );

    // Invoke an entrypoint that traps
    // The expected return code is
    // 0x0002_0000_0000
    // because
    // - there is no return value (hence 00)
    // - the call fails with "missing account" (hence 02)
    // - the remaining is set to 0 since there is no logic error
    let parameter_2 = (
        0u32,                    // instruction
        AccountAddress([9; 32]), // Account which doesn't exist
        Amount::zero(),
    );
    let res_update_2 = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("caller.call".into()),
                message:      OwnedParameter::from_serial(&parameter_2)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating valid contract should work");
    assert_eq!(
        res_update_2.return_value,
        u64::to_le_bytes(0x0002_0000_0000)
    );

    // Invoke an entrypoint that tries to invoke a non-existing contract.
    // The expected return code is
    // 0x0003_0000_0000
    // because
    // - there is no return value (hence 00)
    // - the call fails with "missing contract" (hence 03)
    // - the remaining is set to 0 since there is no logic error
    let parameter_3 = (
        1u32,                             // instruction
        ContractAddress::new(1234, 5678), // Address which does not exist.
        OwnedParameter::empty(),
        EntrypointName::new_unchecked("fail"),
        Amount::zero(),
    );
    let res_update_3 = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("caller.call".into()),
                message:      OwnedParameter::from_serial(&parameter_3)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating valid contract should work");
    assert_eq!(
        res_update_3.return_value,
        u64::to_le_bytes(0x0003_0000_0000)
    );

    // Invoke an entrypoint that tries to invoke a non-existing entrypoint.
    // The expected return code is
    // 0x0004_0000_0000
    // because
    // - there is no return value (hence 00)
    // - the call fails with "invalid entrypoint" (hence 04)
    // - the remaining is set to 0 since there is no logic error
    let parameter_4 = (
        1u32, // instruction
        res_init.contract_address,
        OwnedParameter::empty(),
        EntrypointName::new_unchecked("nonexisting"),
        Amount::zero(),
    );
    let res_update_4 = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("caller.call".into()),
                message:      OwnedParameter::from_serial(&parameter_4)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating valid contract should work");
    assert_eq!(
        res_update_4.return_value,
        u64::to_le_bytes(0x0004_0000_0000)
    );

    // Test 5 is omitted as it uses a v0 contract which is not supported in this
    // library.

    // |Invoke an entrypoint that traps
    // The expected return code is
    // 0x0006_0000_0000
    // because
    // - there is no return value (hence 00)
    // - the call fails with "trap" (hence 06)
    // - the remaining is set to 0 since there is no logic error
    let parameter_6 = (
        1u32, // instruction
        res_init.contract_address,
        OwnedParameter::empty(),
        EntrypointName::new_unchecked("trap"),
        Amount::zero(),
    );
    let res_update_6 = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                address:      res_init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("caller.call".into()),
                message:      OwnedParameter::from_serial(&parameter_6)
                    .expect("Parameter has valid size"),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating valid contract should work");
    assert_eq!(
        res_update_6.return_value,
        u64::to_le_bytes(0x0006_0000_0000)
    );
}
