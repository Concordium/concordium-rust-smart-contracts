//! This module contains tests for transfers fr&om a contract to an account.
//! See more details about the specific test inside the `transfer.wat` file.
use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../concordium-base/smart-contracts/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);

#[test]
fn test_transfer() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(Account::new(ACC_0, initial_balance));

    let res_deploy = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_0,
            module_load_v1_raw(format!("{}/transfer.wasm", WASM_TEST_FOLDER))
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
                init_name: OwnedContractName::new_unchecked("init_transfer".into()),
                param:     OwnedParameter::empty(),
                amount:    Amount::zero(),
            },
        )
        .expect("Initializing valid contract should work");

    let contract_address = res_init.contract_address;

    chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("transfer.forward".into()),
                message:      OwnedParameter::from_serial(&ACC_0)
                    .expect("Parameter has valid size"),
                amount:       Amount::from_micro_ccd(123),
            },
        )
        .expect("Updating contract should succeed");
    // Contract should have forwarded the amount and thus have balance == 0.
    assert_eq!(
        Amount::zero(),
        chain.get_contract(contract_address).unwrap().self_balance
    );

    // Deposit 1000 micro CCD.
    chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("transfer.deposit".into()),
                message:      OwnedParameter::empty(),
                amount:       Amount::from_micro_ccd(1000),
            },
        )
        .expect("Updating contract should succeed");

    // Tell it to send 17 mCCD to ACC_0.
    let parameter = OwnedParameter::from_serial(&(ACC_0, Amount::from_micro_ccd(17)))
        .expect("Parameter has valid size");

    let res_update = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("transfer.send".into()),
                message:      parameter.clone(),
                amount:       Amount::zero(),
            },
        )
        .expect("Updating contract should succeed");
    // Contract should have 1000 - 17 microCCD in balance.
    assert_eq!(
        Amount::from_micro_ccd(1000 - 17),
        chain.get_contract(contract_address).unwrap().self_balance
    );
    assert_eq!(res_update.effective_trace_elements_cloned()[..], [
        ContractTraceElement::Interrupted {
            address: contract_address,
            events:  Vec::new(),
        },
        ContractTraceElement::Transferred {
            from:   contract_address,
            amount: Amount::from_micro_ccd(17),
            to:     ACC_0,
        },
        ContractTraceElement::Resumed {
            address: contract_address,
            success: true,
        },
        ContractTraceElement::Updated {
            data: InstanceUpdatedEvent {
                address:          contract_address,
                amount:           Amount::zero(),
                receive_name:     OwnedReceiveName::new_unchecked("transfer.send".into()),
                contract_version: concordium_base::smart_contracts::WasmVersion::V1,
                instigator:       Address::Account(ACC_0),
                message:          parameter,
                events:           Vec::new(),
            },
        }
    ])
}
