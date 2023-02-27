//! This module contains tests for transfers fr&om a contract to an account.
//! See more details about the specific test inside the `transfer.wat` file.
use concordium_smart_contract_testing::*;
use wasm_chain_integration::v0::Logs;

const WASM_TEST_FOLDER: &str = "../../concordium-node/concordium-consensus/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);

#[test]
fn test_transfer() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy = chain
        .module_deploy_wasm_v1(ACC_0, format!("{}/transfer.wasm", WASM_TEST_FOLDER))
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_transfer"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");

    let contract_address = res_init.contract_address;

    chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            contract_address,
            EntrypointName::new_unchecked("forward"),
            OwnedParameter::new(&ACC_0),
            Amount::from_micro_ccd(123),
            Energy::from(10000),
        )
        .expect("Updating contract should succeed");
    // Contract should have forwarded the amount and thus have balance == 0.
    assert_eq!(
        Amount::zero(),
        chain.contracts.get(&contract_address).unwrap().self_balance
    );

    // Deposit 1000 micro CCD.
    chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            contract_address,
            EntrypointName::new_unchecked("deposit"),
            OwnedParameter::empty(),
            Amount::from_micro_ccd(1000),
            Energy::from(10000),
        )
        .expect("Updating contract should succeed");

    let res_update = chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            contract_address,
            EntrypointName::new_unchecked("send"),
            OwnedParameter::new(&(ACC_0, Amount::from_micro_ccd(17))), /* Tell it to send 17
                                                                        * mCCD to ACC_0. */
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Updating contract should succeed");
    // Contract should have 1000 - 17 microCCD in balance.
    assert_eq!(
        Amount::from_micro_ccd(1000 - 17),
        chain.contracts.get(&contract_address).unwrap().self_balance
    );
    assert_eq!(res_update.chain_events[..], [
        ChainEvent::Interrupted {
            address: contract_address,
            logs:    Logs::new(),
        },
        ChainEvent::Transferred {
            from:   contract_address,
            amount: Amount::from_micro_ccd(17),
            to:     ACC_0,
        },
        ChainEvent::Resumed {
            address: contract_address,
            success: true,
        },
        ChainEvent::Updated {
            address:    contract_address,
            contract:   OwnedContractName::new_unchecked("init_transfer".into()),
            entrypoint: OwnedEntrypointName::new_unchecked("send".into()),
            amount:     Amount::zero(),
        }
    ])
}
