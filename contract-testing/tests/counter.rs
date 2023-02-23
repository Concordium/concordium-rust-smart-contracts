//! This module tests calling a contract from a contract and inspecting the
//! return message. Concretely it invokes a counter contract that maintains a
//! 64-bit counter in its state.

use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../../concordium-node/concordium-consensus/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);

#[test]
fn test_counter() {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(1000000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy = chain
        .module_deploy_wasm_v1(ACC_0, format!("{}/call-counter.wasm", WASM_TEST_FOLDER))
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_counter"),
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
            EntrypointName::new_unchecked("inc"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Updating valid contract should work");
    assert_counter_state(&mut chain, res_init.contract_address, 1);

    chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("inc"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Updating valid contract should work");
    assert_counter_state(&mut chain, res_init.contract_address, 2);

    let parameter = (
        res_init.contract_address,
        OwnedParameter::empty(),
        (EntrypointName::new_unchecked("inc"), Amount::zero()),
    );
    chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            res_init.contract_address,
            EntrypointName::new_unchecked("inc10"),
            OwnedParameter::new(&parameter),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Updating valid contract should work");
    assert_counter_state(&mut chain, res_init.contract_address, 12);
}

/// Looks up in the root of the state trie and compares the value with the
/// `expected`.
fn assert_counter_state(chain: &mut Chain, contract_address: ContractAddress, expected: u64) {
    assert_eq!(
        chain
            .contract_state_lookup(contract_address, &[0, 0, 0, 0, 0, 0, 0, 0])
            .unwrap(),
        u64::to_le_bytes(expected)
    );
}
