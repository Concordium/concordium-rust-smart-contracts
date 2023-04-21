//! This module contains integration tests for the piggy bank.
//! To run them, use `cargo test`.
use concordium_smart_contract_testing::*;
use piggy_bank_part2::*;

const ACC_ADDR_OWNER: AccountAddress = AccountAddress([0u8; 32]);
const ACC_ADDR_OTHER: AccountAddress = AccountAddress([1u8; 32]);
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(1000);

/// A helper method for setting up:
///  - The chain,
///  - The two accounts `ACC_ADDR_OWNER` and `ACC_ADDR_OTHER`, both with
///    `ACC_INITIAL_BALANCE` CCD,
///  - The deployed and initialized piggy bank contract.
fn setup_chain_and_contract() -> (Chain, ContractInitSuccess) {
    let mut chain = Chain::new();

    chain.create_account(Account::new(ACC_ADDR_OWNER, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(ACC_ADDR_OTHER, ACC_INITIAL_BALANCE));

    let module = module_load_v1("piggy_bank_part2.wasm.v1").expect("Module exists and is valid");
    let deployment = chain
        .module_deploy_v1(Signer::with_one_key(), ACC_ADDR_OWNER, module)
        .expect("Deploying valid module should succeed");

    let initialization = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_ADDR_OWNER,
            Energy::from(10000),
            InitContractPayload {
                amount:    Amount::zero(),
                mod_ref:   deployment.module_reference,
                init_name: OwnedContractName::new_unchecked("init_PiggyBank".to_string()),
                param:     OwnedParameter::empty(),
            },
        )
        .expect("Initialization should always succeed");

    (chain, initialization)
}

#[test]
fn test_init() {
    let (chain, initialization) = setup_chain_and_contract();
    assert_eq!(
        chain.contract_balance(initialization.contract_address),
        Some(Amount::zero()),
        "Piggy bank is not initialized with balance of zero"
    );
}

#[test]
fn test_insert_intact() {
    let (mut chain, initialization) = setup_chain_and_contract();
    let insert_amount = Amount::from_ccd(10);

    // Insert 10 CCD.
    let update = chain.contract_update(
        Signer::with_one_key(),
        ACC_ADDR_OWNER,
        Address::Account(ACC_ADDR_OWNER),
        Energy::from(10000),
        UpdateContractPayload {
            amount:       insert_amount,
            address:      initialization.contract_address,
            receive_name: OwnedReceiveName::new_unchecked("PiggyBank.insert".to_string()),
            message:      OwnedParameter::empty(),
        },
    );

    assert!(update.is_ok());
    assert_eq!(chain.contract_balance(initialization.contract_address), Some(insert_amount));
}

#[test]
fn test_smash_intact() {
    let (mut chain, initialization) = setup_chain_and_contract();

    let update = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("PiggyBank.smash".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect("Owner is allowed to smash intact piggy bank");

    // Invoke the view function to check the state and balance.
    let invoke = chain
        .contract_invoke(
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("PiggyBank.view".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect("Invoking `view` should always succeed");

    // Ensure the values returned by the view function are correct.
    let (state, balance): (PiggyBankState, Amount) =
        from_bytes(&invoke.return_value).expect("View should always return a valid result");
    assert_eq!(state, PiggyBankState::Smashed);
    assert_eq!(balance, Amount::zero());
    assert_eq!(update.account_transfers().collect::<Vec<_>>(), [(
        initialization.contract_address,
        Amount::zero(),
        ACC_ADDR_OWNER
    )]);
}

#[test]
fn test_smash_intact_not_owner() {
    let (mut chain, initialization) = setup_chain_and_contract();

    let update_err = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_ADDR_OTHER,
            Address::Account(ACC_ADDR_OTHER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("PiggyBank.smash".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect_err("Smashing should only succeed for the owner");

    let return_value =
        update_err.return_value().expect("Contract should reject and thus return bytes");
    let error: SmashError = from_bytes(&return_value)
        .expect("Contract should return a `SmashError` in serialized form");

    assert_eq!(error, SmashError::NotOwner, "Contract did not fail due to a NotOwner error");
    assert_eq!(
        chain.account_balance_available(ACC_ADDR_OTHER),
        Some(ACC_INITIAL_BALANCE - update_err.transaction_fee),
        "The invoker account was incorrectly charged"
    )
}

#[test]
fn test_smash_smashed() {
    let (mut chain, initialization) = setup_chain_and_contract();

    // Smash once
    chain
        .contract_update(
            Signer::with_one_key(),
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("PiggyBank.smash".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect("The owner should be allowed to smash");

    let update_second_smash_err = chain
        .contract_update(
            Signer::with_one_key(),
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("PiggyBank.smash".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect_err("The piggybank cannot be smashed more than once");

    let return_value =
        update_second_smash_err.return_value().expect("Contract should reject and return bytes");
    let error: SmashError = from_bytes(&return_value)
        .expect("Contract should return a `SmashError` in serialized form");

    assert_eq!(error, SmashError::AlreadySmashed);
}
