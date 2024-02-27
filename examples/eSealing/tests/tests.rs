//! Tests for the eSealing contract.
use concordium_smart_contract_testing::*;
use concordium_std::HashSha2256;
use e_sealing::*;

/// Constants:
const ALICE: AccountAddress = account_address!("0000000000000000000000");
const ALICE_ADDR: Address = Address::Account(ALICE);
const SIGNER: Signer = Signer::with_one_key();

/// Test that registering a file works and produces the expected event.
#[test]
fn test_register_file() {
    let (mut chain, contract_address) = init();

    // The file hash to register.
    let parameter = HashSha2256([0; 32]);

    // Increase the block time of the chain to check it later.
    chain.tick_block_time(Duration::from_millis(123)).expect("Won't overflow.");

    // Register a file.
    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("eSealing.registerFile".to_string()),
            message:      OwnedParameter::from_serial(&parameter).expect("Valid parameter size"),
        })
        .expect("Register file");

    // Check that the expected event was emitted.
    assert_eq!(deserialize_update_events(&update), [Event::Registration(RegistrationEvent {
        file_hash: parameter,
        witness:   ALICE,
        timestamp: Timestamp::from_timestamp_millis(123),
    })]);
}

/// Test that you cannot register the same file twice.
#[test]
fn test_can_not_register_file_twice() {
    let (mut chain, contract_address) = init();

    // The file hash to register.
    let parameter = HashSha2256([0; 32]);

    // Register a file.
    chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("eSealing.registerFile".to_string()),
            message:      OwnedParameter::from_serial(&parameter).expect("Valid parameter size"),
        })
        .expect("Register file");

    // Register the same file again. Which should fail.
    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("eSealing.registerFile".to_string()),
            message:      OwnedParameter::from_serial(&parameter).expect("Valid parameter size"),
        })
        .expect_err("Register file");

    // Check the error message returned.
    let rv: ContractError = update.parse_return_value().expect("Deserialize ContractError.");
    assert_eq!(rv, ContractError::AlreadyRegistered);
}

/// Test that getting a file record works.
#[test]
fn test_get_file() {
    let (mut chain, contract_address) = init();

    // The file hash to register.
    let parameter = HashSha2256([0; 32]);

    // Advance the block time to check it later.
    chain.tick_block_time(Duration::from_millis(123)).expect("Won't overflow.");

    // Register a file.
    chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("eSealing.registerFile".to_string()),
            message:      OwnedParameter::from_serial(&parameter).expect("Valid parameter size"),
        })
        .expect("Register file");

    // Get the file record.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("eSealing.getFile".to_string()),
            message:      OwnedParameter::from_serial(&parameter).expect("Valid parameter size"),
        })
        .expect("Get file");

    // Check that get_file returns the filestate.
    let file_state: Option<FileState> =
        invoke.parse_return_value().expect("Deserialize FileState.");
    assert_eq!(
        file_state,
        Some(FileState {
            timestamp: Timestamp::from_timestamp_millis(123),
            witness:   ALICE,
        })
    );
}

// Helpers:

/// Deserialize the events from an update.
fn deserialize_update_events(update: &ContractInvokeSuccess) -> Vec<Event> {
    update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect()
}

/// Setup chain and contract.
fn init() -> (Chain, ContractAddress) {
    let mut chain = Chain::new();

    // Create some accounts on the chain.
    chain.create_account(Account::new(ALICE, Amount::from_ccd(1000)));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, ALICE, module).expect("Deploy valid module");

    // Initialize the auction contract.
    let init = chain
        .contract_init(SIGNER, ALICE, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_eSealing".to_string()),
            param:     OwnedParameter::empty(),
        })
        .expect("Initialize contract");

    (chain, init.contract_address)
}
