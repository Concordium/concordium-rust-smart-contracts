//! Tests that execute the entrypoints in the `bump-alloc-tests` contract, which
//! doesn't have any functionality besides entrypoint that exercise and test the
//! bump allocator from `concordium_std`.
use concordium_smart_contract_testing::*;
use concordium_std::collections::BTreeMap;

const ACC_0: AccountAddress = AccountAddress([0u8; 32]);
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(1000);
const SIGNER: Signer = Signer::with_one_key();

/// Tests that the allocator correctly handles a data structure such as a map
/// and that lookups return the correct values. Takes as input a map<u64, u64>,
/// two keys, and the expected sum of corresponding values in the map.
#[test]
fn test_memory_layout() {
    let (chain, contract_address) = initialize_chain_and_contract();

    let map: BTreeMap<u64, u64> =
        BTreeMap::from([(1, 2), (2, 3), (4, 5), (99, 100), (9999, 10000)]);
    let key_1: u64 = 4;
    let key_2: u64 = 9999;
    let expected_sum: u64 = 5 + 10000;

    chain
        .contract_invoke(
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                address: contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "bump_alloc_tests.memory_layout".to_string(),
                ),
                message: OwnedParameter::from_serial(&(map, key_1, key_2, expected_sum))
                    .expect("Parameter size is below limit."),
            },
        )
        .print_emitted_events()
        .expect("Update should succeed");
}

/// Test that allocating a large memory chunk the size of the maximum parameter
/// length works.
#[test]
fn test_max_parameter_len() {
    let (chain, contract_address) = initialize_chain_and_contract();

    chain
        .contract_invoke(
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(100_000),
            UpdateContractPayload {
                amount: Amount::zero(),
                address: contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "bump_alloc_tests.max_parameter_len".to_string(),
                ),
                message: OwnedParameter::from_serial(&[42u8; 65535])
                    .expect("Parameter size is below limit."),
            },
        )
        .print_emitted_events()
        .expect("Update should succeed");
}

/// Test that allocating 1MiB works.
#[test]
fn test_allocate_one_mib() {
    let (chain, contract_address) = initialize_chain_and_contract();

    chain
        .contract_invoke(
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(100_000),
            UpdateContractPayload {
                amount: Amount::zero(),
                address: contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "bump_alloc_tests.allocate_one_mib".to_string(),
                ),
                message: OwnedParameter::empty(),
            },
        )
        .print_emitted_events()
        .expect("Update should succeed");
}

/// Test the optimization where the last memory chunk can be reused in certain
/// cases. See the entrypoint for more details.
#[test]
fn test_dealloc_last_optimization() {
    let (chain, contract_address) = initialize_chain_and_contract();

    chain
        .contract_invoke(
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                address: contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "bump_alloc_tests.dealloc_last_optimization".to_string(),
                ),
                message: OwnedParameter::from_serial(&2u64)
                    .expect("Parameter size is below limit."),
            },
        )
        .print_emitted_events()
        .expect("Update should succeed");
}

/// Tests that stack and static data isn't overwritten in the allocator.
#[test]
fn test_stack_and_static() {
    let (chain, contract_address) = initialize_chain_and_contract();

    chain
        .contract_invoke(
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(100_000_000),
            UpdateContractPayload {
                amount: Amount::zero(),
                address: contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "bump_alloc_tests.stack_and_static".to_string(),
                ),
                message: OwnedParameter::from_serial(&("ORIGINAL", 123456, "EVEN"))
                    .expect("Parameter size is below limit."),
            },
        )
        .print_emitted_events()
        .expect("Update should succeed");
}

/// A helper method for initializing the chain and contract.
fn initialize_chain_and_contract() -> (Chain, ContractAddress) {
    // Create the test chain.
    let mut chain = Chain::new();

    // Create one account on the chain.
    chain.create_account(Account::new(ACC_0, ACC_INITIAL_BALANCE));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain
        .module_deploy_v1_debug(SIGNER, ACC_0, module, is_debug_enabled())
        .expect("Deploy valid module");

    let init = chain
        .contract_init(
            SIGNER,
            ACC_0,
            Energy::from(10000),
            InitContractPayload {
                amount: Amount::zero(),
                mod_ref: deployment.module_reference,
                init_name: OwnedContractName::new_unchecked("init_bump_alloc_tests".to_string()),
                param: OwnedParameter::empty(),
            },
        )
        .expect("Init contract should succeed");
    (chain, init.contract_address)
}
