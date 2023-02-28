//! This module tests the relaxed smart contract restrictions introduced in P5
//! for V1 contracts.
//!
//! This will only check that the P5 limits are in effect, as the testing
//! library only supports the most current protocol version (for now, at least).
//!
//! The limit changes in P5 are:
//!   - Parameter size limit: 1kb -> 65kb
//!   - Return value size limit: 16kb -> no limit (apart from energy)
//!   - Number of logs: 64 -> no limit (apart from energy)
//!   - Cost of parameters:
//!     - Of size <= 1kb: base cost + 1NRG / 1 *kilobyte* (same as before P5)
//!     - Of size > 1 kb: base cost + 1NRG / 1 *byte*
use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../../concordium-node/concordium-consensus/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);

/// Test the new parameter size limit.
#[test]
fn test_new_parameter_limit() {
    let (mut chain, contract_address) = deploy_and_init();

    chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            contract_address,
            EntrypointName::new_unchecked("param"),
            mk_parameter(65535, 65535),
            Amount::zero(),
            Energy::from(700000),
        )
        .expect("Updating contract should succeed");
}

/// Test the new return value limit.
#[test]
fn test_new_return_value_limit() {
    let (mut chain, contract_address) = deploy_and_init();

    chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            contract_address,
            EntrypointName::new_unchecked("return-value"),
            OwnedParameter::new(&100_000u32),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Updating contract should succeed");
}

/// Test the new number of logs limit.
#[test]
fn test_new_log_limit() {
    let (mut chain, contract_address) = deploy_and_init();

    chain
        .contract_update(
            ACC_0,
            Address::Account(ACC_0),
            contract_address,
            EntrypointName::new_unchecked("logs"),
            OwnedParameter::new(&64u32),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Updating contract should succeed");
}

/// Helper for deploying and initializing the `relaxed-restrictions.wasm`
/// contract.
fn deploy_and_init() -> (Chain, ContractAddress) {
    let mut chain = Chain::new();
    let initial_balance = Amount::from_ccd(10000);
    chain.create_account(ACC_0, Account::new(initial_balance));

    let res_deploy = chain
        .module_deploy_wasm_v1(
            ACC_0,
            format!("{}/relaxed-restrictions.wasm", WASM_TEST_FOLDER),
        )
        .expect("Deploying valid module should work");

    let res_init = chain
        .contract_init(
            ACC_0,
            res_deploy.module_reference,
            ContractName::new_unchecked("init_relax"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        )
        .expect("Initializing valid contract should work");
    (chain, res_init.contract_address)
}

/// Helper for creating a parameter of a specific size.
///
/// The `internal_param_size` is the size of the parameter passed to the
/// `param-aux` entrypoint. This is used to check the parameter size limit
/// inside the wasm interpreter.
///
/// The `desired_size` is the desired total length of the parameter produced by
/// this function. It is used to check the parameter size limit checked in the
/// testing library.
///
/// The parameter returned will contain
///  - `internal_param_size` (2 bytes)
///  - the entrypoint `"param-aux"` (2 + 9 bytes)
///  - filler `1u8` bytes (remaining until `desired_size` is reached)
fn mk_parameter(internal_param_size: u16, desired_size: u32) -> OwnedParameter {
    let entrypoint = OwnedEntrypointName::new_unchecked("param-aux".into());
    let filler_size = desired_size
        - 2 // length of the parameter itself
        - 2 // internal_param_size
        - 2 // entrypoint name len
        - 9 // entrypoint name
        - 4; // length of filler vector
    let filler = vec![1u8; filler_size as usize];
    OwnedParameter::new(&(internal_param_size, entrypoint, filler))
}
