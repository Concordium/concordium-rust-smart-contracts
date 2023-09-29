//! Some helpers and constants that are used in most or all of the tests in this
//! folder.
use concordium_smart_contract_testing::*;

/// Relative path to the wasm test contracts.
pub(crate) const WASM_TEST_FOLDER: &str =
    "../concordium-rust-sdk/concordium-base/smart-contracts/testdata/contracts/v1";

/// Test account 0.
pub(crate) const ACC_0: AccountAddress = AccountAddress([0; 32]);

/// Test account 1.
/// Dead code is allowed to avoid a warning when running `cargo test`.
/// `cargo test` compiles each test module independently and for the ones that
/// do not use `ACC_1` a warning is produced.
#[allow(dead_code)]
pub(crate) const ACC_1: AccountAddress = AccountAddress([1; 32]);

/// Get the path to a wasm test file in wasm test folder.
///
/// This is simply prepends the test folder path to the file name:
/// `WASM_TEST_FOLDER/{file_name}`.
pub(crate) fn wasm_test_file(file_name: &str) -> String {
    format!("{WASM_TEST_FOLDER}/{file_name}")
}
