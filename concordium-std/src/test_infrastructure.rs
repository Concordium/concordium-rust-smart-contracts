#[cfg(feature = "concordium-quickcheck")]
use quickcheck::*;

/// Reports back an error to the host when compiled to wasm
/// Used internally, not meant to be called directly by contract writers
#[doc(hidden)]
#[cfg(all(feature = "wasm-test", target_arch = "wasm32"))]
pub fn report_error(message: &str, filename: &str, line: u32, column: u32) {
    let msg_bytes = message.as_bytes();
    let filename_bytes = filename.as_bytes();
    unsafe {
        crate::prims::report_error(
            msg_bytes.as_ptr(),
            msg_bytes.len() as u32,
            filename_bytes.as_ptr(),
            filename_bytes.len() as u32,
            line,
            column,
        )
    };
}

/// Reports back an error to the host when compiled to wasm
/// Used internally, not meant to be called directly by contract writers
#[doc(hidden)]
#[cfg(not(all(feature = "wasm-test", target_arch = "wasm32")))]
pub fn report_error(_message: &str, _filename: &str, _line: u32, _column: u32) {}

#[cfg(all(feature = "wasm-test", feature = "concordium-quickcheck", target_arch = "wasm32"))]
use getrandom::register_custom_getrandom;
#[cfg(all(
    feature = "wasm-test",
    feature = "concordium-quickcheck",
    target_arch = "wasm32"
))]
/// A custom function for generating random numbers.
/// There is no Wasm primitive to sample random numbers and this function
/// redirects calls to the `get_random` primitive (host function), which is
/// later handled by `TestHost`, where the actual random number generation
/// happens.
fn get_random(dest: &mut [u8]) -> Result<(), getrandom::Error> {
    unsafe {
        crate::prims::get_random(dest.as_mut_ptr(), dest.len() as u32);
    }
    Ok(())
}

#[cfg(all(
    feature = "wasm-test",
    feature = "concordium-quickcheck",
    target_arch = "wasm32"
))]
// When compiling to Wasm, we register our own custom random number generation
// function, so all the calls, that depend on `getrandom` (like
// `from_entropy`) will call our function instead.
register_custom_getrandom!(get_random);

// Overall number of QuickCheck tests to run.
// Includes both *passed and discarded*.
// Note: when changing this constant, make sure that
// concordium_std_derive::QUICKCHECK_MAX_PASSED_TESTS is adjusted:
// - QUICKCHECK_MAX_PASSED_TESTS is capped by
//   QUICKCHECK_MAX_WITH_DISCARDED_TESTS;
// - QUICKCHECK_MAX_WITH_DISCARDED_TESTS should be bigger allowing some test to
//   be discarded (QuickCheck default is x100).
#[cfg(feature = "concordium-quickcheck")]
const QUICKCHECK_MAX_WITH_DISCARDED_TESTS: u64 = 100_000_000;

#[cfg(all(feature = "concordium-quickcheck", target_arch = "wasm32"))]
/// A customized QuickCheck test runner used for on-chain wasm code.
/// Adds support for reporting errors using the primitives available when
/// running Wasm code.
///
/// The `num_tests` parameter specifies how many random tests to run.
pub fn concordium_qc<A: Testable>(num_tests: u64, f: A) {
    let mut qc = QuickCheck::new()
        .tests(num_tests)
        .max_tests(QUICKCHECK_MAX_WITH_DISCARDED_TESTS);
    let res = qc.quicktest(f);
    match res {
        Ok(n_tests_passed) => {
            if n_tests_passed == 0 {
                // report a error is no tests were generated
                let msg = "(No QuickCheck tests were generated)";
                // calls `report_error` which is handled by `TestHost`
                report_error(msg, file!(), line!(), column!())
            }
        }
        Err(result) => {
            let msg = format!("Failed with the counterexample: {:#?}", result);
            // calls `report_error` which is handled by `TestHost`
            report_error(&msg, file!(), line!(), column!());
        }
    }
}

#[cfg(all(feature = "concordium-quickcheck", not(target_arch = "wasm32")))]
/// A wrapper for QuickCheck test runner for non-wasm targets.
// The `num_tests` parameter specifies how many random tests to run.
pub fn concordium_qc<A: Testable>(num_tests: u64, f: A) {
    QuickCheck::new()
        .tests(num_tests)
        .max_tests(QUICKCHECK_MAX_WITH_DISCARDED_TESTS)
        .quickcheck(f)
}
