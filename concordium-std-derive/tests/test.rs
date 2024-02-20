//! Test that the macros generates compilable code.
#[test]
fn tests() {
    let t = trybuild::TestCases::new();
    t.pass("tests/test-programs/success.rs");
    t.compile_fail("tests/test-programs/fail-*.rs");
}
