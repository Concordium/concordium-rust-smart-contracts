//! Test that the debug macro generates compilable code.
#[test]
fn dbg() {
    let t = trybuild::TestCases::new();
    t.pass("tests/dbg/success.rs");
}
