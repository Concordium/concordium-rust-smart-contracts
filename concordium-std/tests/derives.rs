//! Test correct functioning of trait deriving macros from
//! `concordium-std-derive` package. Test cases presented here check successful
//! (or failed) compilation for the code which uses macros, not its functioning.
#[test]
fn deserial_with_state() {
    let t = trybuild::TestCases::new();
    t.pass("tests/derive-deserial-with-state/success-*.rs");
}

#[test]
fn deletable() {
    let t = trybuild::TestCases::new();
    t.pass("tests/derive-deletable/success-*.rs");
}
