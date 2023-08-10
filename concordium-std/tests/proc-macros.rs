//! Test correct functioning of trait deriving macros from
//! `concordium-std-derive` package. Test cases presented here check successful
//! (or failed) compilation for the code which uses macros, not its functioning.
#[test]
fn derive_deserial_with_state() {
    let t = trybuild::TestCases::new();
    t.pass("tests/derive-deserial-with-state/success-*.rs");
    t.compile_fail("tests/derive-deserial-with-state/fail-*.rs");
}

#[test]
fn derive_deletable() {
    let t = trybuild::TestCases::new();
    t.pass("tests/derive-deletable/success-*.rs");
}

#[test]
fn derive_serial() {
    let t = trybuild::TestCases::new();
    t.pass("tests/derive-serial/success-*.rs");
    t.compile_fail("tests/derive-serial/fail-*.rs");
}

#[test]
fn derive_deserial() {
    let t = trybuild::TestCases::new();
    t.pass("tests/derive-deserial/success-*.rs");
    t.compile_fail("tests/derive-deserial/fail-*.rs");
}

#[test]
fn derive_schema_type() {
    let t = trybuild::TestCases::new();
    t.pass("tests/derive-schema-type/success-*.rs");
    t.compile_fail("tests/derive-schema-type/fail-*.rs");
}
