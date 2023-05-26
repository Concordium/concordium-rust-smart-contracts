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

#[test]
fn serial() {
    let t = trybuild::TestCases::new();
    t.pass("tests/derive-serial/success-*.rs");
}

#[test]
fn deserial() {
    let t = trybuild::TestCases::new();
    t.pass("tests/derive-deserial/success-*.rs");
}

#[cfg(feature = "build-schema")]
#[test]
fn schema_type() {
    let t = trybuild::TestCases::new();
    t.pass("tests/derive-schema-type/success-*.rs");
}
