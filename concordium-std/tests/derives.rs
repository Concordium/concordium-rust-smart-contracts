#[test]
fn deserial_with_state() {
    let t = trybuild::TestCases::new();
    t.pass("tests/derive-deserial-with-state/success-ident-param.rs");
    t.pass("tests/derive-deserial-with-state/success-assoc-type.rs");
}

#[test]
fn deletable() {
    let t = trybuild::TestCases::new();
    t.pass("tests/derive-deletable/success-ident-param.rs");
    t.pass("tests/derive-deletable/success-assoc-type.rs");
}
