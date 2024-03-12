//! Test that the macros generates compilable code.
#[test]
fn tests() {
    std::env::set_var("MY_CUSTOM_FEATURE", "true");
    std::env::set_var("ACC", "3kBx2h5Y2veb4hZgAJWPrr8RyQESKm5TjzF3ti1QQ4VSYLwK1G");
    std::env::set_var("REF", "0000000000000000000000000000000000000000000000000000000000000000");
    std::env::set_var("CONTRACT", "<1234,0>");
    std::env::set_var("PK_25519", "012a7e286063ae5dfcebce40636c0546d367d8c65cd4cb69aae1af77a4d61412");
    std::env::set_var("PK_ECDSA", "0214e6a60b8fc58ea707d8ee8fa6ca7b28626d4f6f80b170982644c95d12111853");
    std::env::set_var("SG_25519", "ec076ae7adaf0a8b921cf2bad86a1a5b5346226618637aa0d6b30f9616f108f9f482640a4ceb14235569cd3af05fac00be2c82dc81c6f6b4a6ba4ea7c3b51a0b");
    std::env::set_var("SG_ECDSA", "EC076AE7ADAF0A8B921CF2BAD86A1A5B5346226618637AA0D6B30F9616F108F9F482640A4CEB14235569CD3AF05FAC00BE2C82DC81C6F6B4A6BA4EA7C3B51A0B");

    let t = trybuild::TestCases::new();
    t.pass("tests/test-programs/success.rs");
    t.compile_fail("tests/test-programs/fail-*.rs");
}
