//! Ensure `derive(Serial)` fails when using 'tag' attribute without a
//! 'repr' attribute.
use concordium_std::*;

#[derive(Serial)]
enum MyTaggedEnum {
    #[concordium(tag = 42)]
    One,
    Two,
}

fn main() {}
