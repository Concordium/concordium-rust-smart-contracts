//! Ensure `derive(Serial)` fails when a 'tag' attribute is greater than what
//! 'repr(u8)' can represent.
use concordium_std::*;

#[derive(Serial)]
#[concordium(repr(u8))]
enum MyTaggedEnum {
    #[concordium(tag = 256)]
    One,
    Two,
}

fn main() {}
