//! Ensure `derive(Serial)` fails when two 'tag' attributes are colliding.
use concordium_std::*;

#[derive(Serial)]
#[concordium(repr(u8))]
enum MyTaggedEnum {
    #[concordium(tag = 42)]
    One,
    #[concordium(tag = 42)]
    Two,
}

fn main() {}
