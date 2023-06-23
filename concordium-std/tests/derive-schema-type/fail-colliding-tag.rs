//! Ensure `derive(SchemaType)` fails when two 'tag' attributes are colliding.
use concordium_std::*;

#[derive(SchemaType)]
#[concordium(repr(u8))]
enum MyTaggedEnum {
    #[concordium(tag = 42)]
    One,
    #[concordium(tag = 42)]
    Two,
}

fn main() {}
