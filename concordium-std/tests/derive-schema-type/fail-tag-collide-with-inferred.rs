//! Ensure `derive(SchemaType)` fails when a 'tag' attribute collides with the
//! default tag for another variant.
use concordium_std::*;

#[derive(SchemaType)]
#[concordium(repr(u8))]
enum MyTaggedEnum {
    One,
    #[concordium(tag = 0)]
    Two,
}

fn main() {}
