//! Ensure `derive(SchemaType)` fails when using 'tag' attribute without a
//! 'repr' attribute.
use concordium_std::*;

#[derive(SchemaType)]
enum MyTaggedEnum {
    #[concordium(tag = 42)]
    One,
    Two,
}

fn main() {}
