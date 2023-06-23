//! Ensure `derive(Deserial)` fails when two 'tag' attributes are colliding.
use concordium_std::*;

#[derive(Deserial)]
#[concordium(repr(u8))]
enum MyTaggedEnum {
    #[concordium(tag = 42)]
    One,
    #[concordium(tag = 42)]
    Two,
}

fn main() {}
