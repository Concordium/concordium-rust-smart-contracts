//! Ensure `derive(Deserial)` fails when 'tag' attribute are collides with the
//! default tag for another variant.
use concordium_std::*;

#[derive(Deserial)]
#[concordium(repr(u8))]
enum MyTaggedEnum {
    One,
    #[concordium(tag = 0)]
    Two,
}

fn main() {}
