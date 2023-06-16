//! Ensure `derive(Deserial)` fails when using 'tag' attribute without a
//! 'repr' attribute.
use concordium_std::*;

#[derive(Deserial)]
enum MyTaggedEnum {
    #[concordium(tag = 42)]
    One,
    Two,
}

fn main() {}
