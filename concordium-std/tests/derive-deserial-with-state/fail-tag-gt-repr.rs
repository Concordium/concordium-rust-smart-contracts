//! Ensure `derive(DeserialWithState)` fails when a 'tag' attribute is greater
//! than what 'repr(u8)' can represent.
use concordium_std::*;

#[derive(DeserialWithState)]
#[concordium(repr(u8))]
#[concordium(state_parameter = "S")]
enum MyTaggedEnum<S> {
    #[concordium(tag = 256)]
    One(StateSet<u32, S>),
    Two,
}

fn main() {}
