//! Ensure `derive(DeserialWithState)` fails when two 'tag' attributes are
//! colliding.
use concordium_std::*;

#[derive(DeserialWithState)]
#[concordium(repr(u8))]
#[concordium(state_parameter = "S")]
enum MyTaggedEnum<S> {
    #[concordium(tag = 42)]
    One(StateMap<u32, String, S>),
    #[concordium(tag = 42)]
    Two,
}

fn main() {}
