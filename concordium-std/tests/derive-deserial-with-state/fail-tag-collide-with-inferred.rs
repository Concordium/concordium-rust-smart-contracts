//! Ensure `derive(DeserialWithState)` fails when 'tag' attribute are collides
//! with the default tag for another variant.
use concordium_std::*;

#[derive(DeserialWithState)]
#[concordium(repr(u8))]
#[concordium(state_parameter = "S")]
enum MyTaggedEnum<S> {
    One(StateSet<u32, S>),
    #[concordium(tag = 0)]
    Two,
}

fn main() {}
