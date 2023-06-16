//! Ensure `derive(DeserialWithState)` fails when using 'tag' attribute without
//! a 'repr' attribute.
use concordium_std::*;

#[derive(DeserialWithState)]
#[concordium(state_parameter = "S")]
enum MyTaggedEnum<S> {
    #[concordium(tag = 42)]
    One(StateSet<u32, S>),
    Two,
}

fn main() {}
