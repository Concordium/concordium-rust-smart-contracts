//! Ensure `derive(DeserialWithState)` fails when a 'forward' attribute is
//! greater than what 'repr(u8)' can represent.
use concordium_std::*;

#[derive(DeserialWithState)]
#[concordium(state_parameter = "S", repr(u8))]
enum Count<S> {
    One {
        field: StateSet<u32, S>,
    },
    #[concordium(forward = [500, 6])]
    Two(Inner),
}

#[derive(Deserial)]
#[concordium(repr(u16))]
enum Inner {
    #[concordium(tag = 500)]
    Alpha {
        balance: u32,
    },
    #[concordium(tag = 6)]
    Beta(u16),
}

fn main() {}
