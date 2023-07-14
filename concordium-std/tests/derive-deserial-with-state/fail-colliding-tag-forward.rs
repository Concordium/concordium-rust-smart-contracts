//! Ensure `derive(DeserialWithState)` fails when 'forward' and 'tag' attributes
//! are colliding.
use concordium_std::*;

#[derive(DeserialWithState)]
#[concordium(state_parameter = "S", repr(u8))]
enum Count<S> {
    One {
        field: StateSet<u32, S>,
    },
    #[concordium(forward = [5, 6])]
    Two(Inner),

    #[concordium(tag = 5)]
    Three(Inner),
}

#[derive(Deserial)]
#[concordium(repr(u8))]
enum Inner {
    #[concordium(tag = 5)]
    Alpha {
        balance: u32,
    },
    #[concordium(tag = 6)]
    Beta(u16),
}

fn main() {}
