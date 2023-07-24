//! Ensure `derive(DeserialWithState)` fails when a 'forward' attribute collides
//! with the default tag for another variant.
use concordium_std::*;

#[derive(DeserialWithState)]
#[concordium(state_parameter = "S", repr(u8))]
enum Count<S> {
    One {
        field: StateSet<u32, S>,
    },
    #[concordium(forward = [0, 6])]
    Two(Inner),
}

#[derive(Deserial)]
#[concordium(repr(u8))]
enum Inner {
    Alpha {
        balance: u32,
    },
    #[concordium(tag = 6)]
    Beta(u16),
}

fn main() {}
