//! Ensure `derive(DeserialWithState)` fails when using 'forward' attribute
//! without a 'repr' attribute.
use concordium_std::*;

#[derive(DeserialWithState)]
#[concordium(state_parameter = "S")]
enum Count<S> {
    One {
        field: StateSet<u32, S>,
    },
    #[concordium(forward = [5, 6])]
    Two(Inner),
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
