//! Ensure `derive(Serial)` fails when using 'forward' attribute without a
//! 'repr' attribute.
use concordium_std::*;

#[derive(Serial)]
enum Count {
    One {
        field: u32,
    },
    #[concordium(forward = [5, 6])]
    Two(Inner),
}

#[derive(Serial)]
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
