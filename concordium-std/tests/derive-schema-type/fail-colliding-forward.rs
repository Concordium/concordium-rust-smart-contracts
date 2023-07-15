//! Ensure `derive(SchemaType)` fails when 'forward' attributes are colliding.
use concordium_std::*;

#[derive(SchemaType)]
#[concordium(repr(u8))]
enum Count {
    One {
        field: u32,
    },
    #[concordium(forward = [5, 6])]
    Two(Inner),

    #[concordium(forward = 5)]
    Three(Inner),
}

#[derive(SchemaType)]
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
