//! Ensure `derive(SchemaType)` fails when a 'forward' attribute is greater than
//! what 'repr(u8)' can represent.
use concordium_std::*;

#[derive(SchemaType)]
#[concordium(repr(u8))]
enum Count {
    One {
        field: u32,
    },
    #[concordium(forward = [500, 6])]
    Two(Inner),
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
