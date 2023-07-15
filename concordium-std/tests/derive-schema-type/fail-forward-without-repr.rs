//! Ensure `derive(SchemaType)` fails when using 'forward' attribute without a
//! 'repr' attribute.
use concordium_std::*;

#[derive(SchemaType)]
enum Count {
    One {
        field: u32,
    },
    #[concordium(forward = [5, 6])]
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
