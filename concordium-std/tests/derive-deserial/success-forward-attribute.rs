//! Ensure `derive(Deserial)` generates code successfully for types using
//! attributes.
use concordium_std::*;

#[derive(Debug, Deserial, PartialEq, Eq)]
#[concordium(repr(u8))]
enum Count {
    One {
        field: u32,
    },
    #[concordium(forward = [5, 6])]
    Two(Inner),
}

#[derive(Debug, Deserial, PartialEq, Eq)]
#[concordium(repr(u8))]
enum Inner {
    #[concordium(tag = 5)]
    Alpha {
        balance: u32,
    },
    #[concordium(tag = 6)]
    Beta(u16),
}

fn main() {
    {
        let bytes = [0, 42, 0, 0, 0];
        let value: Count = from_bytes(&bytes).unwrap();
        assert_eq!(
            Count::One {
                field: 42,
            },
            value
        );
    }

    {
        let bytes = [5, 50, 0, 0, 0];
        let value: Count = from_bytes(&bytes).unwrap();
        assert_eq!(
            Count::Two(Inner::Alpha {
                balance: 50,
            }),
            value
        );
    }

    {
        let bytes = [6, 8, 0];
        let value: Count = from_bytes(&bytes).unwrap();
        assert_eq!(Count::Two(Inner::Beta(8)), value);
    }
}
