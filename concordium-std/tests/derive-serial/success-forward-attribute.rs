//! Ensure `derive(Serial)` generates code successfully for enums using
//! forward attribute.
use concordium_std::*;

#[derive(Serial)]
#[concordium(repr(u8))]
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

fn main() {
    {
        let value = Count::One {
            field: 42,
        };
        let bytes = to_bytes(&value);
        assert_eq!(bytes, vec![0, 42, 0, 0, 0]);
    }
    {
        let value = Count::Two(Inner::Alpha {
            balance: 50,
        });
        let bytes = to_bytes(&value);
        assert_eq!(bytes, vec![5, 50, 0, 0, 0]);
    }

    {
        let value = Count::Two(Inner::Beta(8));
        let bytes = to_bytes(&value);
        assert_eq!(bytes, vec![6, 8, 0]);
    }
}
