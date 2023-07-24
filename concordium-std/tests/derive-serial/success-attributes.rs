//! Ensure `derive(Serial)` generates code successfully for types using
//! attributes.
use concordium_std::*;

#[derive(Serial)]
#[concordium(repr(u8))]
enum MyTaggedEnum {
    #[concordium(tag = 42)]
    One(u8),
    Two(u8),
}

#[derive(Serial)]
#[concordium(repr(u16))]
enum MyTaggedEnumU16 {
    #[concordium(tag = 42)]
    One(u8),
    Two(u8),
}

fn main() {
    {
        let value = MyTaggedEnum::One(3);
        let bytes = to_bytes(&value);
        assert_eq!(bytes, vec![42, 3]);
    }

    {
        let value = MyTaggedEnum::Two(255);
        let bytes = to_bytes(&value);
        assert_eq!(bytes, vec![1, 255]);
    }

    {
        let value = MyTaggedEnumU16::One(3);
        let bytes = to_bytes(&value);
        assert_eq!(bytes, vec![42, 0, 3]);
    }

    {
        let value = MyTaggedEnumU16::Two(255);
        let bytes = to_bytes(&value);
        assert_eq!(bytes, vec![1, 0, 255]);
    }
}
