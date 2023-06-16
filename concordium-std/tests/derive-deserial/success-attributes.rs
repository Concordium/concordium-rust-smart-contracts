//! Ensure `derive(Deserial)` generates code successfully for types using
//! attributes.
use concordium_std::*;

#[derive(Debug, Deserial, PartialEq, Eq)]
#[concordium(repr(u8))]
enum MyTaggedEnum {
    #[concordium(tag = 42)]
    One(u8),
    Two(u8),
}

#[derive(Debug, Deserial, PartialEq, Eq)]
#[concordium(repr(u16))]
enum MyTaggedEnumU16 {
    #[concordium(tag = 42)]
    One(u8),
    Two(u8),
}

fn main() {
    {
        let bytes = [42u8, 3];
        let value: MyTaggedEnum = from_bytes(&bytes).expect("Deserialize MyTaggedEnum");
        assert_eq!(MyTaggedEnum::One(3), value);
    }
    {
        let bytes = [1u8, 255];
        let value: MyTaggedEnum = from_bytes(&bytes).expect("Deserialize MyTaggedEnum");
        assert_eq!(MyTaggedEnum::Two(255), value);
    }
    {
        let bytes = [42u8, 0, 3];
        let value: MyTaggedEnumU16 = from_bytes(&bytes).expect("Deserialize MyTaggedEnumU16");
        assert_eq!(MyTaggedEnumU16::One(3), value);
    }
    {
        let bytes = [1u8, 0, 255];
        let value: MyTaggedEnumU16 = from_bytes(&bytes).expect("Deserialize MyTaggedEnumU16");
        assert_eq!(MyTaggedEnumU16::Two(255), value);
    }
}
