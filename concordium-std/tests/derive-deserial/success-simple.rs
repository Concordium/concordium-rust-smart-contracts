/// Test ensuring derivation works for simple types.
use concordium_std::*;

#[derive(Deserial)]
struct MyStruct {
    field:       u64, // 8 bytes
    other_field: u8,  // 1 byte
}

#[derive(Deserial)]
enum MyEnum {
    One(u64),
    Two(u16),
}

fn main() {
    {
        let bytes = [0u8; 9];
        let _value: MyStruct = from_bytes(&bytes).expect("Deserialize MyStruct");
    }
    {
        let bytes = [0u8; 9];
        let _value: MyEnum = from_bytes(&bytes).expect("Deserialize MyEnum");
    }
}
