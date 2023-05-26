/// Test ensuring derivation works for simple types.
use concordium_std::*;

#[derive(Serial)]
struct MyStruct {
    field:       u32,
    other_field: u8,
}

#[derive(Serial)]
enum MyEnum {
    One(u32),
    Two(u8),
}

fn main() {
    {
        let value = MyStruct {
            field:       42,
            other_field: 5,
        };
        let _bytes = to_bytes(&value);
    }

    {
        let value = MyEnum::Two(1);
        let _bytes = to_bytes(&value);
    }
}
