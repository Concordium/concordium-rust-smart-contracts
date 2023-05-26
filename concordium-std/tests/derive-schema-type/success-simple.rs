/// Test ensuring derivation works for simple types.
use concordium_std::*;

#[derive(SchemaType)]
struct MyStruct {
    field:       u32,
    other_field: u8,
}

#[derive(SchemaType)]
enum MyEnum {
    One(u32),
    Two(u8),
}

fn main() {
    let _type = <MyStruct as schema::SchemaType>::get_type();
    let _type = <MyEnum as schema::SchemaType>::get_type();
}
