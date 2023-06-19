/// Test ensuring derivation works for types with type parameters.
use concordium_std::*;

#[derive(SchemaType)]
struct MyStruct<A> {
    field:       A,
    other_field: u8,
}

#[derive(SchemaType)]
struct MyOtherStruct<A, B> {
    field:       A,
    other_field: B,
}

#[derive(SchemaType)]
enum MyEnum<A> {
    One(u32),
    Two(A),
}

#[derive(SchemaType)]
enum MyOtherEnum<A, B> {
    One(u32),
    Two(A, B),
}

fn main() {
    let _type = <MyStruct<u8> as schema::SchemaType>::get_type();
    let _type = <MyOtherStruct<u8, u16> as schema::SchemaType>::get_type();
    let _type = <MyEnum<u8> as schema::SchemaType>::get_type();
    let _type = <MyOtherEnum<u8, u16> as schema::SchemaType>::get_type();
}
