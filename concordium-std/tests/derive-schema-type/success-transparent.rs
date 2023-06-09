/// Test ensuring derivation works for newtype wrappers with transparent
use concordium_std::*;

#[derive(SchemaType)]
#[concordium(transparent)]
struct MyStruct {
    field: u32,
}

#[derive(SchemaType)]
#[concordium(transparent)]
struct MyOtherStruct {
    field: MyStruct,
}

fn main() {
    {
        let schema_type = <MyStruct as schema::SchemaType>::get_type();
        assert_eq!(schema_type, schema::Type::U32);
    }

    {
        let schema_type = <MyOtherStruct as schema::SchemaType>::get_type();
        assert_eq!(schema_type, schema::Type::U32);
    }
}
