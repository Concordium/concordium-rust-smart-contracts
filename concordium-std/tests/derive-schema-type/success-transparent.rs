/// Test ensuring derivation works for newtype wrappers with transparent
use concordium_std::*;

/// Simple struct
#[derive(SchemaType)]
#[concordium(transparent)]
struct MyStruct {
    field: u32,
}

/// Nested struct
#[derive(SchemaType)]
#[concordium(transparent)]
struct MyOtherStruct {
    field: MyStruct,
}

/// With field attributes
#[derive(SchemaType)]
#[concordium(transparent)]
struct MyCollection {
    #[concordium(size_length = 1)]
    field: Vec<u32>,
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

    {
        let schema_type = <MyCollection as schema::SchemaType>::get_type();
        assert_eq!(
            schema_type,
            schema::Type::List(schema::SizeLength::U8, Box::new(schema::Type::U32))
        );
    }
}
