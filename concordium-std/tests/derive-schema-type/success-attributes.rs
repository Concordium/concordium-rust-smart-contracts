//! Ensure `derive(SchemaType)` generates code successfully for types using
//! attributes.
use concordium_std::*;

#[derive(SchemaType)]
#[concordium(repr(u8))]
enum MyTaggedEnum {
    #[concordium(tag = 42)]
    One,
    Two,
}

#[derive(SchemaType)]
enum MyUntaggedEnum {
    One,
    Two,
}

fn main() {
    {
        let schema_type = <MyTaggedEnum as schema::SchemaType>::get_type();
        assert_eq!(
            schema_type,
            schema::Type::TaggedEnum(collections::BTreeMap::from([
                (42, (String::from("One"), schema::Fields::None)),
                (1, (String::from("Two"), schema::Fields::None))
            ]))
        );
    }

    {
        let schema_type = <MyUntaggedEnum as schema::SchemaType>::get_type();
        assert_eq!(
            schema_type,
            schema::Type::Enum(vec![
                (String::from("One"), schema::Fields::None),
                (String::from("Two"), schema::Fields::None)
            ])
        );
    }
}
