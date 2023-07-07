//! Ensure `derive(SchemaType)` generates code successfully for types using
//! attributes.
use concordium_std::*;

#[derive(SchemaType)]
#[concordium(repr(u8))]
enum Count {
    One,
    #[concordium(forward = [5, 6])]
    Two(Inner),
}

#[derive(SchemaType)]
#[concordium(repr(u8))]
enum Inner {
    #[concordium(tag = 5)]
    Alpha,
    #[concordium(tag = 6)]
    Beta(u8),
}

fn main() {
    {
        let schema_type = <Count as schema::SchemaType>::get_type();
        assert_eq!(
            schema_type,
            schema::Type::TaggedEnum(collections::BTreeMap::from([
                (0, (String::from("One"), schema::Fields::None)),
                (5, (String::from("Alpha"), schema::Fields::None)),
                (6, (String::from("Beta"), schema::Fields::Unnamed(vec![schema::Type::U8])))
            ]))
        );
    }
}
