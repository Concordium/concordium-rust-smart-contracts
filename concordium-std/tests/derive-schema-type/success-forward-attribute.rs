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

// Example using predefined forwarded tags.

#[derive(SchemaType)]
#[concordium(repr(u8))]
enum Event {
    A {
        field: u32,
    },
    #[concordium(forward = cis2_events)]
    B(Cis2Event),
}

#[derive(SchemaType)]
#[concordium(repr(u8))]
enum Cis2Event {
    #[concordium(tag = 255)]
    Transfer,
    #[concordium(tag = 254)]
    Mint,
    #[concordium(tag = 253)]
    Burn,
    #[concordium(tag = 252)]
    UpdateOperator,
    #[concordium(tag = 251)]
    TokenMetadata,
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

    {
        let schema_type = <Event as schema::SchemaType>::get_type();
        assert_eq!(
            schema_type,
            schema::Type::TaggedEnum(collections::BTreeMap::from([
                (
                    0,
                    (
                        String::from("A"),
                        schema::Fields::Named(vec![(String::from("field"), schema::Type::U32)])
                    )
                ),
                (255, (String::from("Transfer"), schema::Fields::None)),
                (254, (String::from("Mint"), schema::Fields::None)),
                (253, (String::from("Burn"), schema::Fields::None)),
                (252, (String::from("UpdateOperator"), schema::Fields::None)),
                (251, (String::from("TokenMetadata"), schema::Fields::None))
            ]))
        );
    }
}
