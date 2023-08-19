/// Test ensuring derivation works for types with type parameters.
use concordium_std::*;

#[derive(Deserial)]
struct MyStruct<A> {
    field:       A,
    other_field: u8,
}

#[derive(Deserial)]
struct MyOtherStruct<A, B> {
    field:       A,
    other_field: B,
}

#[derive(Deserial)]
enum MyEnum<A> {
    One(u32),
    Two(A),
}

#[derive(Deserial)]
enum MyOtherEnum<A, B> {
    One(u32),
    Two(A, B),
}

#[derive(Deserial)]
struct WithStateParameterWhere<S>
where
    S: Clone,
    S: PartialOrd, {
    value: S,
}

#[rustfmt::skip] // skip formatting to maintain lack of trailing comma
mod inner {
    use super::*;
    #[derive(Deserial)]
    struct WithStateParameterWhereTwo<S>
    where
        S: Clone,
        // note the lack of comma compared to the test above
        S: PartialOrd {
        value: S,
    }

    #[derive(Deserial)]
    struct WithStateParameterWhereThree<S>
    where // empty where clause
    {
        value: S,
    }
}


#[derive(Deserial)]
#[concordium(bound(deserial = ""))]
struct ExplicitBound<A> {
    field: marker::PhantomData<A>,
}
struct NotImplemtingDeserial;

fn main() {
    {
        let bytes = [0u8; 9];
        let _value: MyStruct<u64> = from_bytes(&bytes).expect("Deserialize MyStruct");
    }
    {
        let bytes = [0u8; 9];
        let _value: MyOtherStruct<u64, u8> = from_bytes(&bytes).expect("Deserialize MyOtherStruct");
    }
    {
        let bytes = [1u8; 9];
        let _value: MyEnum<u64> = from_bytes(&bytes).expect("Deserialize MyOtherStruct");
    }
    {
        let bytes = [1u8; 10];
        let _value: MyOtherEnum<u64, u8> = from_bytes(&bytes).expect("Deserialize MyOtherStruct");
    }
    {
        let bytes = [0u8; 0];
        let _value: ExplicitBound<NotImplemtingDeserial> =
            from_bytes(&bytes).expect("Deserialize ExplicitBound");
    }
}
