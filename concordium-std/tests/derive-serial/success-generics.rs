/// Test ensuring derivation works for types with type parameters.
use concordium_std::*;

#[derive(Serial)]
struct MyStruct<A> {
    field:       A,
    other_field: u8,
}

#[derive(Serial)]
struct MyOtherStruct<A, B> {
    field:       A,
    other_field: B,
}

#[derive(Serial)]
enum MyEnum<A> {
    One(u32),
    Two(A),
}

#[derive(Serial)]
enum MyOtherEnum<A, B> {
    One(u32),
    Two(A, B),
}

#[derive(Serial)]
#[concordium(state_parameter = "S")]
struct WithStateParameter<S: HasStateApi> {
    test_map: StateMap<u32, String, S>,
}

#[derive(Serial)]
#[concordium(state_parameter = "S")]
struct WithStateParameterWhere<S>
where
    S: HasStateApi,
    S: Clone, {
    test_map: StateMap<u32, String, S>,
}

#[rustfmt::skip] // skip formatting to maintain lack of trailing comma
mod inner {
    use super::*;
    #[derive(Serial)]
    #[concordium(state_parameter = "S")]
    struct WithStateParameterWhereTwo<S>
    where
        S: HasStateApi,
        S: Clone { // note the lack of comma compared to the test above
        test_map: StateMap<u32, String, S>,
    }

    #[derive(Serial)]
    #[concordium(state_parameter = "S")]
    struct WithStateParameterWhereThree<S: HasStateApi>
    where // empty where clause
        {
        test_map: StateMap<u32, String, S>,
    }
}


trait ProxyTrait {
    type State: HasStateApi;
}

#[derive(Serial)]
#[concordium(state_parameter = "T::State")]
struct WithAssocStateParameter<T: ProxyTrait> {
    test_map: StateMap<u32, String, T::State>,
}

fn main() {
    {
        let value = MyStruct::<u32> {
            field:       42,
            other_field: 5,
        };
        let _bytes = to_bytes(&value);
    }
    {
        let value = MyOtherStruct::<u64, u16> {
            field:       42,
            other_field: 5,
        };
        let _bytes = to_bytes(&value);
    }
    {
        let value = MyEnum::<u64>::Two(1);
        let _bytes = to_bytes(&value);
    }
    {
        let value = MyOtherEnum::<u64, u16>::Two(1, 15);
        let _bytes = to_bytes(&value);
    }
}
