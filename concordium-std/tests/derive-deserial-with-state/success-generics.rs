//! Ensure that `derive(DeserialWithState)` can generate a trait implementation
//! when `#[concordium(state_parameter)]` attribute value is not just
//! a type identifier but a type path to the trait's associated type.
use concordium_std::*;

#[derive(DeserialWithState)]
#[concordium(state_parameter = "T")]
struct State1<T, A> {
    map:   StateMap<u32, String, T>,
    other: A,
}

#[derive(DeserialWithState)]
#[concordium(state_parameter = "S")]
struct WithStateParameterWhere<S>
where
    S: HasStateApi,
    S: Clone, {
    test_map: StateMap<u32, String, S>,
}

#[rustfmt::skip] // maintain lack of trailing comma, and empty where clause
mod inner {
    use super::*;
    #[derive(DeserialWithState)]
    #[concordium(state_parameter = "S")]
    struct WithStateParameterWhereTwo<S>
    where
        S: HasStateApi,
        S: Clone { // no trailing comma
        test_map: StateMap<u32, String, S>,
    }

    #[derive(DeserialWithState)]
    #[concordium(state_parameter = "S")]
    struct WithStateParameterWhereThree<S: Deserial>
    where //empty where clause
    {
        test: S,
    }
}

trait ProxyTrait {
    type State: HasStateApi;
}

#[derive(DeserialWithState)]
#[concordium(state_parameter = "T::State")]
struct State2<T: ProxyTrait, A> {
    test_map: StateMap<u32, String, T::State>,
    field:    A,
}

fn main() {}
