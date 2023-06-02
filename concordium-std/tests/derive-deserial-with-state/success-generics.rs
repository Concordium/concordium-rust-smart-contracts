//! Ensure that `derive(DeserialWithState)` can generate trait implementation
//! when `#[concordium(state_parameter)]` attribute value is not just
//! a type identifier but a type path to trait's associated type
use concordium_std::*;

#[derive(DeserialWithState)]
#[concordium(state_parameter = "T")]
struct State1<T, A> {
    map:   StateMap<u32, String, T>,
    other: A,
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
