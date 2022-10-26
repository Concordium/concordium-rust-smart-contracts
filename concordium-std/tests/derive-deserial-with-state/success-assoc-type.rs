use concordium_std::{DeserialWithState, HasStateApi, ParseResult, Read, StateMap};

pub trait ProxyTrait {
    type State: HasStateApi;
}

#[derive(DeserialWithState)]
#[concordium(state_parameter = "T::State")]
pub struct TestDeserial<T: ProxyTrait> {
    pub test_map: StateMap<u32, String, T::State>,
}

fn main() {}
