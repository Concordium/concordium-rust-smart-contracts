//! Ensure that `derive(DeserialWithState)` can generate trait implementation
//! when `#[concordium(state_parameter)]` attribute value is not just
//! a type identifier but a type path to trait's associated type
use concordium_std::{DeserialWithState, HasStateApi, StateMap};

pub trait ProxyTrait {
    type State: HasStateApi;
}

#[derive(DeserialWithState)]
#[concordium(state_parameter = "T::State")]
pub struct TestDeserial<T: ProxyTrait> {
    pub test_map: StateMap<u32, String, T::State>,
}

fn main() {}
