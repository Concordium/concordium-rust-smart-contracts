use concordium_std::{Deletable, HasStateApi, StateMap};

pub trait ProxyTrait {
    type State: HasStateApi;
}

#[derive(Deletable)]
#[concordium(state_parameter = "T::State")]
pub struct TestDeserial<T: ProxyTrait> {
    pub test_map: StateMap<u32, String, T::State>,
}

fn main() {}
