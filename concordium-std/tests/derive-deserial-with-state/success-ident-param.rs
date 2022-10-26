use concordium_std::{DeserialWithState, HasStateApi, ParseResult, Read, StateMap};

#[derive(DeserialWithState)]
#[concordium(state_parameter = "S")]
pub struct TestDeserial<S: HasStateApi> {
    pub test_map: StateMap<u32, String, S>,
}

fn main() {}
