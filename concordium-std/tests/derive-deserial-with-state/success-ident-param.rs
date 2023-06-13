//! Ensure `derive(DeserialWithState)` generates code successfully for the
//! simplest case when `#[concordium(state_parameter)]` is just a type
//! identifier
use concordium_std::{DeserialWithState, HasStateApi, StateMap};

#[derive(DeserialWithState)]
#[concordium(state_parameter = "S")]
pub struct TestDeserial<S: HasStateApi> {
    pub test_map: StateMap<u32, String, S>,
}

fn main() {}
