//! Ensure `derive(Deletable)` generates code successfully for the simplest
//! case when `#[concordium(state_parameter)]` is just a type identifier
use concordium_std::{Deletable, HasStateApi, StateMap};

#[derive(Deletable)]
#[concordium(state_parameter = "S")]
pub struct TestDeserial<S: HasStateApi> {
    pub test_map: StateMap<u32, String, S>,
}

fn main() {}
