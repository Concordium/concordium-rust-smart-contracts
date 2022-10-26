use concordium_std::{Deletable, StateMap, HasStateApi};

#[derive(Deletable)]
#[concordium(state_parameter = "S")]
pub struct TestDeserial<S: HasStateApi> {
    pub test_map: StateMap<u32, String, S>,
}

fn main() { }
