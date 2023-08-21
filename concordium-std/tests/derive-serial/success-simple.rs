//! Ensure `derive(Serial)` generates code successfully for the
//! simplest case when `#[concordium(state_parameter)]` is set.
use concordium_std::*;

#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
struct State<S> {
    map: StateMap<u8, u16, S>,
    set: StateSet<u32, S>,
}

#[init(contract = "test")]
fn contract_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    Ok(State {
        map: state_builder.new_map(),
        set: state_builder.new_set(),
    })
}

fn main() {}
