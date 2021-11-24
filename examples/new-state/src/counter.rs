use concordium_std::*;

type CounterState = u32;

#[derive(Serialize)]
struct StateKey;

#[init(contract = "counter-new-state")]
fn init(_ctx: &impl HasInitContext, state: &mut State) -> InitResult<()> {
    state.insert_item(StateKey, 0)?;

    Ok(())
}

#[receive(contract = "counter-new-state", name = "increment")]
fn receive_increment<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut State,
) -> ReceiveResult<A> {
}
