//! Smart contract test bench
#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;

/// The different errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
enum ContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
}

/// The contract state.
#[derive(Serial, Deserial, Clone, SchemaType)]
struct State {
    u8_value: u8,
}

/// Init function that creates this smart_contract_test_bench.
#[init(contract = "smart_contract_test_bench")]
fn contract_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<State> {
    Ok(State {
        u8_value: 0u8,
    })
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "setU8",
    parameter = "u8",
    error = "ContractError",
    mutable
)]
fn set_u8<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<(), ContractError> {
    let value: u8 = ctx.parameter_cursor().get()?;
    host.state_mut().u8_value = value;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "set_u8_payable",
    parameter = "u8",
    error = "ContractError",
    mutable,
    payable
)]
fn set_u8_payable<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
    _amount: Amount,
) -> Result<(), ContractError> {
    let value: u8 = ctx.parameter_cursor().get()?;
    host.state_mut().u8_value = value;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "view",
    parameter = "HashSha2256",
    error = "ContractError",
    return_value = "State"
)]
fn view<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State, StateApiType = S>,
) -> ReceiveResult<State> {
    Ok(host.state().clone())
}
