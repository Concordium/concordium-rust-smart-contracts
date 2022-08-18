use concordium_std::*;

#[init(contract = "error")]
fn init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<()> {
    Ok(())
}

/// The different errors the contract can produce.
#[derive(Serial, Debug, PartialEq, Eq, Reject, SchemaType)]
enum CustomContractError {
    SomeError(String),
    ParseError,
}

impl From<ParseError> for CustomContractError {
    fn from(_: ParseError) -> Self { CustomContractError::ParseError }
}

#[receive(
    contract = "error",
    name = "receive",
    parameter = "bool",
    return_value = "String",
    error = "CustomContractError"
)]
fn receive<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    _host: &impl HasHost<(), StateApiType = S>,
) -> Result<String, CustomContractError> {
    let param: bool = ctx.parameter_cursor().get()?;
    if param {
        Ok("Success!".into())
    } else {
        Err(CustomContractError::SomeError("Failure...".into()))
    }
}
