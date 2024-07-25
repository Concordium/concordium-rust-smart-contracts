//! # Concordium V1 Smart Contract Template

#![cfg_attr(not(feature = "std"), no_std)]

use concordium_std::*;
use core::fmt::Debug;

/// The state of the smart contract.
#[derive(Serialize, SchemaType)]
pub struct State {
    // Add fields to this type to hold state in the smart contract.
    // This field is just an example.
    custom_state_field: i8,
}

/// Errors that may be emitted by this smart contract.
#[derive(Debug, PartialEq, Eq, Reject, Serialize, SchemaType)]
pub enum Error {
    /// Failed parsing the input parameter.
    #[from(ParseError)]
    ParseParams,
    /// Add variants to this enum to be able to return custom errors from the smart contract.
    CustomError,
}

/// Any type implementing Serialize and SchemaType can be
/// used as an input parameter to a smart contract function.
#[derive(Serialize, SchemaType)]
pub struct CustomInputParameter {
    /// Just an example, you could have any fields here.
    pub num: i8,
}

/// Creates a new instance of the smart contract.
#[init(contract = "{{ crate_name }}", parameter = "CustomInputParameter")]
fn init(ctx: &InitContext, _state_builder: &mut StateBuilder) -> InitResult<State> {
    let param: CustomInputParameter = ctx.parameter_cursor().get()?;

    // Create the initial state of the smart contract here.
    // This state can then be used in the other functions.
    Ok(State {
        custom_state_field: param.num,
    })
}

/// Receive function. The input parameter in this function is the boolean variable `return_error`.
///  If `return_error == true`, the receive function will return a custom error.
///  If `return_error == false`, the receive function executes successfully.
#[receive(
    contract = "{{ crate_name }}",
    name = "receive",
    // You can use any other type than bool here, bool is used here only as an example.
    parameter = "bool",
    error = "Error",
    mutable
)]
fn receive(ctx: &ReceiveContext, _host: &mut Host<State>) -> Result<(), Error> {
    // Parse input and apply any other logic relevant for this function of the smart contract.
    // You can mutate the smart contract state here via host.state_mut(), since the receive attribute has the mutable flag.
    // You can return any of your custom error variants from above.

    let return_error = ctx.parameter_cursor().get()?; // Returns Error::ParseError on failure.
    if return_error {
        Err(Error::CustomError)
    } else {
        Ok(())
    }
}

/// Returns the state of the smart contract.
#[receive(contract = "{{ crate_name }}", name = "view", return_value = "State")]
fn view<'a>(_ctx: &ReceiveContext, host: &'a Host<State>) -> ReceiveResult<&'a State> {
    Ok(host.state())
}
