//! # A smart contract for buying icecream safely
//!
//! This contract solves a very realistic problem related to icecream.
//! Imagine you want to purchase icecream from a vendor, and that you hate
//! eating icecream when it's raining. This contract solves the problem by
//! acting as a middleman which only allows your transfer to the icecream vendor
//! to go through if the sun is shining.
//!
//! The icecream contract relies on a weather service contract to determine the
//! weather. Both contracts are included in this module.
//!
//!
//! ## The Icecream Contract
//!
//! The contract is initialised with a contract address to the weather service
//! contract.
//!
//! Its primary function is `buy_icecream`, which works as follows:
//!  - It is called with an `AccountAddress` of the icecream vendor and the
//!    icecream price as amount.
//!  - It queries the `Weather` from the weather_service contract.
//!  - If it's `Weather::Sunny`, the transfer goes through to the icecream
//!    vendor.
//!  - Otherwise, the amount is returned to invoker.
//!
//! It also has a `replace_weather_service` function, in which the owner can
//! replace the weather service.
//!
//!
//! ## The Weather Service Contract
//!
//! The contract is initialised with the `Weather`.
//!
//! It has `get` and `set` receive functions, which either return or set the
//! weather. Only the owner can update the weather.

#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;

#[derive(Serialize, SchemaType, Clone)]
struct State {
    weather_service: ContractAddress,
}

#[derive(Serialize, SchemaType, Clone, Copy)]
pub enum Weather {
    Rainy,
    Sunny,
}

/// The custom errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
pub enum ContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Failed account transfer.
    #[from(TransferError)]
    TransferError,
    /// Failed contract invoke.
    ContractInvokeError,
    Unauthenticated,
}

impl<A> From<CallContractError<A>> for ContractError {
    fn from(_: CallContractError<A>) -> Self { Self::ContractInvokeError }
}

type ContractResult<A> = Result<A, ContractError>;

/// Initialise the contract with the contract address of the weather service.
#[init(contract = "icecream", parameter = "ContractAddress")]
fn contract_init(ctx: &InitContext, _state_builder: &mut StateBuilder) -> InitResult<State> {
    let weather_service: ContractAddress = ctx.parameter_cursor().get()?;
    Ok(State {
        weather_service,
    })
}

/// Attempt purchasing icecream from the icecream vendor.
#[receive(
    contract = "icecream",
    name = "buy_icecream",
    parameter = "AccountAddress",
    payable,
    mutable,
    error = "ContractError"
)]
fn contract_buy_icecream(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    amount: Amount,
) -> ContractResult<()> {
    let weather_service = host.state().weather_service;
    let icecream_vendor: AccountAddress = ctx.parameter_cursor().get()?;

    let weather = host
        .invoke_contract_raw(
            &weather_service,
            Parameter::empty(),
            EntrypointName::new_unchecked("get"),
            Amount::zero(),
        )?
        .1;
    let weather = if let Some(mut weather) = weather {
        weather.get()?
    } else {
        return Err(ContractError::ContractInvokeError);
    };

    match weather {
        Weather::Rainy => {
            host.invoke_transfer(&ctx.invoker(), amount)?;
            // We could also abort here, but this is useful to show off some
            // testing features.
        }
        Weather::Sunny => host.invoke_transfer(&icecream_vendor, amount)?,
    }
    Ok(())
}

/// Replace the weather service with another.
/// Only the owner of the contract can do so.
#[receive(
    contract = "icecream",
    name = "replace_weather_service",
    parameter = "ContractAddress",
    mutable,
    error = "ContractError"
)]
fn contract_replace_weather_service(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
) -> ContractResult<()> {
    ensure_eq!(Address::Account(ctx.owner()), ctx.sender(), ContractError::Unauthenticated);
    let new_weather_service: ContractAddress = ctx.parameter_cursor().get()?;
    host.state_mut().weather_service = new_weather_service;
    Ok(())
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/// Initialse the weather service with the weather.
#[init(contract = "weather", parameter = "Weather")]
fn weather_init(ctx: &InitContext, _state_builder: &mut StateBuilder) -> InitResult<Weather> {
    let weather = ctx.parameter_cursor().get()?;
    Ok(weather)
}

/// Get the current weather.
#[receive(contract = "weather", name = "get", return_value = "Weather", error = "ContractError")]
fn weather_get(_ctx: &ReceiveContext, host: &Host<Weather>) -> ContractResult<Weather> {
    Ok(*host.state())
}

/// Update the weather.
#[receive(
    contract = "weather",
    name = "set",
    parameter = "Weather",
    mutable,
    error = "ContractError"
)]
fn weather_set(ctx: &ReceiveContext, host: &mut ExternHost<Weather>) -> ContractResult<()> {
    ensure_eq!(Address::Account(ctx.owner()), ctx.sender(), ContractError::Unauthenticated); // Only the owner can update the weather.
    *host.state_mut() = ctx.parameter_cursor().get()?;
    Ok(())
}
