#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;

type WeatherOracle = ContractAddress; // Weather oracle

#[derive(Serialize, SchemaType, Clone)]
enum Weather {
    Raining,
    Sunny,
}

#[init(contract = "icecream", parameter = "ContractAddress")]
fn contract_init(ctx: &impl HasInitContext) -> InitResult<((), WeatherOracle)> {
    let weather_oracle = ctx.parameter_cursor().get()?;
    let return_value = ();
    Ok((return_value, weather_oracle))
}

#[receive(contract = "icecream", name = "buy_icecream", parameter = "AccountAddress", payable)]
fn contract_buy_icecream(
    ctx: &impl HasReceiveContext,
    ops: &mut impl HasOperations<WeatherOracle>,
    _amount: Amount, // Contract accepts the money.
    weather_oracle: &mut WeatherOracle,
) -> ReceiveResult<()> {
    let weather = ops
        .invoke_contract(
            weather_oracle,
            &weather_oracle.clone(),
            Parameter(&[]),
            EntrypointName::new_unchecked("get"),
            Amount::zero(),
        )
        .unwrap_abort()
        .1
        .unwrap_abort()
        .get()?;

    let icecream_vendor = ctx.parameter_cursor().get()?;

    match weather {
        Weather::Raining => ops
            .invoke_transfer(&ctx.owner(), ctx.self_balance())
            .expect_report("Returning CCD to owner failed."),
        Weather::Sunny => ops
            .invoke_transfer(&icecream_vendor, ctx.self_balance())
            .expect_report("Sending CCD to icecream vendor failed."),
    }
    Ok(())
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[init(contract = "weather", parameter = "Weather")]
fn weather_init(ctx: &impl HasInitContext) -> InitResult<((), Weather)> {
    let return_value = ();
    Ok((return_value, ctx.parameter_cursor().get()?))
}

#[receive(contract = "weather", name = "get", parameter = "OwnedReceiveName")]
fn weather_get(
    _ctx: &impl HasReceiveContext,
    _ops: &mut impl HasOperations<Weather>,
    weather: &mut Weather,
) -> ReceiveResult<Weather> {
    Ok(weather.clone())
}

#[receive(contract = "weather", name = "set", parameter = "Weather")]
fn weather_set(
    ctx: &impl HasReceiveContext,
    _ops: &mut impl HasOperations<Weather>,
    weather: &mut Weather,
) -> ReceiveResult<()> {
    assert_eq!(Address::Account(ctx.owner()), ctx.sender());
    *weather = ctx.parameter_cursor().get()?;
    Ok(())
}
