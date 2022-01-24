#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;

#[contract_state(contract = "icecream")]
#[derive(Serialize, SchemaType)]
struct State {
    weather_service: ContractAddress,
    current_state:   StateMachine,
}

#[derive(Serialize, SchemaType)]
enum StateMachine {
    ReadyToBuy,
    WaitingForWeather {
        icecream_vendor: AccountAddress,
    },
}

#[contract_state(contract = "weather")]
#[derive(Serialize, SchemaType)]
enum Weather {
    Rainy,
    Sunny,
}

#[init(contract = "icecream", parameter = "ContractAddress")]
fn contract_init(ctx: &impl HasInitContext) -> InitResult<State> {
    let weather_service = ctx.parameter_cursor().get()?;
    let current_state = StateMachine::ReadyToBuy;
    Ok(State {
        weather_service,
        current_state,
    })
}

#[receive(contract = "icecream", name = "buy_icecream", parameter = "AccountAddress", payable)]
fn contract_buy_icecream<A: HasActions>(
    ctx: &impl HasReceiveContext,
    _amount: Amount, // Contract accepts the money.
    state: &mut State,
) -> ReceiveResult<A> {
    match state.current_state {
        StateMachine::ReadyToBuy => {
            let icecream_vendor = ctx.parameter_cursor().get()?;
            state.current_state = StateMachine::WaitingForWeather {
                icecream_vendor,
            };
            Ok(send(
                &state.weather_service,
                ReceiveName::new_unchecked("weather.get"),
                Amount::zero(),
                &ReceiveName::new_unchecked("icecream.receive_weather"), // The callback function
            ))
        }
        StateMachine::WaitingForWeather {
            icecream_vendor: _,
        } => Err(Reject::default()), // Trying to buy, while still waiting for the weather.
    }
}

#[receive(contract = "icecream", name = "receive_weather", parameter = "Weather")]
fn contract_receive_weather<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut State,
) -> ReceiveResult<A> {
    match state.current_state {
        StateMachine::ReadyToBuy => Err(Reject::default()), /* Should only be called when
                                                              * contract */
        // is waiting for weather.
        StateMachine::WaitingForWeather {
            icecream_vendor,
        } => match ctx.parameter_cursor().get()? {
            Weather::Rainy => Ok(A::simple_transfer(&ctx.owner(), ctx.self_balance())), /* Return money to owner. Not the right weather for icecream. */
            Weather::Sunny => Ok(A::simple_transfer(&icecream_vendor, ctx.self_balance())), /* Buy the icecream!! */
        },
    }
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[init(contract = "weather", parameter = "Weather")]
fn weather_init(ctx: &impl HasInitContext) -> InitResult<Weather> {
    Ok(ctx.parameter_cursor().get()?)
}

#[receive(contract = "weather", name = "get", parameter = "OwnedReceiveName")]
fn weather_get<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut Weather,
) -> ReceiveResult<A> {
    match ctx.sender() {
        Address::Account(_) => Err(Reject::default()), // Only invokeable by contracts.
        Address::Contract(contract_address) => {
            let receive_name: OwnedReceiveName = ctx.parameter_cursor().get()?;
            Ok(send(&contract_address, receive_name.as_ref(), Amount::zero(), state))
        }
    }
}

#[receive(contract = "weather", name = "set", parameter = "Weather")]
fn weather_set<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut Weather,
) -> ReceiveResult<A> {
    assert_eq!(Address::Account(ctx.owner()), ctx.sender());
    *state = ctx.parameter_cursor().get()?;
    Ok(A::accept())
}
