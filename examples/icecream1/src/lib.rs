#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;

#[derive(Serialize, SchemaType, Clone)]
struct State {
    weather_service: ContractAddress,
}

#[derive(Serialize, SchemaType, Clone)]
enum Weather {
    Rainy,
    Sunny,
}

#[init(contract = "icecream", parameter = "ContractAddress")]
fn contract_init(ctx: &impl HasInitContext) -> InitResult<((), State)> {
    let weather_service: ContractAddress = ctx.parameter_cursor().get()?; // Weather service address.
    let return_value = ();
    Ok((return_value, State {
        weather_service,
    }))
}

#[receive(contract = "icecream", name = "buy_icecream", parameter = "AccountAddress", payable)]
fn contract_buy_icecream(
    ctx: &impl HasReceiveContext,
    ops: &mut impl HasOperations<State>,
    amount: Amount,
    state: &mut State,
) -> ReceiveResult<()> {
    let weather = ops
        .invoke_contract(
            state,
            &state.weather_service.clone(),
            Parameter(&[]),
            EntrypointName::new_unchecked("get"),
            Amount::zero(),
        )
        .unwrap_abort()
        .1
        .unwrap_abort()
        .get()?;

    let icecream_vendor: AccountAddress = ctx.parameter_cursor().get()?;

    match weather {
        Weather::Rainy => {
            ops.invoke_transfer(&ctx.owner(), amount).expect("Returning CCD to owner failed.")
            // Could just abort here.
        }
        Weather::Sunny => ops
            .invoke_transfer(&icecream_vendor, amount)
            .expect("Sending CCD to icecream vendor failed."),
    }
    Ok(())
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[init(contract = "weather", parameter = "Weather")]
fn weather_init(ctx: &impl HasInitContext) -> InitResult<((), Weather)> {
    let return_value = ();
    Ok((return_value, ctx.parameter_cursor().get()?))
}

#[receive(contract = "weather", name = "get", return_value = "Weather")]
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

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    const OWNER_ADDR: AccountAddress = AccountAddress([0; 32]);
    const SELF_ADDR: ContractAddress = ContractAddress {
        index:    0,
        subindex: 1,
    };
    const WEATHER_SERVICE: ContractAddress = ContractAddress {
        index:    1,
        subindex: 0,
    };
    const ICECREAM_VENDOR: AccountAddress = AccountAddress([1; 32]);
    const ICECREAM_PRICE: Amount = Amount {
        micro_ccd: 6000000, // 6 CCD
    };

    #[concordium_test]
    fn test_sunny_days() {
        // Arrange
        let mut ctx = ReceiveContextTest::empty();
        let mut ops = ExternOperationsTest::<State>::empty();

        // Set up context
        let parameter = to_bytes(&ICECREAM_VENDOR);
        ctx.set_owner(OWNER_ADDR);
        ctx.set_self_address(SELF_ADDR);
        ctx.set_parameter(&parameter);
        ops.set_balance(ICECREAM_PRICE);

        let mut state = State {
            weather_service: WEATHER_SERVICE,
        };

        // Set up mock invocation
        ops.setup_mock_invocation(
            state.weather_service,
            OwnedEntrypointName::new_unchecked("get".into()),
            Handler::new(MockFn::new(|_parameter, _amount, _state| Ok((false, Weather::Sunny)))),
        );

        // Act
        contract_buy_icecream(&ctx, &mut ops, ICECREAM_PRICE, &mut state)
            .expect_report("Calling buy_icecream failed.");

        // Assert
        assert!(ops.transfer_occurred(&ICECREAM_VENDOR, ICECREAM_PRICE));
    }

    #[concordium_test]
    fn test_rainy_days() {
        // Arrange
        let mut ctx = ReceiveContextTest::empty();
        let mut ops = ExternOperationsTest::<State>::empty();

        // Set up context
        let parameter = to_bytes(&ICECREAM_VENDOR);
        ctx.set_owner(OWNER_ADDR);
        ctx.set_self_address(SELF_ADDR);
        ctx.set_parameter(&parameter);
        ops.set_balance(ICECREAM_PRICE);

        let mut state = State {
            weather_service: WEATHER_SERVICE,
        };

        // Set up mock invocation
        ops.setup_mock_invocation(
            state.weather_service,
            OwnedEntrypointName::new_unchecked("get".into()),
            Handler::new(MockFn::new(|_parameter, _amount, _state| Ok((false, Weather::Rainy)))),
        );

        // Act
        contract_buy_icecream(&ctx, &mut ops, ICECREAM_PRICE, &mut state)
            .expect_report("Calling buy_icecream failed.");

        // Assert
        assert!(ops.transfer_occurred(&OWNER_ADDR, ICECREAM_PRICE));
    }
}
