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

#[derive(Serialize, SchemaType)]
struct State {
    weather_service: ContractAddress,
}

#[derive(Serialize, SchemaType, Clone, Copy)]
enum Weather {
    Rainy,
    Sunny,
}

/// Initialise the contract with the contract address of the weather service.
#[init(contract = "icecream", parameter = "ContractAddress")]
fn contract_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<State> {
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
    mutable
)]
fn contract_buy_icecream<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
    amount: Amount,
) -> ReceiveResult<()> {
    let weather_service = host.state().weather_service;
    let icecream_vendor: AccountAddress = ctx.parameter_cursor().get()?;

    let weather = host
        .invoke_contract_raw(
            &weather_service,
            Parameter(&[]),
            EntrypointName::new_unchecked("get"),
            Amount::zero(),
        )
        .expect_report("Invoking weather contract failed.")
        .1
        .expect_report("Invocation did not return a value.")
        .get()?;

    match weather {
        Weather::Rainy => {
            host.invoke_transfer(&ctx.invoker(), amount).expect("Returning CCD to invoker failed.")
            // We could also abort here, but this is useful to show off some
            // testing features.
        }
        Weather::Sunny => host
            .invoke_transfer(&icecream_vendor, amount)
            .expect_report("Sending CCD to the icecream vendor failed."),
    }
    Ok(())
}

/// Replace the weather service with another.
/// Only the owner of the contract can do so.
#[receive(
    contract = "icecream",
    name = "replace_weather_service",
    parameter = "ContractAddress",
    mutable
)]
fn contract_replace_weather_service<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> ReceiveResult<()> {
    assert_eq!(Address::Account(ctx.owner()), ctx.sender());
    let new_weather_service: ContractAddress = ctx.parameter_cursor().get()?;
    host.state_mut().weather_service = new_weather_service;
    Ok(())
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/// Initialse the weather service with the weather.
#[init(contract = "weather", parameter = "Weather")]
fn weather_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<Weather> {
    let weather = ctx.parameter_cursor().get()?;
    Ok(weather)
}

/// Get the current weather.
#[receive(contract = "weather", name = "get", return_value = "Weather")]
fn weather_get<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<Weather, StateApiType = S>,
) -> ReceiveResult<Weather> {
    Ok(*host.state())
}

/// Update the weather.
#[receive(contract = "weather", name = "set", parameter = "Weather", mutable)]
fn weather_set<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<Weather, StateApiType = S>,
) -> ReceiveResult<()> {
    assert_eq!(Address::Account(ctx.owner()), ctx.sender()); // Only the owner can update the weather.
    *host.state_mut() = ctx.parameter_cursor().get()?;
    Ok(())
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    const INVOKER_ADDR: AccountAddress = AccountAddress([0; 32]);
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
        let mut ctx = TestReceiveContext::empty();
        let state = State {
            weather_service: WEATHER_SERVICE,
        };
        let mut host = TestHost::new(state, TestStateBuilder::new());

        // Set up context
        let parameter = to_bytes(&ICECREAM_VENDOR);
        ctx.set_owner(INVOKER_ADDR);
        ctx.set_invoker(INVOKER_ADDR);
        ctx.set_parameter(&parameter);
        host.set_self_balance(ICECREAM_PRICE); // This should be the balance prior to the call plus the incoming amount.

        // Set up a mock invocation for the weather service.
        host.setup_mock_entrypoint(
            WEATHER_SERVICE,
            OwnedEntrypointName::new_unchecked("get".into()),
            MockFn::returning_ok(Weather::Sunny),
        );

        // Act
        contract_buy_icecream(&ctx, &mut host, ICECREAM_PRICE)
            .expect_report("Calling buy_icecream failed.");

        // Assert
        assert!(host.transfer_occurred(&ICECREAM_VENDOR, ICECREAM_PRICE));
        assert!(host.get_transfers_to(INVOKER_ADDR).is_empty()); // Check that
                                                                 // no
                                                                 // transfers to
                                                                 // the invoker
                                                                 // occured.
    }

    #[concordium_test]
    fn test_rainy_days() {
        // Arrange
        let mut ctx = TestReceiveContext::empty();
        let state = State {
            weather_service: WEATHER_SERVICE,
        };
        let mut host = TestHost::new(state, TestStateBuilder::new());

        // Set up context
        let parameter = to_bytes(&ICECREAM_VENDOR);
        ctx.set_owner(INVOKER_ADDR);
        ctx.set_invoker(INVOKER_ADDR);
        ctx.set_parameter(&parameter);
        host.set_self_balance(ICECREAM_PRICE);

        // Set up mock invocation
        host.setup_mock_entrypoint(
            WEATHER_SERVICE,
            OwnedEntrypointName::new_unchecked("get".into()),
            MockFn::returning_ok(Weather::Rainy),
        );

        // Act
        contract_buy_icecream(&ctx, &mut host, ICECREAM_PRICE)
            .expect_report("Calling buy_icecream failed.");

        // Assert
        assert!(host.transfer_occurred(&INVOKER_ADDR, ICECREAM_PRICE));
        assert_eq!(host.get_transfers(), &[(INVOKER_ADDR, ICECREAM_PRICE)]); // Check that this is the only transfer.
    }

    // TODO: Use a custom error type and check the result instead of using panics,
    // because they can't be caught in wasm (i.e. with cargo concordium test).
    #[concordium_test]
    #[should_panic(expected = "Sending CCD to the icecream vendor failed.: MissingAccount")]
    fn test_missing_icecream_vendor() {
        // Arrange
        let mut ctx = TestReceiveContext::empty();
        let state = State {
            weather_service: WEATHER_SERVICE,
        };
        let mut host = TestHost::new(state, TestStateBuilder::new());

        // Set up context
        let parameter = to_bytes(&ICECREAM_VENDOR);
        ctx.set_owner(INVOKER_ADDR);
        ctx.set_invoker(INVOKER_ADDR);
        ctx.set_parameter(&parameter);
        host.set_self_balance(ICECREAM_PRICE);

        // By default all transfers to accounts will work, but here we want to test what
        // happens when the vendor account doesn't exist.
        host.make_account_missing(ICECREAM_VENDOR);

        // Set up mock invocation
        host.setup_mock_entrypoint(
            WEATHER_SERVICE,
            OwnedEntrypointName::new_unchecked("get".into()),
            MockFn::returning_ok(Weather::Sunny),
        );

        // Act + Assert (should panic)
        contract_buy_icecream(&ctx, &mut host, ICECREAM_PRICE).unwrap();
    }

    // TODO: Use a custom error type and check the result instead of using panics,
    // because they can't be caught in wasm (i.e. with cargo concordium test).
    #[concordium_test]
    #[should_panic(expected = "Invoking weather contract failed.: MissingContract")]
    fn test_missing_weather_service() {
        // Arrange
        let mut ctx = TestReceiveContext::empty();
        let state = State {
            weather_service: WEATHER_SERVICE,
        };
        let mut host = TestHost::new(state, TestStateBuilder::new());

        // Set up context
        let parameter = to_bytes(&ICECREAM_VENDOR);
        ctx.set_owner(INVOKER_ADDR);
        ctx.set_parameter(&parameter);

        // Set up mock invocation
        host.setup_mock_entrypoint(
            WEATHER_SERVICE,
            OwnedEntrypointName::new_unchecked("get".into()),
            MockFn::returning_err::<()>(CallContractError::MissingContract),
        );

        // Act + Assert (should panic)
        contract_buy_icecream(&ctx, &mut host, ICECREAM_PRICE)
            .expect_report("Calling buy_icecream failed.");
    }
}
