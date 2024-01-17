//! # Example contract that gets price feed data from the umbrella oracle protocol.
#![cfg_attr(not(feature = "std"), no_std)]

use concordium_std::*;

#[cfg(test)]
const UMBRELLA_REGISTRY_CONTRACT: ContractAddress = ContractAddress {
    index:    7542,
    subindex: 0,
};

#[cfg(not(test))]
const UMBRELLA_REGISTRY_CONTRACT: ContractAddress = ContractAddress {
    index:    1,
    subindex: 0,
};

#[derive(Serialize, SchemaType, Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq)]
pub struct PriceData {
    /// This is a placeholder, that can be used for some additional data.
    pub data:      u8,
    /// The heartbeat specifies the interval in seconds that the price data will
    /// be refreshed in case the price stays flat. ATTENTION: u64 is used
    /// here instead of u24 (different from the original solidity smart
    /// contracts).
    pub heartbeat: u64,
    /// It is the time the validators run consensus to decide on the price data.
    pub timestamp: Timestamp,
    /// The relative price.
    pub price:     u128,
}

#[derive(Serialize, SchemaType, PartialEq, Eq)]
pub struct Prices {
    pub prices: Vec<(String, u128)>,
}

/// The state of the smart contract.
/// This state can be viewed by querying the node with the command
/// `concordium-client contract invoke` using the `view` function as entrypoint.
// #[derive(Debug, Serialize, SchemaType, Clone)]
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S = StateApi> {
    ///
    umbrella_registry_contract: ContractAddress,
    ///
    last_price_update:          StateMap<String, u128, S>,
}

/// Errors
#[derive(Debug, PartialEq, Eq, Clone, Reject, Serialize, SchemaType)]
pub enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams, // -1
    ///
    PriceNotUpToDate, // -2
    /// Failed to invoke a contract.
    InvokeContractError, // -3
    /// Timestamp overflow
    Overflow, // -4
}

/// Mapping errors related to contract invocations to CustomContractError.
impl<T> From<CallContractError<T>> for CustomContractError {
    fn from(_cce: CallContractError<T>) -> Self { Self::InvokeContractError }
}

/// Init function that creates a new auction
#[init(contract = "smart_contract_oracle_integration")]
fn init(_ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<State> {
    Ok(State {
        umbrella_registry_contract: UMBRELLA_REGISTRY_CONTRACT,
        last_price_update:          state_builder.new_map(),
    })
}

/// View function that returns the content of the state
#[receive(
    contract = "smart_contract_oracle_integration",
    name = "prices",
    return_value = "Vec<(String, u128)>"
)]
fn prices(_ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<Vec<(String, u128)>> {
    let prices: Vec<(String, u128)> =
        host.state().last_price_update.iter().map(|(a, b)| ((*a).clone(), *b)).collect();
    Ok(prices)
}

/// Receive function used to finalize the auction. It sends the highest bid (the
/// current balance of this smart contract) to the owner of the smart contract
/// instance.
#[receive(
    contract = "smart_contract_oracle_integration",
    name = "update_price",
    parameter = "String",
    error = "CustomContractError",
    mutable
)]
fn update_price(ctx: &ReceiveContext, host: &mut Host<State>) -> Result<(), CustomContractError> {
    let price_feed_name: String = ctx.parameter_cursor().get()?;

    let umbrella_registry_contract = host.state.umbrella_registry_contract;

    let parameter = String::from("UmbrellaFeeds");

    let umbrella_feeds_contract = host.invoke_contract_read_only(
        &umbrella_registry_contract,
        &parameter,
        EntrypointName::new_unchecked("getAddress"),
        Amount::zero(),
    )?;

    let umbrella_feeds_contract: ContractAddress =
        if let Some(mut umbrella_feeds_contract) = umbrella_feeds_contract {
            umbrella_feeds_contract.get()?
        } else {
            return Err(CustomContractError::InvokeContractError);
        };

    let price = host.invoke_contract_read_only(
        &umbrella_feeds_contract,
        &price_feed_name,
        EntrypointName::new_unchecked("getPriceData"),
        Amount::zero(),
    )?;

    let price_data: PriceData = if let Some(mut price) = price {
        price.get()?
    } else {
        return Err(CustomContractError::InvokeContractError);
    };

    // Check price feed is not outdated.
    ensure!(
        ctx.metadata().block_time()
            < price_data
                .timestamp
                .checked_add(Duration::from_seconds(price_data.heartbeat))
                .ok_or(CustomContractError::Overflow)?,
        CustomContractError::PriceNotUpToDate.into()
    );

    host.state_mut().last_price_update.insert(price_feed_name, price_data.price);

    Ok(())
}
