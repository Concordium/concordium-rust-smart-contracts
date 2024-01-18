//! # Example contract that gets price feed data from the umbrella oracle protocol.
#![cfg_attr(not(feature = "std"), no_std)]

use concordium_std::*;

/// Registry contract address in the integration test cases.
#[cfg(not(any(feature = "mainnet", feature = "testnet")))]
const UMBRELLA_REGISTRY_CONTRACT: ContractAddress = ContractAddress {
    index:    1,
    subindex: 0,
};

/// Attention: The umbrella oracle is not deployed on mainnet at the time of
/// writing. https://umbrella-network.readme.io/docs/concordium-integration-examples
#[cfg(feature = "mainnet")]
const UMBRELLA_REGISTRY_CONTRACT: ContractAddress = ContractAddress {
    index:    0,
    subindex: 0,
};

/// Registry contract address on Concordium testnet.
#[cfg(feature = "testnet")]
const UMBRELLA_REGISTRY_CONTRACT: ContractAddress = ContractAddress {
    index:    7542,
    subindex: 0,
};

/// The return_parameter of the contract function `getPriceData` from the
/// Umbrella oracle protocol.
#[derive(Serialize, SchemaType, Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq)]
pub struct PriceData {
    /// This is a placeholder, that can be used for some additional data.
    pub data:      u8,
    /// The heartbeat specifies the interval in seconds that the price data will
    /// be refreshed in case the price stays flat.
    pub heartbeat: u64,
    /// It is the time the validators run consensus to decide on the price data.
    pub timestamp: Timestamp,
    /// The relative price.
    pub price:     u128,
}

/// The return_parameter of the contract function `prices`.
#[derive(Serialize, SchemaType, PartialEq, Eq)]
pub struct Prices {
    /// A vector including for each price feed name its corresponding price as
    /// stored in the contract state.
    pub prices: Vec<(String, u128)>,
}

/// The state of the smart contract.
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S = StateApi> {
    /// Map storing for each price feed name (such as `ETH-USDC`) its
    /// corresponding price. A price was last updated whenever the
    /// `update_price` function was invoked with the given price feed name.
    last_price_update: StateMap<String, u128, S>,
}

/// Errors
#[derive(Debug, PartialEq, Eq, Clone, Reject, Serialize, SchemaType)]
pub enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams, // -1
    /// Failed updating the price because the price fetched from the oracle is
    /// not up to date.
    PriceNotUpToDate, // -2
    /// Failed to invoke a contract.
    InvokeContractError, // -3
    /// Failed because the timestamp overflowed.
    Overflow, // -4
}

/// Mapping errors related to contract invocations to CustomContractError.
impl<T> From<CallContractError<T>> for CustomContractError {
    fn from(_cce: CallContractError<T>) -> Self { Self::InvokeContractError }
}

/// Init function that creates a new contract.
#[init(contract = "smart_contract_oracle_integration")]
fn init(_ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<State> {
    Ok(State {
        last_price_update: state_builder.new_map(),
    })
}

/// View function that returns the content of the state.
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

/// Receive function to update the prices in the contract state.
#[receive(
    contract = "smart_contract_oracle_integration",
    name = "update_price",
    parameter = "String",
    error = "CustomContractError",
    mutable
)]
fn update_price(ctx: &ReceiveContext, host: &mut Host<State>) -> Result<(), CustomContractError> {
    let umbrella_feeds_contract = host.invoke_contract_read_only(
        &UMBRELLA_REGISTRY_CONTRACT,
        &String::from("UmbrellaFeeds"),
        EntrypointName::new_unchecked("getAddress"),
        Amount::zero(),
    )?;

    let umbrella_feeds_contract: ContractAddress =
        if let Some(mut umbrella_feeds_contract) = umbrella_feeds_contract {
            umbrella_feeds_contract.get()?
        } else {
            return Err(CustomContractError::InvokeContractError);
        };

    let price_feed_name: String = ctx.parameter_cursor().get()?;

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
        CustomContractError::PriceNotUpToDate
    );

    host.state_mut().last_price_update.insert(price_feed_name, price_data.price);

    Ok(())
}
