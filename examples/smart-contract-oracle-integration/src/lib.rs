//! # Implementation of an auction smart contract
//!
//! Accounts can invoke the bid function to participate in the auction.
//! An account has to send some CCD when invoking the bid function.
//! This CCD amount has to exceed the current highest bid by a minimum raise
//! to be accepted by the smart contract.
//!
//! The minimum raise is set when initializing and is defined in Euro cent.
//! The contract uses the current exchange rate used by the chain by the time of
//! the bid, to convert the bid into EUR.
//!
//! The smart contract keeps track of the current highest bidder as well as
//! the CCD amount of the highest bid. The CCD balance of the smart contract
//! represents the highest bid. When a new highest bid is accepted by the smart
//! contract, the smart contract refunds the old highest bidder.
//!
//! Bids have to be placed before the auction ends. The participant with the
//! highest bid (the last bidder) wins the auction.
//!
//! After the auction ends, any account can finalize the auction. The owner of
//! the smart contract instance receives the highest bid (the balance of this
//! contract) when the auction is finalized. This can be done only once.
//!
//! Terminology: `Accounts` are derived from a public/private key pair.
//! `Contract` instances are created by deploying a smart contract
//! module and initializing it.

#![cfg_attr(not(feature = "std"), no_std)]

use concordium_std::*;

const UMBRELLA_REGISTRY_CONTRACT: ContractAddress = ContractAddress {
    index:    7542,
    subindex: 0,
};

#[derive(Serialize, SchemaType, PartialEq, Eq)]
pub struct Prices {
    pub prices: Vec<(String, u64)>,
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
    last_price_update:          StateMap<String, u64, S>,
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
    return_value = "Vec<(String, u64)>"
)]
fn prices(_ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<Vec<(String, u64)>> {
    let prices: Vec<(String, u64)> =
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

    // let umbrella_feeds_contract: ContractAddress =
    //     if let Some(mut umbrella_feeds_contract) = umbrella_feeds_contract {
    //         umbrella_feeds_contract.get()?
    //     } else {
    //         return Err(CustomContractError::InvokeContractError);
    //     };

    // let price = host.invoke_contract_read_only(
    //     &umbrella_feeds_contract,
    //     &price_feed_name,
    //     EntrypointName::new_unchecked("getPriceData"),
    //     Amount::zero(),
    // )?;

    // let price: u64 = if let Some(mut price) = price {
    //     price.get()?
    // } else {
    //     return Err(CustomContractError::InvokeContractError);
    // };

    // host.state_mut().last_price_update.insert(price_feed_name, price);

    Ok(())
}
