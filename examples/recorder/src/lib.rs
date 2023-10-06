#![cfg_attr(not(feature = "std"), no_std)]

//! A simple contract that records account addresses, and has
//! an entrypoint to invoke transfers to all those addresses.
//! The contract maintains a list of addresses. Addresses may be added with the
//! "record" entrypoint, and removed with "delete" entrypoint.
//!
//! There is a "transfer" entrypoint that will trigger a transfer to all the
//! current addresses, of 0CCD. After all the transfers the addresses are
//! deleted from the state.
//!
//! This contract tests a reasonably small example of state interactions.
//!
//! Tests are located in the `./tests` folder.
use concordium_std::*;

#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S = StateApi> {
    addresses: StateSet<AccountAddress, S>,
}

#[init(contract = "recorder")]
fn init(_ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<State> {
    Ok(State {
        addresses: state_builder.new_set(),
    })
}

#[receive(contract = "recorder", name = "record", parameter = "AccountAddress", mutable)]
fn receive_record(ctx: &ReceiveContext, host: &mut Host<State>) -> ReceiveResult<()> {
    let address: AccountAddress = ctx.parameter_cursor().get()?;

    host.state_mut().addresses.insert(address);
    Ok(())
}

#[receive(
    contract = "recorder",
    name = "delete",
    parameter = "AccountAddress",
    return_value = "bool",
    mutable
)]
fn receive_delete(ctx: &ReceiveContext, host: &mut Host<State>) -> ReceiveResult<bool> {
    let addr_to_remove = ctx.parameter_cursor().get()?;
    let res = host.state_mut().addresses.remove(&addr_to_remove);
    Ok(res)
}

#[receive(contract = "recorder", name = "transfer", return_value = "u64", mutable)]
fn receive_transfer(_ctx: &ReceiveContext, host: &mut Host<State>) -> ReceiveResult<u64> {
    let addresses = &host.state().addresses;
    let mut count = 0;
    for addr in addresses.iter() {
        if host.invoke_transfer(&addr, Amount::from_micro_ccd(0)).is_ok() {
            count += 1;
        }
    }
    host.state_mut().addresses.clear();
    Ok(count)
}

#[receive(contract = "recorder", name = "list", return_value = "Vec<AccountAddress>")]
fn receive_list(_ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<Vec<AccountAddress>> {
    let mut ret: Vec<AccountAddress> = Vec::new();
    for addr in host.state().addresses.iter() {
        ret.push(*addr);
    }
    Ok(ret)
}
