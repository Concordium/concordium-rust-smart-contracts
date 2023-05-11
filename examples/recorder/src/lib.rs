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
use concordium_std::*;

#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S> {
    addresses: StateSet<AccountAddress, S>,
}

#[init(contract = "recorder")]
fn init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    Ok(State {
        addresses: state_builder.new_set(),
    })
}

#[receive(contract = "recorder", name = "record", parameter = "AccountAddress", mutable)]
fn receive_record<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<()> {
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
fn receive_delete<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<bool> {
    let addr_to_remove = ctx.parameter_cursor().get()?;
    let res = host.state_mut().addresses.remove(&addr_to_remove);
    Ok(res)
}

#[receive(contract = "recorder", name = "transfer", return_value = "u64", mutable)]
fn receive_transfer<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<u64> {
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
fn receive_list<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<Vec<AccountAddress>> {
    let mut ret: Vec<AccountAddress> = Vec::new();
    for addr in host.state().addresses.iter() {
        ret.push(*addr);
    }
    Ok(ret)
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    #[concordium_test]
    fn test_init() {
        let ctx = TestInitContext::empty();

        let mut state_builder = TestStateBuilder::new();

        let _ = init(&ctx, &mut state_builder).expect_report("Init failed");
    }

    #[concordium_test]
    fn test_receive() {
        let state_api = TestStateApi::new();
        let mut state_builder = TestStateBuilder::open(state_api);

        // Set up initial state contents via init.
        let initial_state =
            init(&TestInitContext::empty(), &mut state_builder).expect_report("Init failed");

        let mut host = TestHost::new(initial_state, state_builder);

        let mut ctx = TestReceiveContext::empty();

        let addr0 = AccountAddress([0u8; 32]);
        ctx.set_parameter(addr0.as_ref());
        receive_record(&ctx, &mut host).expect_report("Recording failed.");

        let addr1 = AccountAddress([1u8; 32]);
        ctx.set_parameter(addr1.as_ref());
        receive_record(&ctx, &mut host).expect_report("Recording failed.");

        let list =
            receive_list(&TestReceiveContext::empty(), &host).expect_report("Listing failed.");
        claim_eq!(&list[..], &[addr0, addr1][..], "Contract has incorrect addresses.");

        let n = receive_transfer(&TestReceiveContext::empty(), &mut host)
            .expect_report("Transfer failed.");
        claim_eq!(n, 2, "Incorrect number of transfers.");
        let transfers_occurred = host.get_transfers();
        claim_eq!(
            &transfers_occurred[..],
            &[(addr0, Amount::from_micro_ccd(0)), (addr1, Amount::from_micro_ccd(0))][..]
        );

        // now the contract state should be empty
        let list =
            receive_list(&TestReceiveContext::empty(), &host).expect_report("Listing failed.");
        claim_eq!(&list[..], &[][..], "Contract should have no addresses.");
    }
}
