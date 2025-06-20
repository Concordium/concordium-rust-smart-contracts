//! An example of reentrancy attacks.
//!
//! Consists of two contracts:
//!  - `counter-notify`
//!    - A counter contract that also notifies some contract about increments.
//!    - After the notification call it checks to see that its counter hasn't
//!      been altered.
//!  - `reentrancy-attacker`
//!    - A contract that tries to make an reentrancy attack on the
//!      `counter-notify` contract.
#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;

type State = u64;

#[derive(SchemaType, Serial, Deserial, PartialEq)]
pub enum ReentryOccurance {
    NoReentryAttack,
    ReentryAttack,
}

#[init(contract = "counter-notify")]
#[inline(always)]
fn contract_init(_ctx: &InitContext, _state_builder: &mut StateBuilder) -> InitResult<State> {
    Ok(0u64)
}

#[receive(contract = "counter-notify", name = "just-increment", mutable)]
fn just_increment(_ctx: &ReceiveContext, host: &mut Host<State>) -> ReceiveResult<()> {
    *host.state_mut() += 1;
    Ok(())
}

#[receive(
    contract = "counter-notify",
    name = "increment-and-notify",
    mutable,
    parameter = "(ContractAddress, OwnedEntrypointName)",
    return_value = "ReentryOccurance"
)]
fn increment_and_notify(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
) -> ReceiveResult<ReentryOccurance> {
    let (contract, entrypoint): (ContractAddress, OwnedEntrypointName) =
        ctx.parameter_cursor().get()?;

    // Increment counter
    *host.state_mut() += 1;
    let preinvoke_count = *host.state();

    // Notify a contract about the new counter value.
    host.invoke_contract(
        &contract,
        &preinvoke_count,
        entrypoint.as_entrypoint_name(),
        Amount::zero(),
    )
    .unwrap_abort();

    let is_reentry = if preinvoke_count != *host.state() {
        ReentryOccurance::ReentryAttack
    } else {
        ReentryOccurance::NoReentryAttack
    };

    Ok(is_reentry)
}

////////////////////////////////////////////////////////////////////////////////////////////////

#[init(contract = "reentrancy-attacker")]
fn reentrancy_init(_ctx: &InitContext, _state_builder: &mut StateBuilder) -> InitResult<()> {
    Ok(())
}

/// Tries to call the entrypoint `just-increment` on the sender iff it is a
/// contract. Fails if the sender is an account or the `just-increment` call
/// fails.
#[receive(contract = "reentrancy-attacker", name = "call-just-increment", mutable)]
fn reentrancy_receive(ctx: &ReceiveContext, host: &mut Host<()>) -> ReceiveResult<()> {
    match ctx.sender() {
        Address::Account(_) => fail!(),
        Address::Contract(contract) => {
            host.invoke_contract(
                &contract,
                &(),
                EntrypointName::new_unchecked("just-increment"),
                Amount::zero(),
            )
            .unwrap();
            Ok(())
        }
    }
}
