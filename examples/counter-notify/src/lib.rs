#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;

type State = u64;

#[init(contract = "counter-notify")]
#[inline(always)]
fn contract_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<State> {
    Ok(0u64)
}

#[receive(contract = "counter-notify", name = "just-increment", mutable)]
fn just_increment<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> ReceiveResult<()> {
    *host.state_mut() += 1;
    Ok(())
}

#[receive(contract = "counter-notify", name = "increment-and-notify", mutable)]
fn increment_and_notify<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> ReceiveResult<bool> {
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

    // This will be false if the reentrancy has occurred.
    Ok(preinvoke_count == *host.state())
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use concordium_std::claim_eq;
    use test_infrastructure::*;

    #[concordium_test]
    fn state_can_change_due_to_reentrancy() {
        let mut ctx = TestReceiveContext::empty();
        let self_address = ContractAddress {
            index:    0,
            subindex: 0,
        };
        let entrypoint_just_increment = OwnedEntrypointName::new_unchecked("just-increment".into());
        let parameter_bytes = to_bytes(&(self_address, entrypoint_just_increment.clone()));
        ctx.set_parameter(&parameter_bytes);
        ctx.set_self_address(self_address);

        let mut host = TestHost::new(0u64, TestStateBuilder::new());

        // We are simulating reentrancy with this mock because we mutate the state.
        host.setup_mock_entrypoint(
            self_address,
            entrypoint_just_increment,
            MockFn::new_v1(|_parameter, _amount, _balance, state: &mut State| {
                *state += 1;
                Ok((true, ()))
            }),
        );

        let res = increment_and_notify(&ctx, &mut host).expect_report("Calling receive failed.");

        // The count
        claim_eq!(res, false);
    }
}
