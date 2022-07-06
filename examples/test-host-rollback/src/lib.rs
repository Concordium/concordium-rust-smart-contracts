use concordium_std::*;

#[derive(Reject, PartialEq, Eq, Debug)]
enum ContractError {
    Error,
    ParseError,
}

impl From<ParseError> for ContractError {
    fn from(_: ParseError) -> Self { ContractError::ParseError }
}

type State = u32;

#[init(contract = "test-host-rollback")]
fn init<S: HasStateApi>(
    _: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<State> {
    Ok(0)
}

#[receive(mutable, contract = "test-host-rollback", name = "update")]
fn contract_update<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<(), ContractError> {
    // Always increment state.
    *host.state_mut() += 1;

    let invoke_and_succeed = ctx.parameter_cursor().get()?;

    if invoke_and_succeed {
        let _res = host.invoke_contract(
            &ctx.self_address(),
            &false,
            EntrypointName::new_unchecked("update"),
            Amount::zero(),
        );
        Ok(())
    } else {
        Err(ContractError::Error)
    }
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use concordium_std::test_infrastructure::*;

    #[concordium_test]
    fn test_increment_and_fail() {
        let ctx_init = TestInitContext::empty();
        let mut state_builder = TestStateBuilder::new();
        let state = init(&ctx_init, &mut state_builder).expect_report("Failed to initialize");
        let mut host = TestHost::new(state, state_builder);

        claim_eq!(*host.state(), 0);

        let mut ctx_rcv = TestReceiveContext::default();
        let parameter = to_bytes(&false);
        ctx_rcv.set_parameter(&parameter); // Don't invoke, just increment and then return Err.

        // Call update function.
        let result = with_rollback(|host| contract_update(&ctx_rcv, host), &mut host);
        claim_eq!(result, Err(ContractError::Error));

        // The state should be 0, as the update failed.
        claim_eq!(*host.state(), 0);
    }

    #[concordium_test]
    fn test_increment_invoke_and_succeed() {
        let ctx_init = TestInitContext::empty();
        let mut state_builder = TestStateBuilder::new();
        let state = init(&ctx_init, &mut state_builder).expect_report("Failed to initialize");
        let mut host = TestHost::new(state, state_builder);

        claim_eq!(*host.state(), 0);

        let mut ctx_rcv = TestReceiveContext::default();
        let parameter = to_bytes(&true);
        ctx_rcv.set_parameter(&parameter); // Invoke and then return success.
        let self_address = ContractAddress {
            index:    0,
            subindex: 0,
        };
        ctx_rcv.set_self_address(self_address);

        host.setup_mock_entrypoint(
            self_address,
            OwnedEntrypointName::new_unchecked("update".to_string()),
            MockFn::new_v1::<(), _>(|_, _, _, state: &mut State| {
                *state += 1;
                Err(CallContractError::Trap)
            }),
        );

        // Call update function.
        let result = with_rollback(|host| contract_update(&ctx_rcv, host), &mut host);
        claim_eq!(result, Ok(()));

        // The state should be 1, as the outer receive worked, but the inner invoke
        // failed.
        claim_eq!(*host.state(), 1);
    }
}
