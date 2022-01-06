use concordium_std::*;

#[contract_state(contract = "fib")]
#[derive(Serialize, SchemaType)]
pub struct State {
    result: u64,
}

#[init(contract = "fib")]
#[inline(always)]
fn contract_init(_ctx: &impl HasInitContext) -> InitResult<((), State)> {
    let state = State {
        result: 0,
    };
    Ok(((), state))
}

// 4
// - f(3)
//   - f(2)
//     - f(1) => + 1
//     - f(0) => + 1
//   - f(1) => + 1
// - f(2)
//   - f(1) => + 1
//   - f(0) => + 1
//

// Add the nth Fibonacci number F(n) to this contract's state.
// This is achieved by recursively sending messages to this receive method,
// corresponding to the recursive evaluation F(n) = F(n-1) + F(n-2) (for n>1).
#[inline(always)]
#[receive(contract = "fib", name = "receive")]
fn contract_receive(
    ctx: &impl HasReceiveContext,
    ops: &mut impl HasOperations<State>,
    state: &mut State,
) -> ReceiveResult<u64> {
    // Try to get the parameter (64bit unsigned integer).
    let n: u64 = ctx.parameter_cursor().get()?;
    if n <= 1 {
        state.result += 1;
        Ok(state.result)
    } else {
        let self_address = ctx.self_address();
        ops.invoke_contract(
            state,
            &self_address,
            Parameter(&(n - 1).to_le_bytes()),
            EntrypointName::new("receive").unwrap(),
            Amount::zero(),
        )
        .unwrap_abort();
        ops.invoke_contract(
            state,
            &self_address,
            Parameter(&(n - 2).to_le_bytes()),
            EntrypointName::new("receive").unwrap(),
            Amount::zero(),
        )
        .unwrap_abort();

        Ok(state.result)
    }
}

// Calculates the nth Fibonacci number where n is the given amount and sets the
// state to that number.
#[inline(always)]
#[receive(contract = "fib", name = "receive_calc_fib", payable)]
fn contract_receive_calc_fib(
    _ctx: &impl HasReceiveContext<()>,
    _ops: &mut impl HasOperations<State>,
    amount: Amount,
    state: &mut State,
) -> ReceiveResult<()> {
    state.result = fib(amount.micro_ccd);
    Ok(())
}

// Recursively and naively calculate the nth Fibonacci number.
fn fib(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        fib(n - 1) + fib(n - 2)
    }
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;
    #[concordium_test]
    fn calc_fib_works() {
        let ctx = ReceiveContextTest::empty();
        let mut ops = ExternOperationsTest::empty();
        let mut state = State {
            result: 0,
        };
        let amount = Amount::from_micro_ccd(7);

        contract_receive_calc_fib(&ctx, &mut ops, amount, &mut state)
            .expect_report("Calling receive failed.");

        assert_eq!(state.result, 21);
    }

    #[concordium_test]
    fn receive_works() {
        let mut ctx = ReceiveContextTest::empty();
        let parameter_bytes = to_bytes(&4u64);
        let contract_address = ContractAddress {
            index:    0,
            subindex: 0,
        };
        ctx.set_parameter(&parameter_bytes);
        ctx.set_self_address(contract_address.clone());

        let mut state = State {
            result: 0,
        };
        let mut ops = ExternOperationsTest::<State>::empty();

        ops.setup_mock_invocation(
            contract_address,
            OwnedEntrypointName::new(String::from("receive")).unwrap_abort(),
            MockFn::new(|parameter, _amount, state| {
                let n: u64 = match from_bytes(parameter.0) {
                    Ok(n) => n,
                    Err(_) => return Err(InvokeError::Trap),
                };
                match n {
                    3 => state.result += 3,
                    2 => state.result += 2,
                    _ => return Err(InvokeError::Trap),
                }
                Ok(state.result)
            }),
        );

        contract_receive(&ctx, &mut ops, &mut state).expect_report("Calling receive failed.");

        assert_eq!(state.result, 5);
    }
}
