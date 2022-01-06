#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;

#[contract_state(contract = "fib")]
#[derive(Serialize, SchemaType)]
pub struct State {
    result: u64,
}

#[init(contract = "fib")]
#[inline(always)]
fn contract_init(_ctx: &impl HasInitContext<()>) -> InitResult<((), State)> {
    let state = State {
        result: 0,
    };
    Ok(((), state))
}

// Add the the nth Fibonacci number F(n) to this contract's state.
// This is achieved by recursively calling the contract itself.
#[inline(always)]
#[receive(contract = "fib", name = "receive", low_level)]
fn contract_receive(
    ctx: &impl HasReceiveContext<()>,
    ops: &mut impl HasOperations<ContractState>,
    state: &mut ContractState,
) -> ReceiveResult<u64> {
    // Try to get the parameter (64bit unsigned integer).
    let n: u64 = ctx.parameter_cursor().get()?;
    if n <= 1 {
        state.seek(SeekFrom::Start(0))?;
        1u64.serial(state)?;
        Ok(1)
    } else {
        let self_address = ctx.self_address();
        let p2 = (n - 2).to_le_bytes();
        let mut n2 = ops
            .invoke_contract(
                state,
                &self_address,
                Parameter(&p2),
                EntrypointName::new_unchecked("receive"),
                Amount::zero(),
            )
            .unwrap_abort()
            .unwrap_abort();
        state.seek(SeekFrom::Start(0))?;
        let cv2: u64 = state.get()?;
        let n2: u64 = n2.get().unwrap_abort();
        ensure_eq!(cv2, n2);

        let p1 = (n - 1).to_le_bytes();
        let mut n1 = ops
            .invoke_contract(
                state,
                &self_address,
                Parameter(&p1),
                EntrypointName::new_unchecked("receive"),
                Amount::zero(),
            )
            .unwrap_abort()
            .unwrap_abort();
        state.seek(SeekFrom::Start(0))?;
        let cv1: u64 = state.get()?;
        let n1: u64 = n1.get().unwrap_abort();
        ensure_eq!(cv1, n1);
        state.seek(SeekFrom::Start(0))?;
        (cv1 + cv2).serial(state)?;
        Ok(cv1 + cv2)
    }
}

/// Retrieve the value of the state.
#[inline(always)]
#[receive(contract = "fib", name = "view")]
fn contract_view(
    _ctx: &impl HasReceiveContext<()>,
    _ops: &mut impl HasOperations<State>,
    state: &mut State,
) -> ReceiveResult<u64> {
    Ok(state.result)
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

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
        // TODO
        // contract_receive(&ctx, &mut ops, &mut state).expect_report("Calling receive
        // failed.");

        assert_eq!(state.result, 5);
    }
}
