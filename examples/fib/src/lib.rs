#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;

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

// Add the the nth Fibonacci number F(n) to this contract's state.
// This is achieved by recursively calling the contract itself.
#[inline(always)]
#[receive(contract = "fib", name = "receive", parameter = "u64", return_value = "u64")]
fn contract_receive(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State>,
) -> ReceiveResult<u64> {
    // Try to get the parameter (64bit unsigned integer).
    let n: u64 = ctx.parameter_cursor().get()?;
    if n <= 1 {
        host.state().result = 1;
        Ok(1)
    } else {
        let self_address = ctx.self_address();
        let p2 = (n - 2).to_le_bytes();
        let mut n2 = host
            .invoke_contract(
                &self_address,
                Parameter(&p2),
                EntrypointName::new_unchecked("receive"),
                Amount::zero(),
            )
            .unwrap_abort()
            .1
            .unwrap_abort();
        let cv2 = host.state().result;
        let n2: u64 = n2.get().unwrap_abort();
        ensure_eq!(cv2, n2);

        let p1 = (n - 1).to_le_bytes();
        let mut n1 = host
            .invoke_contract(
                &self_address,
                Parameter(&p1),
                EntrypointName::new_unchecked("receive"),
                Amount::zero(),
            )
            .unwrap_abort()
            .1
            .unwrap_abort();
        let cv1 = host.state().result;
        let n1: u64 = n1.get().unwrap_abort();
        ensure_eq!(cv1, n1);
        host.state().result = cv1 + cv2;
        Ok(cv1 + cv2)
    }
}

/// Retrieve the value of the state.
#[inline(always)]
#[receive(contract = "fib", name = "view", return_value = "u64")]
fn contract_view(
    _ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State>,
) -> ReceiveResult<u64> {
    Ok(host.state().result)
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    // Compute the n-th fibonacci number.
    fn fib(n: u64) -> u64 {
        let mut n1 = 1;
        let mut n2 = 1;
        for _ in 2..=n {
            let t = n1;
            n1 = n2;
            n2 += t;
        }
        n2
    }

    #[concordium_test]
    fn receive_works() {
        let mut ctx = ReceiveContextTest::empty();
        let parameter_bytes = to_bytes(&10u64);
        let contract_address = ContractAddress {
            index:    0,
            subindex: 0,
        };
        ctx.set_parameter(&parameter_bytes);
        ctx.set_self_address(contract_address.clone());

        let mut host = HostTest::new(State {
            result: 0,
        });

        host.setup_mock_entrypoint(
            contract_address,
            OwnedEntrypointName::new_unchecked("receive".into()),
            MockFn::new(|parameter, _amount, state: &mut State| {
                let n: u64 = match from_bytes(parameter.0) {
                    Ok(n) => n,
                    Err(_) => return Err(InvokeError::Trap),
                };
                state.result = fib(n);
                Ok((true, state.result))
            }),
        );
        let res = contract_receive(&ctx, &mut host).expect_report("Calling receive failed.");
        assert_eq!(res, fib(10));
        assert_eq!(host.state().result, fib(10));
    }
}
