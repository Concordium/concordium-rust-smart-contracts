#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;

#[derive(Serialize, Clone)]
pub struct State {
    result: u64,
}

#[init(contract = "fib")]
#[inline(always)]
fn contract_init(_ctx: &InitContext, _state_builder: &mut StateBuilder) -> InitResult<State> {
    let state = State { result: 0 };
    Ok(state)
}

// Add the the nth Fibonacci number F(n) to this contract's state.
// This is achieved by recursively calling the contract itself.
#[inline(always)]
#[receive(
    contract = "fib",
    name = "receive",
    parameter = "u64",
    return_value = "u64",
    mutable
)]
fn contract_receive(ctx: &ReceiveContext, host: &mut Host<State>) -> ReceiveResult<u64> {
    // Try to get the parameter (64bit unsigned integer).
    let n: u64 = ctx.parameter_cursor().get()?;
    if n <= 1 {
        host.state_mut().result = 1;
        Ok(1)
    } else {
        let self_address = ctx.self_address();
        let mut n2 = host
            .invoke_contract_raw(
                &self_address,
                Parameter::new_unchecked(&(n - 2).to_le_bytes()[..]),
                EntrypointName::new_unchecked("receive"),
                Amount::zero(),
            )
            .unwrap_abort()
            .1
            .unwrap_abort();
        let cv2 = host.state().result;
        let n2: u64 = n2.get().unwrap_abort();
        ensure_eq!(cv2, n2);
        let mut n1 = host
            .invoke_contract_raw(
                &self_address,
                Parameter::new_unchecked(&(n - 1).to_le_bytes()[..]),
                EntrypointName::new_unchecked("receive"),
                Amount::zero(),
            )
            .unwrap_abort()
            .1
            .unwrap_abort();
        let cv1 = host.state().result;
        let n1: u64 = n1.get().unwrap_abort();
        ensure_eq!(cv1, n1);
        host.state_mut().result = cv1 + cv2;
        Ok(cv1 + cv2)
    }
}

/// Retrieve the value of the state.
#[inline(always)]
#[receive(contract = "fib", name = "view", return_value = "u64")]
fn contract_view(_ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<u64> {
    Ok(host.state().result)
}
