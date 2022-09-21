//! Note: This contract is not meant for production, it is used to illustrate
//! how to use the standard library and the tooling Concordium provides. There
//! is no claim that the logic of the contract is reasonable, or safe.
//!
//! # A Concordium V1 smart contract
use concordium_std::*;

/// Your smart contract state.
#[derive(Serialize, SchemaType)]
pub struct State {
    // Your state
}

/// Your smart contract errors.
#[derive(Reject, Serial, SchemaType)]
enum Error {
    /// YourError
    YourError,
}

/// Init function that creates a new smart contract.
#[init(contract = "{{crate_name}}")]
fn your_smart_contract_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<State> {
    // Your code

    Ok(State {})
}

/// Payable Receive function.
#[receive(contract = "{{crate_name}}", name = "receiveFunction", payable, mutable, error = "Error")]
fn your_smart_contract_receive_function<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    _host: &mut impl HasHost<State, StateApiType = S>,
    _amount: Amount,
) -> Result<(), Error> {
    // Your code

    let error_occurred = false;

    if error_occurred {
        Err(Error::YourError)
    } else {
        Ok(())
    }
}

/// View function that returns the content of the state.
#[receive(contract = "{{crate_name}}", name = "viewFunction", return_value = "State")]
fn your_smart_contract_view_function<'a, 'b, S: HasStateApi>(
    _ctx: &'a impl HasReceiveContext,
    host: &'b impl HasHost<State, StateApiType = S>,
) -> ReceiveResult<&'b State> {
    Ok(host.state())
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    #[concordium_test]
    /// Init test
    fn test_init() {
        let ctx = TestInitContext::empty();

        let mut state_builder = TestStateBuilder::new();

        let state_result = your_smart_contract_init(&ctx, &mut state_builder);
        state_result.expect_report("Contract initialization results in error");
    }

    #[concordium_test]
    /// Test 1
    fn test_1() {
        // Your test
    }
}
