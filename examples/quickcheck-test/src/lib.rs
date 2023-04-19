use concordium_std::*;

#[derive(Serialize)]
struct State {
    threshold: u16,
    count:     u16,
}

impl State {
    fn new(threshold: u16) -> Self {
        State {
            count: 0,
            threshold,
        }
    }

    // Increment only if the current count is below the threshold.
    fn increment(&mut self) {
        if self.count < self.threshold {
            self.count += 1;
        }
    }
}

#[init(contract = "my_contract")]
fn contract_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<State> {
    let threshold = ctx.parameter_cursor().get()?;
    Ok(State::new(threshold))
}

#[receive(contract = "my_contract", name = "my_receive", mutable)]
fn contract_update_counter<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> ReceiveResult<()> {
    host.state_mut().increment();
    Ok(())
}

#[concordium_cfg_test]
mod test {
    use super::*;

    // Property: counter stays below the threshold for any number of calls `n`.
    // Run 1000 tests with random `threshold` values.
    #[concordium_quickcheck(num_tests = 500)]
    fn prop_counter_always_below_threshold(threshold: u16, n: u16) -> bool {
        let mut state = State::new(threshold);
        for _ in 0..n {
            state.increment()
        }
        state.count <= threshold
    }
}
