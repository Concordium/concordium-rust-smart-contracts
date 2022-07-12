use concordium_std::*;

#[derive(Reject, PartialEq, Eq, Debug)]
enum ContractError {
    Error,
    ParseError,
}

impl From<ParseError> for ContractError {
    fn from(_: ParseError) -> Self { ContractError::ParseError }
}

#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S: HasStateApi> {
    my_boxed_num: StateBox<u32, S>,
    my_num:       u32,
    my_set:       StateSet<u32, S>,
    my_map:       StateMap<u32, StateBox<u32, S>, S>,
}

impl<S: HasStateApi> State<S> {
    #[cfg(test)]
    fn get_values(&self) -> (u32, u32, Vec<u32>, Vec<(u32, u32)>) {
        let set: Vec<u32> = self.my_set.iter().map(|v| *v).collect();
        let map: Vec<(u32, u32)> = self.my_map.iter().map(|(k, v)| (*k, v.get().clone())).collect();
        (*self.my_boxed_num.get(), self.my_num, set, map)
    }

    fn increment(&mut self) {
        self.my_boxed_num.update(|v| *v += 1);
        self.my_num += 1;
    }

    fn add_to_set(&mut self) { self.my_set.insert(self.my_num); }

    fn add_to_map(&mut self, state_builder: &mut StateBuilder<S>) {
        self.my_map.insert(self.my_num, state_builder.new_box(self.my_num));
    }
}

// #[concordium_cfg_test]
// mod test_impls {
//     use super::*;
//     use concordium_std::test_infrastructure::*;

//     unsafe impl StateClone for State<TestStateApi> {
//         unsafe fn clone_state(&self, cloned_state_api: TestStateApi) -> Self
// {             Self {
//                 my_boxed_num: StateBox::clone_state(&self.my_boxed_num,
// cloned_state_api.clone()),                 my_num:       self.my_num,
//                 my_set:
// self.my_set.clone_state(cloned_state_api.clone()),                 my_map:
// self.my_map.clone_state(cloned_state_api),             }
//         }
//     }
// }

#[init(contract = "test-host-rollback")]
fn init<S: HasStateApi>(
    _: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    Ok(State {
        my_boxed_num: state_builder.new_box(0),
        my_num:       0,
        my_set:       state_builder.new_set(),
        my_map:       state_builder.new_map(),
    })
}

#[receive(mutable, contract = "test-host-rollback", name = "update")]
fn contract_update<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(), ContractError> {
    // Always increment state.
    let (state, state_builder) = host.state_and_builder();
    state.increment();
    state.add_to_set();
    state.add_to_map(state_builder);

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
    fn test_rollback_immediately() {
        let ctx_init = TestInitContext::empty();
        let mut state_builder = TestStateBuilder::new();
        let state = init(&ctx_init, &mut state_builder).expect_report("Failed to initialize");
        let mut host = TestHost::new(state, state_builder);

        claim_eq!(host.state().get_values(), (0, 0, vec![], vec![]));

        let mut ctx_rcv = TestReceiveContext::default();
        let parameter = to_bytes(&false);
        ctx_rcv.set_parameter(&parameter); // Don't invoke, just increment and then return Err.

        // Call update function.
        let result = with_rollback(|host| contract_update(&ctx_rcv, host), &mut host);
        claim_eq!(result, Err(ContractError::Error));

        // The state should be 0, as the update failed.
        claim_eq!(host.state().get_values(), (0, 0, vec![], vec![]));
    }

    #[concordium_test]
    fn test_rollback_inner_call_only() {
        let ctx_init = TestInitContext::empty();
        let mut state_builder = TestStateBuilder::new();
        let state = init(&ctx_init, &mut state_builder).expect_report("Failed to initialize");
        let mut host = TestHost::new(state, state_builder);

        claim_eq!(host.state().get_values(), (0, 0, vec![], vec![]));

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
            MockFn::new_v1::<(), _>(|_, _, _, state: &mut State<TestStateApi>| {
                state.increment();
                state.add_to_set();
                Err(CallContractError::Trap)
            }),
        );

        // Call update function.
        let result = with_rollback(|host| contract_update(&ctx_rcv, host), &mut host);
        claim_eq!(result, Ok(()));

        // The state should be 1, as the outer receive worked, but the inner invoke
        // failed.
        claim_eq!(host.state().get_values(), (1, 1, vec![1], vec![(1, 1)]));
    }

    #[concordium_test]
    fn test_no_rollback() {
        let ctx_init = TestInitContext::empty();
        let mut state_builder = TestStateBuilder::new();
        let state = init(&ctx_init, &mut state_builder).expect_report("Failed to initialize");
        let mut host = TestHost::new(state, state_builder);

        claim_eq!(host.state().get_values(), (0, 0, vec![], vec![]));

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
            MockFn::new_v1::<(), _>(|_, _, _, state: &mut State<TestStateApi>| {
                state.increment();
                state.add_to_set();
                // NOTE: Cannot get StateBuilder for calling add_to_map.
                Ok((true, ()))
            }),
        );

        // Call update function.
        let result = with_rollback(|host| contract_update(&ctx_rcv, host), &mut host);
        claim_eq!(result, Ok(()));

        // The state should be (2,2), as both the inner and outer call succeeded.
        claim_eq!(host.state().get_values(), (2, 2, vec![1, 2], vec![(1, 1)]));
    }
}
