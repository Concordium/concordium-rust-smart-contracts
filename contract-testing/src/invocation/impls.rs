use super::types::*;
use crate::{
    constants,
    impls::{
        contract_events_from_logs, from_interpreter_energy, lookup_module_cost,
        to_interpreter_energy,
    },
    types::{Account, BalanceError, Contract, ContractModule, TransferError},
    DebugTraceElement, ExecutionError, InvokeExecutionError,
};
use concordium_base::{
    base::{AccountAddressEq, Energy, InsufficientEnergy},
    constants::MAX_PARAMETER_LEN,
    contracts_common::{
        to_bytes, AccountAddress, AccountBalance, Address, Amount, ChainMetadata, ContractAddress,
        ExchangeRates, ModuleReference, OwnedEntrypointName, OwnedReceiveName,
    },
    smart_contracts::{
        ContractTraceElement, InstanceUpdatedEvent, OwnedContractName, OwnedParameter, WasmVersion,
    },
    transactions::UpdateContractPayload,
};
use concordium_smart_contract_engine::{
    v0,
    v1::{self, trie, InvokeResponse},
    ExecResult, InterpreterEnergy,
};
use concordium_wasm::artifact::{self, CompiledFunction};
use std::collections::{btree_map, BTreeMap};

impl<'a, 'b> EntrypointInvocationHandler<'a, 'b> {
    /// Used for handling the *initial* part of invoking an entrypoint.
    ///
    /// **Preconditions:**
    ///  - `invoker` exists
    ///  - `invoker` has sufficient balance to pay for `remaining_energy`
    ///  - `sender` exists
    ///  - if the contract (`contract_address`) exists, then its `module` must
    ///    also exist.
    fn invoke_entrypoint_initial(
        &mut self,
        invoker: AccountAddress,
        sender: Address,
        payload: UpdateContractPayload,
        trace_elements_checkpoint: usize,
    ) -> Result<
        Result<(v1::ReceiveResult<CompiledFunction>, InvocationData), InvokeResponse>,
        TestConfigurationError,
    > {
        // Charge the base cost for updating a contract.
        self.remaining_energy
            .tick_energy(constants::UPDATE_CONTRACT_INSTANCE_BASE_COST)?;

        // Move the amount from the sender to the contract, if any.
        // And get the new self_balance.
        let instance_self_balance = if payload.amount.micro_ccd() > 0 {
            let transfer_result = match sender {
                Address::Account(sender_account) => self.transfer_from_account_to_contract(
                    payload.amount,
                    sender_account,
                    payload.address,
                ),
                Address::Contract(sender_contract) => self.transfer_from_contract_to_contract(
                    payload.amount,
                    sender_contract,
                    payload.address,
                ),
            };
            match transfer_result {
                Ok(new_balance_from) => new_balance_from,
                Err(transfer_error) => {
                    let kind = match transfer_error {
                        TransferError::BalanceError {
                            error: BalanceError::Overflow,
                        } => {
                            // Balance overflows are unrecoverable and short circuit.
                            return Err(TestConfigurationError::BalanceOverflow);
                        }
                        TransferError::BalanceError {
                            error: BalanceError::Insufficient,
                        } => v1::InvokeFailure::InsufficientAmount,
                        TransferError::ToMissing => v1::InvokeFailure::NonExistentContract,
                    };
                    // Return early.
                    return Ok(Err(v1::InvokeResponse::Failure { kind }));
                }
            }
        } else {
            match self.contract_balance(payload.address) {
                Some(self_balance) => self_balance,
                None => {
                    // Return early.
                    return Ok(Err(v1::InvokeResponse::Failure {
                        kind: v1::InvokeFailure::NonExistentContract,
                    }));
                }
            }
        };

        // Get the instance and artifact. To be used in several places.
        let instance = self
            .chain
            .contracts
            .get(&payload.address)
            .expect("Contract known to exist at this point");
        let module = self.contract_module(instance);

        // Construct the receive name (or fallback receive name) and ensure its presence
        // in the contract. Also returns the contract name and entrypoint name as they
        // are needed further down.
        let (contract_name, receive_name, entrypoint_name) = {
            let borrowed_receive_name = payload.receive_name.as_receive_name();
            let contract_name = borrowed_receive_name.contract_name();
            let owned_contract_name =
                OwnedContractName::new_unchecked(format!("init_{}", contract_name));
            let owned_entrypoint_name = borrowed_receive_name.entrypoint_name().to_owned();
            let receive_name = borrowed_receive_name.get_chain_name();
            let fallback_receive_name = format!("{}.", contract_name);
            if module.artifact.has_entrypoint(receive_name) {
                (
                    owned_contract_name,
                    payload.receive_name,
                    owned_entrypoint_name,
                )
            } else if module
                .artifact
                .has_entrypoint(fallback_receive_name.as_str())
            {
                (
                    owned_contract_name,
                    OwnedReceiveName::new_unchecked(fallback_receive_name),
                    owned_entrypoint_name,
                )
            } else {
                // Return early.
                return Ok(Err(v1::InvokeResponse::Failure {
                    kind: v1::InvokeFailure::NonExistentEntrypoint,
                }));
            }
        };

        // Subtract the cost of looking up the module
        self.remaining_energy
            .tick_energy(lookup_module_cost(&module))?;

        // Sender policies have a very bespoke serialization in
        // order to allow skipping portions of them in smart contracts.
        let sender_policies = {
            let mut out = Vec::new();
            let policy = &self
                .chain
                .account(invoker)
                .expect("Precondition violation: invoker must exist.")
                .policy;
            policy
                .serial_for_smart_contract(&mut out)
                .expect("Writing to a vector should succeed.");
            out
        };

        // Construct the receive context
        let receive_ctx = v1::ReceiveContext {
            // This should be the entrypoint specified, even if we end up
            // calling the fallback entrypoint, as this will be visible to the
            // contract via a host function.
            entrypoint: entrypoint_name.clone(),
            common:     v0::ReceiveContext {
                metadata: ChainMetadata {
                    slot_time: self.chain.parameters.block_time,
                },
                invoker,
                self_address: payload.address,
                self_balance: instance_self_balance,
                sender,
                owner: instance.owner,
                sender_policies,
            },
        };

        let mod_idx_before_invoke = self.next_contract_modification_index;

        // Construct the instance state
        let mut loader = v1::trie::Loader::new(&[][..]); // An empty loader is fine currently, as we do not use caching in this lib.
        let mut mutable_state = self.contract_state(payload.address);
        let mut mutable_state = mutable_state.make_fresh_generation(&mut loader);
        let inner = mutable_state.get_inner(&mut loader);
        let instance_state = v1::InstanceState::new(loader, inner);

        // Get the initial result from invoking receive
        let initial_result = self.run_interpreter(|energy| {
            v1::invoke_receive(
                module.artifact,
                receive_ctx,
                v1::ReceiveInvocation {
                    amount: payload.amount,
                    // This will either be the one provided on the fallback receive name.
                    receive_name: receive_name.as_receive_name(),
                    parameter: payload.message.as_ref(),
                    energy,
                },
                instance_state,
                v1::ReceiveParams {
                    max_parameter_size:           MAX_PARAMETER_LEN,
                    limit_logs_and_return_values: false,
                    support_queries:              true,
                },
            )
        })?;
        // Set up some data needed for recursively processing the receive until the end,
        // i.e. beyond interrupts.
        Ok(Ok((initial_result, InvocationData {
            sender,
            address: payload.address,
            contract_name,
            entrypoint: entrypoint_name,
            parameter: payload.message,
            amount: payload.amount,
            state: mutable_state,
            trace_elements_checkpoint,
            next_mod_idx_checkpoint: mod_idx_before_invoke,
            mod_idx_before_invoke,
        })))
    }

    /// Used for handling contract entrypoint invocations internally.
    ///
    /// **Preconditions:**
    ///  - `invoker` exists
    ///  - `invoker` has sufficient balance to pay for `remaining_energy`
    ///  - `sender` exists
    ///  - if the contract (`contract_address`) exists, then its `module` must
    ///    also exist.
    pub(crate) fn invoke_entrypoint(
        &mut self,
        invoker: AccountAddress,
        sender: Address,
        payload: UpdateContractPayload,
    ) -> Result<(InvokeResponse, Vec<DebugTraceElement>), TestConfigurationError> {
        let mut stack = Vec::new();
        let mut trace_elements = Vec::new();
        stack.push(Next::Initial {
            sender,
            payload,
            trace_elements_checkpoint: 0,
        });
        // Initialized to a dummy value. This will always be set or the function will
        // terminate with an Err.
        let mut invoke_response: Option<InvokeResponse> = None;
        while let Some(invocation_data) = stack.pop() {
            let (receive_result, mut invocation_data) = match invocation_data {
                Next::Resume {
                    mut data,
                    config,
                    response,
                } => {
                    match response {
                        Some(response) => {
                            let receive_result = self.run_interpreter(|energy| {
                                v1::resume_receive(
                                    config,
                                    response,
                                    energy,
                                    &mut data.state,
                                    false, /* the state never changes on interrupts that have
                                            * immediate handlers */
                                    // An empty loader is fine currently, as we do not use
                                    // caching in this lib.
                                    v1::trie::Loader::new(&[][..]),
                                )
                            })?;
                            (receive_result, data)
                        }
                        None => {
                            // we are resuming from a contract call
                            let (success, call_response) = match invoke_response
                                .take()
                                .expect("Response should be available")
                            {
                                v1::InvokeResponse::Success {
                                    data: return_value, ..
                                } => {
                                    let invoke_response = v1::InvokeResponse::Success {
                                        // The balance returned by `invoke_entrypoint`
                                        // is the balance of the contract called. But we
                                        // are interested in the new balance of the caller.
                                        new_balance: self.contract_balance_unchecked(data.address),
                                        data:        return_value,
                                    };
                                    (true, invoke_response)
                                }
                                failure => (false, failure),
                            };

                            // Remove the last state changes if the invocation failed.
                            let state_changed = if !success {
                                self.rollback();
                                false // We rolled back, so no changes were
                                      // made to this contract.
                            } else {
                                let mod_idx_after_invoke = self.modification_index(data.address);
                                let state_changed =
                                    mod_idx_after_invoke != data.mod_idx_before_invoke;
                                if state_changed {
                                    // Update the state field with the newest value from the
                                    // changeset.
                                    data.state = self.contract_state(data.address);
                                }
                                state_changed
                            };

                            // Add resume event
                            let resume_event = ContractTraceElement::Resumed {
                                address: data.address,
                                success,
                            };

                            self.push_regular_trace_element(
                                &mut trace_elements,
                                resume_event,
                                data.entrypoint.clone(),
                            );
                            let receive_result = self.run_interpreter(|energy| {
                                v1::resume_receive(
                                    config,
                                    call_response,
                                    energy,
                                    &mut data.state,
                                    state_changed,
                                    // An empty loader is fine currently, as we do not use
                                    // caching in this lib.
                                    v1::trie::Loader::new(&[][..]),
                                )
                            })?;
                            (receive_result, data)
                        }
                    }
                }
                Next::Initial {
                    sender,
                    payload,
                    trace_elements_checkpoint,
                } => {
                    match self.invoke_entrypoint_initial(
                        invoker,
                        sender,
                        payload,
                        trace_elements_checkpoint,
                    )? {
                        Ok(x) => x,
                        Err(ier) => {
                            // invocation has failed. No more to do for this call.
                            // Since no traces were produced we don't have to roll them back.
                            invoke_response = Some(ier);
                            continue;
                        }
                    }
                }
            };

            match receive_result {
                v1::ReceiveResult::Success {
                    logs,
                    state_changed,
                    return_value,
                    remaining_energy,
                } => {
                    // Update the remaining_energy field.
                    self.update_energy(remaining_energy);

                    let update_event = ContractTraceElement::Updated {
                        data: InstanceUpdatedEvent {
                            contract_version: WasmVersion::V1,
                            address:          invocation_data.address,
                            instigator:       invocation_data.sender,
                            amount:           invocation_data.amount,
                            message:          invocation_data.parameter.clone(),
                            receive_name:     OwnedReceiveName::construct_unchecked(
                                invocation_data.contract_name.as_contract_name(),
                                invocation_data.entrypoint.as_entrypoint_name(),
                            ),
                            events:           contract_events_from_logs(logs),
                        },
                    };
                    // Add update event
                    self.push_regular_trace_element(
                        &mut trace_elements,
                        update_event,
                        invocation_data.entrypoint.clone(),
                    );

                    // Save changes to changeset.
                    if state_changed {
                        self.save_state_changes(
                            invocation_data.address,
                            &mut invocation_data.state,
                        );
                    }

                    invoke_response = Some(v1::InvokeResponse::Success {
                        new_balance: self.contract_balance_unchecked(invocation_data.address),
                        data:        Some(return_value),
                    });
                }
                v1::ReceiveResult::Interrupt {
                    remaining_energy,
                    state_changed,
                    logs,
                    config,
                    interrupt,
                } => {
                    // Update the remaining_energy field.
                    self.update_energy(remaining_energy);
                    // Create the interrupt event, which will be included for transfers, calls,
                    // and upgrades, but not for the remaining
                    // interrupts.
                    let interrupt_event = ContractTraceElement::Interrupted {
                        address: invocation_data.address,
                        events:  contract_events_from_logs(logs),
                    };
                    // Remember what state we are in before invoking.
                    // This is used to report, upon resume, whether the contracts's
                    // state has changed.
                    invocation_data.mod_idx_before_invoke = if state_changed {
                        self.save_state_changes(invocation_data.address, &mut invocation_data.state)
                    } else {
                        self.modification_index(invocation_data.address)
                    };
                    match interrupt {
                        v1::Interrupt::Transfer { to, amount } => {
                            // Add the interrupt event
                            self.push_regular_trace_element(
                                &mut trace_elements,
                                interrupt_event,
                                invocation_data.entrypoint.clone(),
                            );

                            let response = match self.transfer_from_contract_to_account(
                                amount,
                                invocation_data.address,
                                to,
                            ) {
                                Ok(new_balance) => v1::InvokeResponse::Success {
                                    new_balance,
                                    data: None,
                                },
                                Err(err) => {
                                    let kind = match err {
                                        TransferError::ToMissing => {
                                            v1::InvokeFailure::NonExistentAccount
                                        }

                                        TransferError::BalanceError {
                                            error: BalanceError::Insufficient,
                                        } => v1::InvokeFailure::InsufficientAmount,

                                        TransferError::BalanceError {
                                            error: BalanceError::Overflow,
                                        } => {
                                            // Balance overflows are unrecoverable and short
                                            // circuit.
                                            return Err(TestConfigurationError::BalanceOverflow);
                                        }
                                    };
                                    v1::InvokeResponse::Failure { kind }
                                }
                            };

                            let success = matches!(response, v1::InvokeResponse::Success { .. });
                            if success {
                                // Add transfer event
                                let transfer_event = ContractTraceElement::Transferred {
                                    from: invocation_data.address,
                                    amount,
                                    to,
                                };
                                self.push_regular_trace_element(
                                    &mut trace_elements,
                                    transfer_event,
                                    invocation_data.entrypoint.clone(),
                                );
                            }
                            // Add resume event
                            let resume_event = ContractTraceElement::Resumed {
                                address: invocation_data.address,
                                success,
                            };
                            self.push_regular_trace_element(
                                &mut trace_elements,
                                resume_event,
                                invocation_data.entrypoint.clone(),
                            );

                            self.remaining_energy.tick_energy(
                                concordium_base::transactions::cost::SIMPLE_TRANSFER,
                            )?;

                            stack.push(Next::Resume {
                                data: invocation_data,
                                // the state never changes on transfers
                                config,
                                response: Some(response),
                            });
                        }
                        v1::Interrupt::Call {
                            address,
                            parameter,
                            name,
                            amount,
                        } => {
                            // Add the interrupt event
                            self.push_regular_trace_element(
                                &mut trace_elements,
                                interrupt_event,
                                invocation_data.entrypoint.clone(),
                            );

                            match self
                                .chain
                                .contracts
                                .get(&address)
                                .map(|c| c.contract_name.as_contract_name())
                            {
                                // The contract to call does not exist.
                                None => {
                                    let response = v1::InvokeResponse::Failure {
                                        kind: v1::InvokeFailure::NonExistentContract,
                                    };
                                    // Add resume event
                                    let resume_event = ContractTraceElement::Resumed {
                                        address: invocation_data.address,
                                        success: false,
                                    };
                                    self.push_regular_trace_element(
                                        &mut trace_elements,
                                        resume_event,
                                        invocation_data.entrypoint.clone(),
                                    );
                                    stack.push(Next::Resume {
                                        data: invocation_data,
                                        config,
                                        response: Some(response),
                                    });
                                }
                                Some(contract_name) => {
                                    // Make a checkpoint before calling another contract so that we
                                    // may roll back.
                                    self.checkpoint();

                                    let receive_name = OwnedReceiveName::construct_unchecked(
                                        contract_name,
                                        name.as_entrypoint_name(),
                                    );
                                    let message = OwnedParameter::new_unchecked(parameter);

                                    let sender = Address::Contract(invocation_data.address);
                                    // Remember to continue the current execution after handling the
                                    // call.
                                    stack.push(Next::Resume {
                                        data: invocation_data,
                                        config,
                                        response: None,
                                    });

                                    // Add the call to the stack to execute.
                                    stack.push(Next::Initial {
                                        sender,
                                        payload: UpdateContractPayload {
                                            amount,
                                            address,
                                            receive_name,
                                            message,
                                        },
                                        trace_elements_checkpoint: trace_elements.len(),
                                    });
                                }
                            };
                        }
                        v1::Interrupt::Upgrade { module_ref } => {
                            // Add the interrupt event.
                            self.push_regular_trace_element(
                                &mut trace_elements,
                                interrupt_event,
                                invocation_data.entrypoint.clone(),
                            );

                            // Charge a base cost.
                            self.remaining_energy
                                .tick_energy(constants::INITIALIZE_CONTRACT_INSTANCE_BASE_COST)?;

                            let response = match self.chain.modules.get(&module_ref) {
                                None => v1::InvokeResponse::Failure {
                                    kind: v1::InvokeFailure::UpgradeInvalidModuleRef,
                                },
                                Some(module) => {
                                    // Charge for the module lookup.
                                    self.remaining_energy
                                        .tick_energy(lookup_module_cost(module))?;

                                    if module.artifact.export.contains_key(
                                        invocation_data
                                            .contract_name
                                            .as_contract_name()
                                            .get_chain_name(),
                                    ) {
                                        // Update module reference in the changeset.
                                        let old_module_ref = self.save_module_upgrade(
                                            invocation_data.address,
                                            module_ref,
                                        );

                                        // Charge for the initialization cost.
                                        self.remaining_energy.tick_energy(
                                            constants::INITIALIZE_CONTRACT_INSTANCE_CREATE_COST,
                                        )?;

                                        let upgrade_event = ContractTraceElement::Upgraded {
                                            address: invocation_data.address,
                                            from:    old_module_ref,
                                            to:      module_ref,
                                        };

                                        self.push_regular_trace_element(
                                            &mut trace_elements,
                                            upgrade_event,
                                            invocation_data.entrypoint.clone(),
                                        );

                                        v1::InvokeResponse::Success {
                                            new_balance: self.contract_balance_unchecked(
                                                invocation_data.address,
                                            ),
                                            data:        None,
                                        }
                                    } else {
                                        v1::InvokeResponse::Failure {
                                            kind: v1::InvokeFailure::UpgradeInvalidContractName,
                                        }
                                    }
                                }
                            };

                            let success = matches!(response, v1::InvokeResponse::Success { .. });
                            let resumed_event = ContractTraceElement::Resumed {
                                address: invocation_data.address,
                                success,
                            };
                            self.push_regular_trace_element(
                                &mut trace_elements,
                                resumed_event,
                                invocation_data.entrypoint.clone(),
                            );
                            stack.push(Next::Resume {
                                data: invocation_data,
                                config,
                                response: Some(response),
                            });
                        }
                        v1::Interrupt::QueryAccountBalance { address } => {
                            let response = match self.account_balance(address) {
                                Some(balance) => v1::InvokeResponse::Success {
                                    new_balance: self
                                        .contract_balance_unchecked(invocation_data.address),
                                    data:        Some(to_bytes(&balance)),
                                },
                                None => v1::InvokeResponse::Failure {
                                    kind: v1::InvokeFailure::NonExistentAccount,
                                },
                            };

                            self.remaining_energy.tick_energy(
                                constants::CONTRACT_INSTANCE_QUERY_ACCOUNT_BALANCE_COST,
                            )?;
                            stack.push(Next::Resume {
                                data: invocation_data,
                                config,
                                response: Some(response),
                            });
                        }
                        v1::Interrupt::QueryContractBalance { address } => {
                            let response = match self.contract_balance(address) {
                                None => v1::InvokeResponse::Failure {
                                    kind: v1::InvokeFailure::NonExistentContract,
                                },
                                Some(bal) => v1::InvokeResponse::Success {
                                    // Balance of contract querying. Won't change. Notice the
                                    // `data.address`.
                                    new_balance: self
                                        .contract_balance_unchecked(invocation_data.address),
                                    data:        Some(to_bytes(&bal)),
                                },
                            };

                            self.remaining_energy.tick_energy(
                                constants::CONTRACT_INSTANCE_QUERY_CONTRACT_BALANCE_COST,
                            )?;
                            stack.push(Next::Resume {
                                data: invocation_data,
                                config,
                                response: Some(response),
                            });
                        }
                        v1::Interrupt::QueryExchangeRates => {
                            let exchange_rates = ExchangeRates {
                                euro_per_energy:    self.chain.parameters.euro_per_energy,
                                micro_ccd_per_euro: self.chain.parameters.micro_ccd_per_euro,
                            };

                            let response = v1::InvokeResponse::Success {
                                new_balance: self
                                    .contract_balance_unchecked(invocation_data.address),
                                data:        Some(to_bytes(&exchange_rates)),
                            };

                            self.remaining_energy.tick_energy(
                                constants::CONTRACT_INSTANCE_QUERY_EXCHANGE_RATE_COST,
                            )?;

                            stack.push(Next::Resume {
                                data: invocation_data,
                                config,
                                response: Some(response),
                            });
                        }
                    }
                }
                v1::ReceiveResult::Reject {
                    reason,
                    return_value,
                    remaining_energy,
                } => {
                    self.update_energy(remaining_energy);
                    // Remove the failure stack traces from the list and include them in a failure
                    // element.
                    let failure_traces =
                        trace_elements.split_off(invocation_data.trace_elements_checkpoint);

                    // Create a `WithFailures` element even if `failure_traces` is empty, as the
                    // reject reason and energy usage is still relevant.
                    let with_failure = DebugTraceElement::WithFailures {
                        contract_address: invocation_data.address,
                        entrypoint:       invocation_data.entrypoint.clone(),
                        error:            InvokeExecutionError::Reject {
                            reason,
                            return_value: return_value.clone(),
                        },
                        trace_elements:   failure_traces,
                        energy_used:      self.energy_used(),
                    };
                    trace_elements.push(with_failure);

                    // Reset the next modification index as well.
                    self.next_contract_modification_index = invocation_data.next_mod_idx_checkpoint;
                    invoke_response = Some(v1::InvokeResponse::Failure {
                        kind: v1::InvokeFailure::ContractReject {
                            code: reason,
                            data: return_value,
                        },
                    });
                }
                v1::ReceiveResult::Trap {
                    error,
                    remaining_energy,
                } => {
                    self.update_energy(remaining_energy);
                    // Remove the failure stack traces from the list and include them in a failure
                    // element.
                    let failure_traces =
                        trace_elements.split_off(invocation_data.trace_elements_checkpoint);

                    // Create a `WithFailures` element even if `failure_traces` is empty, as the
                    // error and energy usage is still relevant.
                    let with_failure = DebugTraceElement::WithFailures {
                        contract_address: invocation_data.address,
                        entrypoint:       invocation_data.entrypoint.clone(),
                        error:            InvokeExecutionError::Trap {
                            error: ExecutionError(error),
                        },
                        trace_elements:   failure_traces,
                        energy_used:      self.energy_used(),
                    };
                    trace_elements.push(with_failure);

                    // Reset the next modification index as well.
                    self.next_contract_modification_index = invocation_data.next_mod_idx_checkpoint;
                    invoke_response = Some(v1::InvokeResponse::Failure {
                        kind: v1::InvokeFailure::RuntimeError,
                    });
                }
                // Convert this to an error here, so that we will short circuit processing.
                v1::ReceiveResult::OutOfEnergy => return Err(TestConfigurationError::OutOfEnergy),
            }
        }
        Ok((
            invoke_response.expect("Response should have been set."),
            trace_elements,
        ))
    }

    /// Make a transfer from a contract to an account in the changeset.
    ///
    /// Returns the new balance of `from`.
    ///
    /// **Preconditions:**
    ///  - Assumes that `from` contract exists.
    fn transfer_from_contract_to_account(
        &mut self,
        amount: Amount,
        from: ContractAddress,
        to: AccountAddress,
    ) -> Result<Amount, TransferError> {
        // Ensure the `to` account exists.
        if !self.chain.accounts.contains_key(&to.into()) {
            return Err(TransferError::ToMissing);
        }

        // Make the transfer.
        let new_balance = self.change_contract_balance(from, AmountDelta::Negative(amount))?;
        self.change_account_balance(to, AmountDelta::Positive(amount))
            .expect("Cannot fail when adding");

        Ok(new_balance)
    }

    /// Make a transfer between contracts in the changeset.
    ///
    /// Returns the new balance of `to`.
    ///
    /// **Preconditions:**
    ///  - Assumes that `from` contract exists.
    fn transfer_from_contract_to_contract(
        &mut self,
        amount: Amount,
        from: ContractAddress,
        to: ContractAddress,
    ) -> Result<Amount, TransferError> {
        // Ensure the `to` contract exists.
        if !self.chain.contracts.contains_key(&to) {
            return Err(TransferError::ToMissing);
        }

        // Make the transfer.
        self.change_contract_balance(from, AmountDelta::Negative(amount))?;
        let new_balance = self.change_contract_balance(to, AmountDelta::Positive(amount))?;
        Ok(new_balance)
    }

    /// Make a transfer from an account to a contract in the changeset.
    ///
    /// Returns the new balance of `to`.
    ///
    /// **Preconditions:**
    ///  - Assumes that `from` account exists.
    fn transfer_from_account_to_contract(
        &mut self,
        amount: Amount,
        from: AccountAddress,
        to: ContractAddress,
    ) -> Result<Amount, TransferError> {
        // Ensure the `to` account exists.
        if !self.chain.contracts.contains_key(&to) {
            return Err(TransferError::ToMissing);
        }

        // Make the transfer.
        self.change_account_balance(from, AmountDelta::Negative(amount))?;
        let new_balance = self.change_contract_balance(to, AmountDelta::Positive(amount))?;
        Ok(new_balance)
    }

    /// Changes the contract balance in the topmost checkpoint on the changeset.
    ///
    /// If contract isn't already present in the changeset, it is added.
    ///
    /// Returns an error if the change in balance would go below `0`, which is a
    /// valid error, or if the amounts would overflow, which is an unrecoverable
    /// configuration error in the tests.
    /// Otherwise, it returns the new balance of the contract.
    ///
    /// The precondition is not part of the error type, as this is an internal
    /// helper function that is only called when the precondition is met.
    ///
    /// Returns the new balance.
    ///
    /// **Preconditions:**
    ///  - Contract must exist.
    fn change_contract_balance(
        &mut self,
        address: ContractAddress,
        delta: AmountDelta,
    ) -> Result<Amount, BalanceError> {
        match self.changeset.current_mut().contracts.entry(address) {
            btree_map::Entry::Vacant(vac) => {
                // get original balance
                let original_balance = self
                    .chain
                    .contracts
                    .get(&address)
                    .expect("Precondition violation: contract assumed to exist")
                    .self_balance;
                // Try to apply the balance or return an error if insufficient funds.
                let new_contract_balance = delta.apply_to_balance(original_balance)?;
                // Insert the changes into the changeset.
                vac.insert(ContractChanges {
                    self_balance_delta: delta,
                    ..ContractChanges::new(original_balance)
                });
                Ok(new_contract_balance)
            }
            btree_map::Entry::Occupied(mut occ) => {
                let contract_changes = occ.get_mut();
                let new_delta = contract_changes.self_balance_delta.add_delta(delta);
                // Try to apply the balance or return an error if insufficient funds.
                let new_contract_balance =
                    new_delta.apply_to_balance(contract_changes.self_balance_original)?;
                contract_changes.self_balance_delta = new_delta;
                Ok(new_contract_balance)
            }
        }
    }

    /// Changes the account balance in the topmost checkpoint on the changeset.
    ///
    /// If account isn't already present in the changeset, it is added.
    ///
    /// Returns an error if a negative delta is provided which exceeds the
    /// available balance of the account. Otherwise, it returns the new
    /// available balance of the account.
    /// Otherwise, it returns the new balance of the account.
    ///
    /// The precondition is not part of the error type, as this is an internal
    /// helper function that is only called when the precondition is met.
    ///
    /// **Preconditions:**
    ///  - Account must exist.
    fn change_account_balance(
        &mut self,
        address: AccountAddress,
        delta: AmountDelta,
    ) -> Result<Amount, BalanceError> {
        match self.changeset.current_mut().accounts.entry(address.into()) {
            btree_map::Entry::Vacant(vac) => {
                // get original balance
                let mut original_balance = self
                    .chain
                    .accounts
                    .get(&address.into())
                    .expect("Precondition violation: account assumed to exist")
                    .balance
                    .available();
                if self.invoker == address {
                    // It has been checked that the invoker account has sufficient balance for
                    // paying.
                    original_balance -= self.reserved_amount;
                }
                // Try to apply the balance or return an error if insufficient funds.
                let new_account_balance = delta.apply_to_balance(original_balance)?;
                // Insert the changes into the changeset.
                vac.insert(AccountChanges {
                    original_balance,
                    balance_delta: delta,
                });
                Ok(new_account_balance)
            }
            btree_map::Entry::Occupied(mut occ) => {
                let account_changes = occ.get_mut();
                let new_delta = account_changes.balance_delta.add_delta(delta);
                // Try to apply the balance or return an error if insufficient funds.
                let new_account_balance =
                    new_delta.apply_to_balance(account_changes.original_balance)?;
                account_changes.balance_delta = new_delta;
                Ok(new_account_balance)
            }
        }
    }

    /// Returns the contract balance from the topmost checkpoint on the
    /// changeset. Or, alternatively, from persistence.
    ///
    /// **Preconditions:**
    ///  - Contract must exist.
    fn contract_balance_unchecked(&self, address: ContractAddress) -> Amount {
        self.contract_balance(address)
            .expect("Precondition violation: contract must exist")
    }

    /// Looks up the contract balance from the topmost checkpoint on the
    /// changeset. Or, alternatively, from persistence.
    fn contract_balance(&self, address: ContractAddress) -> Option<Amount> {
        match self.changeset.current().contracts.get(&address) {
            Some(changes) => Some(changes.current_balance()),
            None => self.chain.contracts.get(&address).map(|c| c.self_balance),
        }
    }

    /// Returns the contract module from the topmost checkpoint on
    /// the changeset. Or, alternatively, from persistence.
    ///
    /// **Preconditions:**
    ///  - Contract instance must exist (and therefore also the artifact).
    ///  - If the changeset contains a module reference, then it must refer a
    ///    deployed module.
    fn contract_module(&self, contract: &Contract) -> ContractModule {
        match self
            .changeset
            .current()
            .contracts
            .get(&contract.address)
            .and_then(|c| c.module)
        {
            // Contract has been upgrade, new module exists.
            Some(new_module) => self
                .chain
                .modules
                .get(&new_module)
                .expect("Precondition violation: module must exist.")
                .clone(),
            // Contract hasn't been upgraded. Use persisted module.
            None => self
                .chain
                .modules
                .get(&contract.module_reference)
                .expect("Precondition violation: module must exist.")
                .clone(),
        }
    }

    /// Get the contract state, either from the changeset or by thawing it from
    /// persistence.
    ///
    /// **Preconditions:**
    ///  - Contract instance must exist.
    fn contract_state(&self, address: ContractAddress) -> trie::MutableState {
        match self
            .changeset
            .current()
            .contracts
            .get(&address)
            .and_then(|c| c.state.clone())
        {
            // Contract state has been modified.
            Some(modified_state) => modified_state,
            // Contract state hasn't been modified. Thaw from persistence.
            None => self
                .chain
                .contracts
                .get(&address)
                .expect("Precondition violation: contract must exist")
                .state
                .thaw(),
        }
    }

    /// Looks up the account balance for an account by first checking
    /// the changeset, then the persisted values.
    fn account_balance(&self, address: AccountAddress) -> Option<AccountBalance> {
        let mut account_balance = self
            .chain
            .accounts
            .get(&address.into())
            .map(|a| a.balance)?;
        match self
            .changeset
            .current()
            .accounts
            .get(&address.into())
            .map(|a| a.current_balance())
        {
            // Account exists in changeset.
            // Return the staked and locked balances from persistence, as they can't change during
            // entrypoint invocation.
            Some(total) => Some(AccountBalance {
                total,
                staked: account_balance.staked,
                locked: account_balance.locked,
            }),
            // Account doesn't exist in changeset.
            None => {
                if self.invoker == address {
                    account_balance.total -= self.reserved_amount;
                }
                Some(account_balance)
            }
        }
    }

    /// Saves a mutable state for a contract in the changeset.
    ///
    /// If the contract already has an entry in the changeset, the old state
    /// will be replaced. Otherwise, the entry is created and the state is
    /// added.
    ///
    /// This method also increments the `self.next_contract_modification_index`.
    ///
    /// Returns the `modification_index` set for the contract.
    ///
    /// **Preconditions:**
    ///  - Contract must exist.
    fn save_state_changes(
        &mut self,
        address: ContractAddress,
        state: &mut trie::MutableState,
    ) -> u32 {
        let state = state.clone();
        let modification_index = self.next_contract_modification_index;
        match self.changeset.current_mut().contracts.entry(address) {
            btree_map::Entry::Vacant(vac) => {
                let original_balance = self
                    .chain
                    .contracts
                    .get(&address)
                    .expect("Precondition violation: contract must exist.")
                    .self_balance;
                vac.insert(ContractChanges {
                    state: Some(state),
                    modification_index,
                    ..ContractChanges::new(original_balance)
                });
            }
            btree_map::Entry::Occupied(mut occ) => {
                let changes = occ.get_mut();
                changes.state = Some(state);
                changes.modification_index = modification_index;
            }
        }
        self.next_contract_modification_index += 1;
        modification_index
    }

    /// Saves a new module reference for the contract in the changeset.
    ///
    /// If the contract already has an entry in the changeset, the old module is
    /// replaced. Otherwise, the entry is created and the module is added.
    ///
    /// Returns the previous module, which is either the one from persistence,
    /// or the most recent one from the changeset.
    ///
    /// **Preconditions:**
    ///  - Contract must exist.
    ///  - Module must exist.
    fn save_module_upgrade(
        &mut self,
        address: ContractAddress,
        module_reference: ModuleReference,
    ) -> ModuleReference {
        match self.changeset.current_mut().contracts.entry(address) {
            btree_map::Entry::Vacant(vac) => {
                let contract = self
                    .chain
                    .contracts
                    .get(&address)
                    .expect("Precondition violation: contract must exist.");
                let old_module_ref = contract.module_reference;
                let original_balance = contract.self_balance;
                vac.insert(ContractChanges {
                    module: Some(module_reference),
                    ..ContractChanges::new(original_balance)
                });
                old_module_ref
            }
            btree_map::Entry::Occupied(mut occ) => {
                let changes = occ.get_mut();
                let old_module_ref = match changes.module {
                    Some(old_module) => old_module,
                    None => {
                        self.chain
                            .contracts
                            .get(&address)
                            .expect("Precondition violation: contract must exist.")
                            .module_reference
                    }
                };
                changes.module = Some(module_reference);
                old_module_ref
            }
        }
    }

    /// Returns the modification index for a contract.
    ///
    /// It looks it up in the changeset, and if it isn't there, it will return
    /// `0`.
    fn modification_index(&self, address: ContractAddress) -> u32 {
        self.changeset
            .current()
            .contracts
            .get(&address)
            .map_or(0, |c| c.modification_index)
    }

    /// Makes a new checkpoint.
    fn checkpoint(&mut self) { self.changeset.checkpoint(); }

    /// Roll back to the previous checkpoint.
    fn rollback(&mut self) { self.changeset.rollback(); }

    /// Update the `remaining_energy` field by converting the input to
    /// [`InterpreterEnergy`] and then [`Energy`].
    fn update_energy(&mut self, remaining_energy: u64) {
        *self.remaining_energy = from_interpreter_energy(InterpreterEnergy::from(remaining_energy));
    }

    /// Run the interpreter with the provided function and the
    /// `self.remaining_energy`.
    ///
    /// This function ensures that the energy calculations is handled as in the
    /// node.
    fn run_interpreter<F>(
        &mut self,
        f: F,
    ) -> Result<v1::ReceiveResult<artifact::CompiledFunction>, InsufficientEnergy>
    where
        F: FnOnce(InterpreterEnergy) -> ExecResult<v1::ReceiveResult<artifact::CompiledFunction>>,
    {
        let available_interpreter_energy = to_interpreter_energy(*self.remaining_energy);
        let res = match f(available_interpreter_energy) {
            Ok(res) => res,
            Err(err) => {
                // An error occurred in the interpreter and it doesn't return the remaining
                // energy. We convert this to a trap and set the energy to the
                // last known amount.
                return Ok(v1::ReceiveResult::Trap {
                    error:            err,
                    remaining_energy: available_interpreter_energy.energy,
                });
            }
        };
        let mut subtract_then_convert = |remaining_energy| -> Result<u64, InsufficientEnergy> {
            let remaining_energy = InterpreterEnergy::from(remaining_energy);
            // Using `saturating_sub` here should be ok since we should never be able to use
            // more energy than what is available.
            let used_energy = from_interpreter_energy(
                available_interpreter_energy.saturating_sub(remaining_energy),
            );
            self.remaining_energy.tick_energy(used_energy)?;
            Ok(to_interpreter_energy(*self.remaining_energy).energy)
        };
        match res {
            v1::ReceiveResult::Success {
                logs,
                state_changed,
                return_value,
                remaining_energy,
            } => {
                let remaining_energy = subtract_then_convert(remaining_energy)?;
                Ok(v1::ReceiveResult::Success {
                    logs,
                    state_changed,
                    return_value,
                    remaining_energy,
                })
            }

            v1::ReceiveResult::Interrupt {
                remaining_energy,
                state_changed,
                logs,
                config,
                interrupt,
            } => {
                let remaining_energy = subtract_then_convert(remaining_energy)?;

                Ok(v1::ReceiveResult::Interrupt {
                    remaining_energy,
                    state_changed,
                    logs,
                    config,
                    interrupt,
                })
            }
            v1::ReceiveResult::Reject {
                reason,
                return_value,
                remaining_energy,
            } => Ok(v1::ReceiveResult::Reject {
                reason,
                return_value,
                remaining_energy: subtract_then_convert(remaining_energy)?,
            }),
            v1::ReceiveResult::Trap {
                error,
                remaining_energy,
            } => Ok(v1::ReceiveResult::Trap {
                error,
                remaining_energy: subtract_then_convert(remaining_energy)?,
            }),
            // Convert this to an error so that we will short-circuit the processing.
            v1::ReceiveResult::OutOfEnergy => Err(InsufficientEnergy),
        }
    }

    /// The energy used so far in this transaction.
    fn energy_used(&self) -> Energy { self.energy_reserved - *self.remaining_energy }

    /// Helper for that constructs and pushes a [`DebugTraceElement::Regular`]
    /// to the `trace_elements` list provided.
    fn push_regular_trace_element(
        &self,
        trace_elements: &mut Vec<DebugTraceElement>,
        trace_element: ContractTraceElement,
        entrypoint: OwnedEntrypointName,
    ) {
        let energy_used = self.energy_used();
        let new = DebugTraceElement::Regular {
            entrypoint,
            trace_element,
            energy_used,
        };
        trace_elements.push(new);
    }
}

impl ChangeSet {
    /// Creates a new changeset with one empty [`Changes`] element on the
    /// stack..
    pub(crate) fn new() -> Self {
        Self {
            stack: vec![Changes {
                contracts: BTreeMap::new(),
                accounts:  BTreeMap::new(),
            }],
        }
    }

    /// Make a checkpoint by putting a clone of the top element onto the stack.
    fn checkpoint(&mut self) {
        let cloned_top_element = self.current().clone();
        self.stack.push(cloned_top_element);
    }

    /// Perform a rollback by popping the top element of the stack.
    fn rollback(&mut self) {
        self.stack
            .pop()
            .expect("Internal error: change set stack should never be empty.");
    }

    /// Get an immutable reference the current (latest) checkpoint.
    fn current(&self) -> &Changes {
        self.stack
            .last()
            .expect("Internal error: change set stack should never be empty.")
    }

    /// Get a mutable reference to the current (latest) checkpoint.
    fn current_mut(&mut self) -> &mut Changes {
        self.stack
            .last_mut()
            .expect("Internal error: change set stack should never be empty.")
    }

    /// Try to persist all changes from the changeset.
    ///
    /// If the energy needed for storing extra state is larger than the
    /// `remaining_energy`, then:
    ///  - no changes will be persisted,
    ///  - an [`OutOfEnergy`] error is returned.
    ///
    /// Otherwise, it returns whether the state of the provided
    /// `invoked_contract` was changed.
    ///
    /// **Preconditions:**
    ///  - All contracts, modules, accounts referred must exist in persistence.
    ///  - All amount deltas must be valid (i.e. not cause underflows when added
    ///    to balance).
    pub(crate) fn persist(
        mut self,
        remaining_energy: &mut Energy,
        invoked_contract: ContractAddress,
        persisted_accounts: &mut BTreeMap<AccountAddressEq, Account>,
        persisted_contracts: &mut BTreeMap<ContractAddress, Contract>,
    ) -> Result<bool, InsufficientEnergy> {
        let current = self.current_mut();
        let mut invoked_contract_has_state_changes = false;
        // Persist contract changes and collect the total increase in states sizes.
        let mut collector = v1::trie::SizeCollector::default();
        let mut loader = v1::trie::Loader::new(&[][..]); // An empty loader is fine currently, as we do not use caching in this lib.

        let mut frozen_states: BTreeMap<ContractAddress, trie::PersistentState> = BTreeMap::new();

        // Create frozen versions of all the states, to compute the energy needed.
        for (addr, changes) in current.contracts.iter_mut() {
            if let Some(modified_state) = &mut changes.state {
                frozen_states.insert(*addr, modified_state.freeze(&mut loader, &mut collector));
            }
        }

        // One energy per extra byte of state.
        let energy_for_state_increase = Energy::from(collector.collect());

        // Return an error if out of energy.
        remaining_energy.tick_energy(energy_for_state_increase)?;

        // Then persist all the changes.
        for (addr, changes) in current.contracts.iter_mut() {
            let mut contract = persisted_contracts
                .get_mut(addr)
                .expect("Precondition violation: contract must exist");
            // Update balance.
            if !changes.self_balance_delta.is_zero() {
                contract.self_balance = changes
                    .self_balance_delta
                    .apply_to_balance(changes.self_balance_original)
                    .expect("Precondition violation: amount delta causes underflow");
            }
            // Update module reference.
            if let Some(new_module_ref) = changes.module {
                contract.module_reference = new_module_ref;
            }
            // Update state.
            if changes.state.is_some() {
                if *addr == invoked_contract {
                    invoked_contract_has_state_changes = true;
                }
                // Replace with the frozen state we created earlier.
                contract.state = frozen_states
                    .remove(addr)
                    .expect("Known to exist since we just added it.");
            }
        }
        // Persist account changes.
        for (addr, changes) in current.accounts.iter() {
            let mut account = persisted_accounts
                .get_mut(addr)
                .expect("Precondition violation: account must exist");
            // Update balance.
            if !changes.balance_delta.is_zero() {
                account.balance.total = changes
                    .balance_delta
                    .apply_to_balance(account.balance.total)
                    .expect("Precondition violation: amount delta causes underflow");
            }
        }

        Ok(invoked_contract_has_state_changes)
    }

    /// Traverses the last checkpoint in the changeset and collects the energy
    /// needed to be charged for additional state bytes.
    ///
    /// Returns an [`OutOfEnergy`] error if the energy needed for storing the
    /// extra state is larger than `remaining_energy`.
    ///
    /// Otherwise, it returns whether the state of the provided
    /// `invoked_contract` has changed.
    pub(crate) fn collect_energy_for_state(
        mut self,
        remaining_energy: &mut Energy,
        invoked_contract: ContractAddress,
    ) -> Result<bool, InsufficientEnergy> {
        let mut invoked_contract_has_state_changes = false;
        let mut loader = v1::trie::Loader::new(&[][..]); // An empty loader is fine currently, as we do not use caching in this lib.
        let mut collector = v1::trie::SizeCollector::default();
        for (addr, changes) in self.current_mut().contracts.iter_mut() {
            if let Some(modified_state) = &mut changes.state {
                if *addr == invoked_contract {
                    invoked_contract_has_state_changes = true;
                }
                modified_state.freeze(&mut loader, &mut collector);
            }
        }

        // One energy per extra byte in the state.
        let energy_for_state_increase = Energy::from(collector.collect());

        // Return an error if we run out of energy.
        remaining_energy.tick_energy(energy_for_state_increase)?;

        Ok(invoked_contract_has_state_changes)
    }
}

impl Default for ChangeSet {
    fn default() -> Self { Self::new() }
}

impl AmountDelta {
    /// Create a new [`Self`], with the value `+0`.
    fn new() -> Self { Self::Positive(Amount::zero()) }

    /// Subtract an [`Amount`] from [`Self`].
    fn subtract_amount(self, amount: Amount) -> Self {
        match self {
            Self::Positive(current) => {
                if current >= amount {
                    Self::Positive(current.subtract_micro_ccd(amount.micro_ccd))
                } else {
                    Self::Negative(amount.subtract_micro_ccd(current.micro_ccd))
                }
            }
            Self::Negative(current) => Self::Negative(current.add_micro_ccd(amount.micro_ccd)),
        }
    }

    /// Add an [`Amount`] from [`Self`].
    fn add_amount(self, amount: Amount) -> Self {
        match self {
            Self::Positive(current) => Self::Positive(current.add_micro_ccd(amount.micro_ccd)),
            Self::Negative(current) => {
                if current >= amount {
                    Self::Negative(current.subtract_micro_ccd(amount.micro_ccd))
                } else {
                    Self::Positive(amount.subtract_micro_ccd(current.micro_ccd))
                }
            }
        }
    }

    /// Add two [`Self`] to create a new one.
    fn add_delta(self, delta: AmountDelta) -> Self {
        match delta {
            AmountDelta::Positive(d) => self.add_amount(d),
            AmountDelta::Negative(d) => self.subtract_amount(d),
        }
    }

    /// Whether the [`Self`] is zero (either `+0` or `-0`).
    fn is_zero(&self) -> bool {
        match self {
            AmountDelta::Positive(d) => d.micro_ccd == 0,
            AmountDelta::Negative(d) => d.micro_ccd == 0,
        }
    }

    /// Returns a new balance with the `AmountDelta` applied, or a
    /// [`BalanceError`] error if the change would result in a negative
    /// balance or an overflow.
    fn apply_to_balance(&self, balance: Amount) -> Result<Amount, BalanceError> {
        match self {
            AmountDelta::Positive(d) => balance.checked_add(*d).ok_or(BalanceError::Overflow),
            AmountDelta::Negative(d) => balance.checked_sub(*d).ok_or(BalanceError::Insufficient),
        }
    }
}

impl ContractChanges {
    /// Create a new `Self`. The original balance must be provided, all other
    /// fields take on default values.
    fn new(original_balance: Amount) -> Self {
        Self {
            modification_index:    0,
            self_balance_delta:    AmountDelta::new(),
            self_balance_original: original_balance,
            state:                 None,
            module:                None,
        }
    }

    /// Get the current balance by adding the original balance and the balance
    /// delta.
    ///
    /// **Preconditions:**
    ///  - `balance_delta + original_balance` must be larger than `0`.
    fn current_balance(&self) -> Amount {
        self.self_balance_delta
            .apply_to_balance(self.self_balance_original)
            .expect("Precondition violation: invalid `balance_delta`.")
    }
}

impl AccountChanges {
    /// Get the current balance by adding the original balance and the balance
    /// delta.
    ///
    /// **Preconditions:**
    ///  - `balance_delta + original_balance` must be larger than `0`.
    fn current_balance(&self) -> Amount {
        self.balance_delta
            .apply_to_balance(self.original_balance)
            .expect("Precondition violation: invalid `balance_delta`.")
    }
}

impl From<InsufficientEnergy> for TestConfigurationError {
    fn from(_: InsufficientEnergy) -> Self { Self::OutOfEnergy }
}

#[cfg(test)]
mod tests {
    mod amount_delta {
        use crate::{invocation::types::AmountDelta, Amount};
        #[test]
        fn test() {
            let mut x = AmountDelta::new();
            assert_eq!(x, AmountDelta::Positive(Amount::zero()));

            let one = Amount::from_ccd(1);
            let two = Amount::from_ccd(2);
            let three = Amount::from_ccd(3);
            let five = Amount::from_ccd(5);

            x = x.subtract_amount(one); // -1 CCD
            x = x.subtract_amount(one); // -2 CCD
            assert_eq!(x, AmountDelta::Negative(two));
            x = x.add_amount(five); // +3 CCD
            assert_eq!(x, AmountDelta::Positive(three));
            x = x.subtract_amount(five); // -2 CCD
            assert_eq!(x, AmountDelta::Negative(two));
            x = x.add_amount(two); // 0

            x = x.add_amount(Amount::from_micro_ccd(1)); // 1 mCCD
            assert_eq!(x, AmountDelta::Positive(Amount::from_micro_ccd(1)));
            x = x.subtract_amount(Amount::from_micro_ccd(2)); // -1 mCCD
            assert_eq!(x, AmountDelta::Negative(Amount::from_micro_ccd(1)));
        }
    }
}
