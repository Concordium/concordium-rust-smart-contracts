//! # A Concordium V1 smart contract
use concordium_std::*;
use core::fmt::Debug;

/// Your smart contract state.
#[derive(Serial, DeserialWithState, SchemaType, StateClone)]
#[concordium(state_parameter = "S")]
pub struct State<S> {
    balances: StateMap<Address, Amount, S>,
    lock : bool,
}

/// Your smart contract errors.
#[derive(Debug, PartialEq, Eq, Reject, Serial, SchemaType)]
enum Error {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParamsError,
    WithdrawWithoutFunds,
    CallError,
    TransferError,
}

impl<T> From<CallContractError<T>> for Error {
    fn from(_cce: CallContractError<T>) -> Self { Self::CallError }
}

/// Mapping errors related to contract invocations to Error.
impl From<TransferError> for Error {
    fn from(_te: TransferError) -> Self { Self::TransferError }
}

/// Init function that creates a new smart contract.
#[init(contract = "reentrancy")]
fn init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    let state = State {
        balances: state_builder.new_map(),
        lock: false
    };
    Ok(state)
}

#[receive(
    contract = "reentrancy",
    name = "reentrant_withdraw",
    parameter = "OwnedEntrypointName",
    error = "Error",
    mutable
)]
fn reentrant_withdraw<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(), Error> {
    ensure!(!host.state().lock, Error::CallError);
    host.state_mut().lock = true;
    let sender = ctx.sender();
    // Get balance for the sender, or reject if the sender is not found or the
    // balance is zero.
    let sender_balance = match host.state().balances.get(&sender) {
        Some(bal) if *bal > Amount::zero() => *bal,
        _ => return Err(Error::WithdrawWithoutFunds),
    };

    {
        // Transfer the amount to the sender or call an entrypoint, if it's a contract.
        match sender {
            Address::Account(acc) => host.invoke_transfer(&acc, sender_balance)?,
            Address::Contract(addr) => {
                let entrypoint: OwnedEntrypointName = ctx.parameter_cursor().get()?;
                // At this point we giving the control out to an unknown smart contract.
                // This contract can call this entry point again multiple times before the rest
                // of the code is reached.
                host.invoke_contract(
                    &addr,
                    &Parameter(&[]),
                    entrypoint.as_entrypoint_name(),
                    sender_balance,
                )?;
            }
        };
    }

    // Reset the sender's balance to zero.
    // This code is reached only after transfering CCD back/calling an
    // external contract.
    if let Some(mut v) = host.state().balances.get_mut(&sender) {
        *v = Amount::zero();
    }
    host.state_mut().lock = false;
    Ok(())
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    const AMOUNT: Amount = Amount::from_micro_ccd(1);
    const INITIAL_BALANCE: Amount = Amount::from_micro_ccd(2);
    const CONTRACT_ADDRESS: ContractAddress = ContractAddress {
        index:    0,
        subindex: 0,
    };

    fn initialize_data<S: HasStateApi>(state_builder: &mut StateBuilder<S>) -> State<S> {
        let mut balances = state_builder.new_map();
        balances.insert(
            Address::Contract(ContractAddress {
                index:    0,
                subindex: 0,
            }),
            AMOUNT,
        );
        State {
            balances,
            lock: false
        }
    }

    /// Test reentracy behaviour of the contract.
    /// Calling `reentrant_withdraw` results in a call to an external contract
    /// that calls back the original contract. We emulate this behaviour
    /// using a mock entrypoint.
    #[concordium_test]
    fn test_reentrant_withdraw() {
        let mut ctx = TestReceiveContext::empty();

        ctx.set_sender(Address::Contract(ContractAddress {
            index:    0,
            subindex: 0,
        }));

        let mut state_builder = TestStateBuilder::new();

        // Initializing state
        let initial_state = initialize_data(&mut state_builder);

        let entry_point = OwnedEntrypointName::new_unchecked("reentrant_withdraw".into());
        let parameter_bytes = to_bytes(&entry_point);
        ctx.set_parameter(&parameter_bytes);

        let mut host = TestHost::new(initial_state, state_builder);

        host.set_self_balance(INITIAL_BALANCE);

        // Set up a mock entrypoint that calls back to our contract
        host.setup_mock_entrypoint(
            CONTRACT_ADDRESS,
            OwnedEntrypointName::new_unchecked("reentrant_withdraw".to_string()),
            MockFn::new_v1(|_parameter, _amount, balance, state: &mut State<_>| {
                // We cannot make another invoke inside this mock, but we have access to the
                // `balance` which is the balance of the contract making this
                // invoke. So we can simulate invoking withdraw by subtracting
                // the sender's amount stored in the contract state from the balance.

                let b = state.balances.get_mut(&Address::Contract(CONTRACT_ADDRESS));

                let mut sender_balance = match b {
                    Some(bal) if *bal > Amount::zero() => bal,
                    _ => fail!("Insufficent funds"),
                };

                // Emulate withdraw by subtracting the sender's balance.
                *balance -= *sender_balance;

                // Reset the sender's balance to zero.
                *sender_balance = Amount::zero();

                let state_modified = true;
                Ok((state_modified, ()))
            }),
        );
        // Call the contract function.
        reentrant_withdraw(&ctx, &mut host).expect_report("Withdraw call failed");

        let resulting_balance = host.self_balance();
        let expected_balance = INITIAL_BALANCE - AMOUNT;

        claim_eq!(
            resulting_balance,
            expected_balance,
            "Incorrect balance: expected {:?}, found: {:?}",
            expected_balance,
            resulting_balance
        );
    }
}
