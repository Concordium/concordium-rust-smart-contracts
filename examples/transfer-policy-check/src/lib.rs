/*! A contract that showcases how to use policies.
 *
 * In particular, it can act as a filter for transfers to an account,
 * where the filter requires the sender to be from a specific country.
 *
 * The contract is initialised with `init`, in which an account address is
 * provided, which will be set as the state.
 *
 * The contract has a single receive entrypoint, `receive`,
 * which checks whether all sender policies have their country of residence
 * attribute set to `LOCAL_COUNTRY`. If that is the case, then the `amount`
 * will be forwarded to the account address held in the state. OTherwise,
 * the receive function will reject with `ContractError::NotLocalSender`.
 */
use concordium_std::*;

type State = AccountAddress;
const LOCAL_COUNTRY: [u8; 2] = *b"DK";

#[derive(Reject, PartialEq, Eq, Debug)]
enum ContractError {
    NotLocalSender,
    TransferErrorAmountTooLarge,
    TransferErrorAccountMissing,
}

impl From<TransferError> for ContractError {
    fn from(e: TransferError) -> Self {
        match e {
            TransferError::AmountTooLarge => Self::TransferErrorAmountTooLarge,
            TransferError::MissingAccount => Self::TransferErrorAccountMissing,
        }
    }
}

/// Set the account address that `receive` will forward CCD to.
#[init(contract = "polices", parameter = "AccountAddress")]
fn init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<()> {
    Ok(ctx.parameter_cursor().get()?)
}

/// Forward the `amount` to the account defined in the state iff all sender
/// policies have the country of residence in `LOCAL_COUNTRY`.
#[receive(contract = "transfer-policy-check", name = "receive", payable)]
fn receive<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State, StateApiType = S>,
    amount: Amount,
) -> Result<(), ContractError> {
    for policy in ctx.policies() {
        if !policy.attributes().any(|(tag, val)| {
            tag == attributes::COUNTRY_OF_RESIDENCE && val.as_ref() == &LOCAL_COUNTRY[..]
        }) {
            return Err(ContractError::NotLocalSender);
        }
    }
    Ok(host.invoke_transfer(host.state(), amount)?)
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use concordium_std::test_infrastructure::*;

    const ACCOUNT_0: AccountAddress = AccountAddress([0u8; 32]);

    #[concordium_test]
    fn receive_with_correct_policies() {
        let mut ctx = TestReceiveContext::empty();
        ctx.push_policy(Policy {
            identity_provider: 0,
            created_at:        Timestamp::from_timestamp_millis(0),
            valid_to:          Timestamp::from_timestamp_millis(1000),
            items:             vec![(attributes::COUNTRY_OF_RESIDENCE, LOCAL_COUNTRY.into())],
        });
        ctx.push_policy(Policy {
            identity_provider: 0,
            created_at:        Timestamp::from_timestamp_millis(0),
            valid_to:          Timestamp::from_timestamp_millis(1000),
            items:             vec![(attributes::COUNTRY_OF_RESIDENCE, LOCAL_COUNTRY.into())],
        });

        let state = ACCOUNT_0;
        let state_builder = TestStateBuilder::new();
        let mut host = TestHost::new(state, state_builder);
        let transfer_amount = Amount::from_micro_ccd(10);
        host.set_self_balance(transfer_amount);
        let res = receive(&ctx, &host, transfer_amount);
        assert!(res.is_ok());
        assert_eq!(host.get_transfers(), vec![(ACCOUNT_0, transfer_amount)]);
    }

    #[concordium_test]
    fn receive_with_incorrect_policies() {
        let mut ctx = TestReceiveContext::empty();
        ctx.push_policy(Policy {
            identity_provider: 0,
            created_at:        Timestamp::from_timestamp_millis(0),
            valid_to:          Timestamp::from_timestamp_millis(1000),
            items:             vec![(attributes::COUNTRY_OF_RESIDENCE, LOCAL_COUNTRY.into())],
        });
        ctx.push_policy(Policy {
            identity_provider: 0,
            created_at:        Timestamp::from_timestamp_millis(0),
            valid_to:          Timestamp::from_timestamp_millis(1000),
            items:             vec![(
                attributes::COUNTRY_OF_RESIDENCE,
                b"NOT_LOCAL_COUNTRY".into(), /* Chose an invalid country to avoid conflicts
                                              * with valid settings of `LOCAL_COUNTRY`. */
            )],
        });

        let state = ACCOUNT_0;
        let state_builder = TestStateBuilder::new();
        let mut host = TestHost::new(state, state_builder);
        let transfer_amount = Amount::from_micro_ccd(10);
        host.set_self_balance(transfer_amount);
        let res = receive(&ctx, &host, transfer_amount);
        assert_eq!(res, Err(ContractError::NotLocalSender));
    }
}
