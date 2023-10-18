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
 * will be forwarded to the account address held in the state. Otherwise,
 * the receive function will reject with `ContractError::NotLocalSender`.
 */
#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;

type State = AccountAddress;
pub const LOCAL_COUNTRY: [u8; 2] = *b"DK";

#[derive(Serialize, Reject, PartialEq, Eq, Debug, SchemaType)]
pub enum ContractError {
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
#[init(contract = "transfer-policy-check", parameter = "AccountAddress")]
fn init(ctx: &InitContext, _state_builder: &mut StateBuilder) -> InitResult<State> {
    let parameter: AccountAddress = ctx.parameter_cursor().get()?;
    Ok(parameter)
}

/// Forward the `amount` to the account defined in the state iff all sender
/// policies have the country of residence in `LOCAL_COUNTRY`.
#[receive(contract = "transfer-policy-check", name = "receive", payable, error = "ContractError")]
fn receive(ctx: &ReceiveContext, host: &Host<State>, amount: Amount) -> Result<(), ContractError> {
    for policy in ctx.policies() {
        for (tag, value) in policy.attributes() {
            if tag == attributes::COUNTRY_OF_RESIDENCE && value.as_ref() != &LOCAL_COUNTRY[..] {
                return Err(ContractError::NotLocalSender);
            }
        }
    }
    Ok(host.invoke_transfer(host.state(), amount)?)
}
