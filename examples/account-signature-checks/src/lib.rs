#![cfg_attr(not(feature = "std"), no_std)]

//! A basic example showing how to retrieve account keys, and check account
//! signatures.
use concordium_std::*;
use core::fmt::Debug;
const a:u8= 1;

#[derive(Debug, PartialEq, Eq, Reject, Serial, SchemaType)]
enum Error {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Account that we wanted was not present.
    MissingAccount,
    /// Signature data was malformed.
    MalformedData,
}

impl From<CheckAccountSignatureError> for Error {
    fn from(value: CheckAccountSignatureError) -> Self {
        match value {
            CheckAccountSignatureError::MissingAccount => Self::MissingAccount,
            CheckAccountSignatureError::MalformedData => Self::MalformedData,
        }
    }
}

impl From<QueryAccountPublicKeysError> for Error {
    fn from(QueryAccountPublicKeysError: QueryAccountPublicKeysError) -> Self {
        Self::MissingAccount
    }
}

/// We don't need state for this specific demonstration.
#[derive(Serialize)]
struct State {}

/// Init function that creates a new smart contract.
#[init(contract = "account_signature_checks")]
fn init(_ctx: &InitContext, _state_builder: &mut StateBuilder) -> InitResult<State> { Ok(State {}) }

#[derive(Deserial, SchemaType)]
struct CheckParam {
    address: AccountAddress,
    sigs:    AccountSignatures,
    #[concordium(size_length = 4)]
    data:    Vec<u8>,
}

/// View function that checks the signature with account keys on the provided
/// data.
#[receive(
    contract = "account_signature_checks",
    name = "check",
    parameter = "CheckParam",
    error = "Error",
    return_value = "bool"
)]
fn check(ctx: &ReceiveContext, host: &Host<State>) -> Result<bool, Error> {
    let param: CheckParam = ctx.parameter_cursor().get()?;
    let r = host.check_account_signature(param.address, &param.sigs, &param.data)?;
    Ok(r)
}

/// View function that returns the account's public keys.
#[receive(
    contract = "account_signature_checks",
    name = "view_keys",
    parameter = "AccountAddress",
    return_value = "AccountPublicKeys"
)]
fn view_keys(ctx: &ReceiveContext, host: &Host<State>) -> Result<AccountPublicKeys, Error> {
    let param: AccountAddress = ctx.parameter_cursor().get()?;
    let pk = host.account_public_keys(param)?;
    Ok(pk)
}
