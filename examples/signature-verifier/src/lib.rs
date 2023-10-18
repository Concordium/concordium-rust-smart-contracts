//! # Signature Verifier contract for Ed25519
//!
//! This contract has a single receive function, which verifies a Ed25519
//! signature. It shows off how to use the `crypto_primitives` attribute, which
//! gives the function access to the cryptographic primitives from the
//! [`HasCryptoPrimitives`] trait.
use concordium_std::*;

type State = ();

#[derive(SchemaType, Serialize)]
pub struct VerificationParameter {
    pub public_key: PublicKeyEd25519,
    pub signature:  SignatureEd25519,
    pub message:    Vec<u8>,
}

#[init(contract = "signature-verifier")]
fn contract_init(_ctx: &InitContext, _state_builder: &mut StateBuilder) -> InitResult<State> {
    Ok(())
}

/// Verify a ed25519 signature and return the result as a bool. Expects a
/// [`VerificationParameter`] as the parameter.
#[receive(
    contract = "signature-verifier",
    name = "verify",
    crypto_primitives,
    parameter = "VerificationParameter",
    return_value = "bool"
)]
fn contract_receive(
    ctx: &ReceiveContext,
    _host: &Host<State>,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ReceiveResult<bool> {
    let param: VerificationParameter = ctx.parameter_cursor().get()?;
    let is_valid = crypto_primitives.verify_ed25519_signature(
        param.public_key,
        param.signature,
        &param.message,
    );
    Ok(is_valid)
}
