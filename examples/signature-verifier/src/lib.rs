//! # Signature Verifier contract for Ed25519
//!
//! This contract has a single receive function, which verifies a Ed25519
//! signature. It shows off how to use the `crypto_utils` attribute, which gives
//! the function access to cryptographic utility functions from the
//! [`HasCryptoUtils`] trait.
use concordium_std::*;

type State = ();

#[derive(SchemaType, Serialize)]
struct VerificationParameter {
    public_key: PublicKeyEd25519,
    signature:  SignatureEd25519,
    message:    Vec<u8>,
}

#[init(contract = "signature-verifier")]
fn contract_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<State> {
    Ok(())
}

/// Verify a ed25519 signature and return the result as a bool. Expects a
/// [`VerificationParameter`] as the parameter.
#[receive(contract = "signature-verifier", name = "verify", crypto_utils)]
fn contract_receive<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    _host: &impl HasHost<State, StateApiType = S>,
    crypto_utils: &impl HasCryptoUtils,
) -> ReceiveResult<bool> {
    let param: VerificationParameter = ctx.parameter_cursor().get()?;
    let is_valid =
        crypto_utils.verify_ed25519_signature(param.public_key, param.signature, &param.message);
    Ok(is_valid)
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use concordium_std::test_infrastructure::*;

    #[concordium_test]
    #[cfg(not(feature = "crypto-utils"))]
    fn test_crypto() {
        let mut ctx = TestReceiveContext::empty();
        let host = TestHost::new((), TestStateBuilder::new());
        let crypto_utils = TestCryptoUtils::new();

        let param = VerificationParameter {
            public_key: [0; 32],
            signature:  [1; 64],
            message:    vec![2; 100],
        };
        let param_bytes = to_bytes(&param);
        ctx.set_parameter(&param_bytes);

        crypto_utils.setup_verify_ed25519_signature_mock(|_, _, _| true);

        let res = contract_receive(&ctx, &host, &crypto_utils);
        claim_eq!(res, Ok(true))
    }

    // TODO: Add test that uses the crypto-utils feature.
}
