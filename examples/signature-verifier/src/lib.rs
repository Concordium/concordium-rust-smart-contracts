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
#[receive(
    contract = "signature-verifier",
    name = "verify",
    crypto_utils,
    parameter = "VerificationParameter",
    return_value = "bool"
)]
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
    fn test_receive_with_mocks() {
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

    #[concordium_test]
    #[cfg(feature = "crypto-utils")]
    fn test_receive() {
        let mut ctx = TestReceiveContext::empty();
        let host = TestHost::new((), TestStateBuilder::new());
        let crypto_utils = TestCryptoUtils::new();

        let param = VerificationParameter {
            public_key: [
                53, 162, 168, 229, 46, 250, 217, 117, 219, 246, 88, 14, 119, 52, 228, 242, 73, 234,
                165, 234, 138, 118, 62, 147, 74, 134, 113, 205, 126, 68, 100, 153,
            ],
            signature:  [
                170, 242, 191, 224, 247, 247, 70, 49, 133, 3, 112, 66, 33, 24, 243, 14, 135, 135,
                197, 113, 122, 74, 21, 82, 122, 94, 29, 15, 252, 121, 27, 102, 59, 21, 9, 177, 33,
                2, 46, 242, 96, 134, 179, 120, 89, 0, 29, 9, 100, 38, 116, 250, 59, 226, 1, 247,
                217, 220, 39, 8, 245, 230, 236, 2,
            ],
            message:    b"Concordium".to_vec(),
        };
        let param_bytes = to_bytes(&param);
        ctx.set_parameter(&param_bytes);

        let res = contract_receive(&ctx, &host, &crypto_utils);
        claim_eq!(res, Ok(true))
    }
}
