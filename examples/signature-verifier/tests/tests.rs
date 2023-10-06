//! Tests for the signature-verifier contract.
use concordium_smart_contract_testing::*;
use concordium_std::{PublicKeyEd25519, SignatureEd25519};
use signature_verifier::*;

const ALICE: AccountAddress = AccountAddress([0u8; 32]);
const ALICE_ADDR: Address = Address::Account(ALICE);
const SIGNER: Signer = Signer::with_one_key();

/// Tests that the signature verifier contract returns true when the signature
/// is valid.
#[test]
fn test_signature_check() {
    let mut chain = Chain::new();

    // Create an account.
    chain.create_account(Account::new(ALICE, Amount::from_ccd(1000)));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists.");
    let deployment = chain.module_deploy_v1(SIGNER, ALICE, module).expect("Module deploys.");

    // Initialize the signature verifier contract.
    let init = chain
        .contract_init(SIGNER, ALICE, Energy::from(10_000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_signature-verifier".to_string()),
            param:     OwnedParameter::empty(),
        })
        .expect("Initialize signature verifier contract");

    // Construct a parameter with an invalid signature.
    let parameter_invalid = VerificationParameter {
        public_key: PublicKeyEd25519([0; 32]),
        signature:  SignatureEd25519([1; 64]),
        message:    vec![2; 100],
    };

    // Call the contract with the invalid signature.
    let update_invalid = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      init.contract_address,
            receive_name: OwnedReceiveName::new_unchecked("signature-verifier.verify".to_string()),
            message:      OwnedParameter::from_serial(&parameter_invalid)
                .expect("Parameter has valid size."),
        })
        .expect("Call signature verifier contract with an invalid signature.");
    // Check that it returns `false`.
    let rv: bool = from_bytes(&update_invalid.return_value).expect("Deserializing bool");
    assert_eq!(rv, false);

    // Construct a parameter with a valid signature.
    let parameter_valid = VerificationParameter {
        public_key: PublicKeyEd25519([
            53, 162, 168, 229, 46, 250, 217, 117, 219, 246, 88, 14, 119, 52, 228, 242, 73, 234,
            165, 234, 138, 118, 62, 147, 74, 134, 113, 205, 126, 68, 100, 153,
        ]),
        signature:  SignatureEd25519([
            170, 242, 191, 224, 247, 247, 70, 49, 133, 3, 112, 66, 33, 24, 243, 14, 135, 135, 197,
            113, 122, 74, 21, 82, 122, 94, 29, 15, 252, 121, 27, 102, 59, 21, 9, 177, 33, 2, 46,
            242, 96, 134, 179, 120, 89, 0, 29, 9, 100, 38, 116, 250, 59, 226, 1, 247, 217, 220, 39,
            8, 245, 230, 236, 2,
        ]),
        message:    b"Concordium".to_vec(),
    };

    // Call the contract with the valid signature.
    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      init.contract_address,
            receive_name: OwnedReceiveName::new_unchecked("signature-verifier.verify".to_string()),
            message:      OwnedParameter::from_serial(&parameter_valid)
                .expect("Parameter has valid size."),
        })
        .expect("Call signature verifier contract with a valid signature.");
    // Check that it returns `true`.
    let rv: bool = from_bytes(&update.return_value).expect("Deserializing bool");
    assert_eq!(rv, true);
}
