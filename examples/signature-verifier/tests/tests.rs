//! Tests for the signature-verifier contract.
use concordium_smart_contract_testing::*;
use concordium_std::{PublicKeyEd25519, SignatureEd25519};
use signature_verifier::*;
use std::str::FromStr;

const ALICE: AccountAddress = account_address!("00000000000000000000000000000000");
const ALICE_ADDR: Address = Address::Account(ALICE);
const SIGNER: Signer = Signer::with_one_key();

/// Tests that the signature verifier contract returns true when the signature
/// is valid. The signature is generated outside this test case
/// (e.g. with https://cyphr.me/ed25519_tool/ed.html).
#[test]
fn test_outside_signature_check() {
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
    // Check that the signature does NOT verify.
    let rv: bool = update_invalid.parse_return_value().expect("Deserializing bool");
    assert!(!rv, "Signature verification should fail.");

    // Construct a parameter with a valid signature.
    let parameter_valid = VerificationParameter {
        public_key: PublicKeyEd25519::from_str("35a2a8e52efad975dbf6580e7734e4f249eaa5ea8a763e934a8671cd7e446499").expect("Valid public key"),
        signature:  SignatureEd25519::from_str("aaf2bfe0f7f74631850370422118f30e8787c5717a4a15527a5e1d0ffc791b663b1509b121022ef26086b37859001d09642674fa3be201f7d9dc2708f5e6ec02").expect("Valid signature"),
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
    // Check that the signature verifies.
    let rv: bool = update.parse_return_value().expect("Deserializing bool");
    assert!(rv, "Signature checking failed.");
}

/// Tests that the signature verifier contract returns true when the signature
/// is valid. The signature is generated in the test case.
#[test]
fn test_inside_signature_check() {
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

    use ed25519_dalek::{Signer, SigningKey};

    let rng = &mut rand::thread_rng();

    // Construct message, verifying_key, and signature.
    let message: &[u8] = b"Concordium";
    let signing_key = SigningKey::generate(rng);
    let verifying_key = signing_key.verifying_key();
    let signature = signing_key.sign(&message);

    // Construct a parameter with an invalid signature.
    let parameter_invalid = VerificationParameter {
        public_key: PublicKeyEd25519(verifying_key.to_bytes()),
        signature:  SignatureEd25519(signature.to_bytes()),
        message:    b"wrong_message".to_vec(),
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

    // Check that the signature does NOT verify.
    let rv: bool = update_invalid.parse_return_value().expect("Deserializing bool");
    assert!(!rv, "Signature verification should fail.");

    // Construct a parameter with a valid signature.
    let parameter_valid = VerificationParameter {
        public_key: PublicKeyEd25519(verifying_key.to_bytes()),
        signature:  SignatureEd25519(signature.to_bytes()),
        message:    message.to_vec(),
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

    // Check that the signature verifies.
    let rv: bool = update.parse_return_value().expect("Deserializing bool");
    assert!(rv, "Signature checking failed.");
}
