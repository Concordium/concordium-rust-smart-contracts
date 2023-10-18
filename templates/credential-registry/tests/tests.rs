//! Tests for the credential registry contract.
use concordium_cis2::*;
use concordium_smart_contract_testing::*;
use concordium_std::{PublicKeyEd25519, SignatureEd25519, Timestamp};
use {{crate_name}}::*;

/// Constants for tests
const SIGNER: Signer = Signer::with_one_key();
pub const ISSUER_ACCOUNT: AccountAddress = AccountAddress([0u8; 32]);
pub const ISSUER_ADDRESS: Address = Address::Account(ISSUER_ACCOUNT);
pub const ISSUER_METADATA_URL: &str = "https://example-university.com/university.json";
pub const CREDENTIAL_METADATA_URL: &str =
    "https://example-university.com/diplomas/university-vc-metadata.json";
pub const CREDENTIAL_TYPE: &str = "UniversityDegreeCredential";
pub const CREDENTIAL_SCHEMA_URL: &str =
    "https://credentials-schemas.com/JsonSchema2023-education-certificate.json";
// Seed: 2FEE333FAD122A45AAB7BEB3228FA7858C48B551EA8EBC49D2D56E2BA22049FF
pub const PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([
    172, 5, 96, 236, 139, 208, 146, 88, 124, 42, 62, 124, 86, 108, 35, 242, 32, 11, 7, 48, 193, 61,
    177, 220, 104, 169, 145, 4, 8, 1, 236, 112,
]);
pub const SIGNATURE: SignatureEd25519 = SignatureEd25519([
    254, 138, 58, 131, 209, 45, 191, 52, 98, 228, 26, 234, 155, 245, 244, 226, 0, 153, 104, 111,
    201, 136, 243, 167, 251, 116, 110, 206, 172, 223, 41, 180, 90, 22, 63, 43, 157, 129, 226, 75,
    49, 33, 155, 76, 160, 133, 127, 146, 150, 80, 199, 201, 80, 98, 179, 43, 46, 46, 211, 222, 185,
    216, 12, 4,
]);

/// Test initialization of the contract.
#[test]
fn test_init() {
    let (_chain, init) = setup();

    let schema = get_credential_schema();

    let events = init
        .events
        .iter()
        .map(|e| e.parse().expect("Parse event"))
        .collect::<Vec<CredentialEvent>>();

    {% if revocable_by_others %}assert_eq!(events.len(), 3);{% else %}assert_eq!(events.len(), 2);{% endif %}
    assert_eq!(
        events[0],
        CredentialEvent::IssuerMetadata(issuer_metadata()),
        "Incorrect issuer metadata event logged"
    );{% if revocable_by_others %}
    assert_eq!(
        events[1],
        CredentialEvent::RevocationKey(RevocationKeyEvent {
            key:    PUBLIC_KEY,
            action: RevocationKeyAction::Register,
        }),
        "Incorrect revocation key event logged"
    );{% endif %}
    assert_eq!(
        {% if revocable_by_others %}events[2],{% else %}events[1],{% endif %}
        CredentialEvent::Schema(CredentialSchemaRefEvent {
            credential_type: schema.0,
            schema_ref:      schema.1,
        }),
        "Incorrect schema event logged"
    );
}

/// Test register credential.
#[test]
fn test_register_credential() {
    let (mut chain, init) = setup();

    let update = register_credential(&mut chain, init.contract_address);

    let credential_status = get_credential_status(&mut chain, init.contract_address, PUBLIC_KEY);
    assert_eq!(credential_status, CredentialStatus::Active, "Credential is not active");

    // Check that the correct register event was produced.
    let events = update
        .events()
        .flat_map(|(_contract, events)| events.iter().map(|e| e.parse().expect("Parsing event")))
        .collect::<Vec<CredentialEvent>>();

    assert_eq!(events, [CredentialEvent::Register(CredentialEventData {
        holder_id:       PUBLIC_KEY,
        schema_ref:      SchemaRef {
            schema_ref: MetadataUrl {
                url:  CREDENTIAL_SCHEMA_URL.to_string(),
                hash: None,
            },
        },
        credential_type: CredentialType {
            credential_type: CREDENTIAL_TYPE.to_string(),
        },
        metadata_url:    MetadataUrl {
            url:  CREDENTIAL_METADATA_URL.into(),
            hash: None,
        },
    })]);
}

/// Test the revoke credential entrypoint, when the holder revokes the
/// credential.
#[test]
fn test_revoke_by_holder() {
    let (mut chain, init) = setup();
    // Register a credential that is revocable by the holder.
    register_credential(&mut chain, init.contract_address);

    let revocation_reason: Reason = "Just because".to_string().into();

    let update = revoke_credential(&mut chain, init.contract_address, &revocation_reason);

    // Check the credential status.
    let credential_status = get_credential_status(&mut chain, init.contract_address, PUBLIC_KEY);
    assert_eq!(credential_status, CredentialStatus::Revoked, "Credential is not revoked");

    // Check that the correct revoke event was produced.
    let events = update
        .events()
        .flat_map(|(_contract, events)| events.iter().map(|e| e.parse().expect("Parsing event")))
        .collect::<Vec<CredentialEvent>>();
    assert_eq!(events, [CredentialEvent::Revoke(RevokeCredentialEvent {
        holder_id: PUBLIC_KEY,
        revoker:   Revoker::Holder,
        reason:    Some(revocation_reason),
    })]);
}{% if restorable %}

/// Test the restore credential entrypoint.
#[test]
fn test_contract_restore_credential() {
    let (mut chain, init) = setup();

    // Register a credential.
    register_credential(&mut chain, init.contract_address);

    // Revoke the credential.
    let revocation_reason: Reason = "Just because".to_string().into();
    revoke_credential(&mut chain, init.contract_address, &revocation_reason);

    // Check that the credential status is revoked.
    let credential_status = get_credential_status(&mut chain, init.contract_address, PUBLIC_KEY);
    assert_eq!(credential_status, CredentialStatus::Revoked, "Credential is not revoked");

    // Restore the credential.
    let parameter = RestoreCredentialIssuerParam {
        credential_id: PUBLIC_KEY,
        reason:        None,
    };

    let update = chain
        .contract_update(
            SIGNER,
            ISSUER_ACCOUNT,
            ISSUER_ADDRESS,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      init.contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "{{crate_name}}.restoreCredential".to_string(),
                ),
                message:      OwnedParameter::from_serial(&parameter)
                    .expect("Parameter has valid size."),
            },
        )
        .expect("Restore credential call succeeds.");

    // Check that the credential status is active again.
    let credential_status = get_credential_status(&mut chain, init.contract_address, PUBLIC_KEY);
    assert_eq!(credential_status, CredentialStatus::Active, "Credential is not active");

    // Check that the restore event was produced.
    let events = update
        .events()
        .flat_map(|(_contract, events)| events.iter().map(|e| e.parse().expect("Parsing event")))
        .collect::<Vec<CredentialEvent>>();
    assert_eq!(events, [CredentialEvent::Restore(RestoreCredentialEvent {
        holder_id: PUBLIC_KEY,
        reason:    None,
    })]);
}{% endif %}

// Helpers:

pub fn issuer_metadata() -> MetadataUrl {
    MetadataUrl {
        url:  ISSUER_METADATA_URL.to_string(),
        hash: None,
    }
}

pub fn get_credential_schema() -> (CredentialType, SchemaRef) {
    (
        CredentialType {
            credential_type: CREDENTIAL_TYPE.to_string(),
        },
        SchemaRef {
            schema_ref: MetadataUrl {
                url:  CREDENTIAL_SCHEMA_URL.to_string(),
                hash: None,
            },
        },
    )
}

/// Helper that registers a credential and returns the update type.
fn register_credential(
    chain: &mut Chain,
    contract_address: ContractAddress,
) -> ContractInvokeSuccess {
    let parameter = RegisterCredentialParam {
        credential_info: CredentialInfo {
            holder_id:        PUBLIC_KEY,
            holder_revocable: true,
            valid_from:       Timestamp::from_timestamp_millis(0),
            valid_until:      None,
            metadata_url:     MetadataUrl {
                url:  CREDENTIAL_METADATA_URL.to_string(),
                hash: None,
            },
        },
        auxiliary_data:  Vec::new(),
    };

    chain
        .contract_update(
            SIGNER,
            ISSUER_ACCOUNT,
            ISSUER_ADDRESS,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "{{crate_name}}.registerCredential".to_string(),
                ),
                message:      OwnedParameter::from_serial(&parameter)
                    .expect("Parameter has valid size."),
            },
        )
        .expect("Successfully registers credential")
}

/// Helper that revokes the credential.
fn revoke_credential(
    chain: &mut Chain,
    contract_address: ContractAddress,
    revocation_reason: &Reason,
) -> ContractInvokeSuccess {
    // Create signing data.
    let signing_data = SigningData {
        contract_address,
        entry_point: OwnedEntrypointName::new_unchecked("revokeCredentialHolder".into()),
        nonce: 0,
        timestamp: Timestamp::from_timestamp_millis(10000000000),
    };
    // Create input parameters for revocation.
    let revoke_param = RevokeCredentialHolderParam {
        signature: SIGNATURE,
        data:      RevocationDataHolder {
            credential_id: PUBLIC_KEY,
            signing_data,
            reason: Some(revocation_reason.clone()),
        },
    };
    // Call the revoke credential entrypoint.
    let update = chain
        .contract_update(
            SIGNER,
            ISSUER_ACCOUNT,
            ISSUER_ADDRESS,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "{{crate_name}}.revokeCredentialHolder".to_string(),
                ),
                message:      OwnedParameter::from_serial(&revoke_param)
                    .expect("Parameter has valid size."),
            },
        )
        .expect("Revoke credential call succeeds.");
    update
}

/// Helper for looking up the status of a credential.
fn get_credential_status(
    chain: &mut Chain,
    contract_address: ContractAddress,
    key: PublicKeyEd25519,
) -> CredentialStatus {
    let credential_status = chain
        .contract_invoke(
            ISSUER_ACCOUNT,
            ISSUER_ADDRESS,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "{{crate_name}}.credentialStatus".to_string(),
                ),
                message:      OwnedParameter::from_serial(&key).expect("Parameter has valid size."),
            },
        )
        .expect("Credential Status call succeeds.");

    credential_status.parse_return_value().expect("Parse credential status")
}

/// Setup chain and contract.
fn setup() -> (Chain, ContractInitSuccess) {
    let mut chain = Chain::new();

    chain.create_account(Account::new(ISSUER_ACCOUNT, Amount::from_ccd(10000)));

    let module = module_load_v1("./concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain
        .module_deploy_v1(SIGNER, ISSUER_ACCOUNT, module)
        .expect("Module deploys successfully");

    let schema = get_credential_schema();
    let init_params = InitParams {
        issuer_metadata: issuer_metadata(),
        issuer_account:  ISSUER_ACCOUNT.into(),
        issuer_key:      PUBLIC_KEY,{% if revocable_by_others %}
        revocation_keys: vec![PUBLIC_KEY],{% endif %}
        credential_type: schema.0.clone(),
        schema:          schema.1.clone(),
    };

    let init = chain
        .contract_init(SIGNER, ISSUER_ACCOUNT, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_{{crate_name}}".to_string()),
            param:     OwnedParameter::from_serial(&init_params)
                .expect("Parameter has valid size."),
        })
        .expect("Contract initializes successfully");
    (chain, init)
}
