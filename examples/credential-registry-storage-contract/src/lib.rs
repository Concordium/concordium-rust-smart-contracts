//! The contract is used for storing verifiable credentials for the Web3Id
//! infrastructure. The contract stores encrypted credential secrets with some
//! metadata associated with them. The state contains a simple key-value store
//! where each public key can store its associated encrypted credential so that
//! the credential can be recovered by off-chain tools. The `keys` for the store
//! are the Ed25519 public keys and the `values` are the `metadata +
//! credential_secrets`. The metadata associated with the credential contains
//! information needed for decoding the encrypted credential secret. Only if an
//! off-chain tool has access to the private key (associated with the public
//! key), it can decode the credential secrets in this smart contract
//! (credential secrets cannot be decoded by third parties to preserve privacy).
//! To enter credentials into this contract, only the associated private key to
//! the public key can authorize the creation of an entry in this smart contract
//! for its key. To authorize the entry the associated private key to the public
//! key signs its metadata/credential_secret that it wants to store. This
//! ensures that entries are generated/authorized by the public/private key pair
//! that they are associated with. The entries in this contract are immutable
//! and cannot be updated anymore once stored in this contract. Each
//! public/private key pair can authorize/generate up to one entry in this
//! contract.
#![cfg_attr(not(feature = "std"), no_std)]

use concordium_std::*;

/// Metadata is a string of two bytes that contain information needed for
/// decoding the credentials.
#[derive(Serial, SchemaType, Clone, Copy, Deserial, PartialEq)]
struct Metadata([u8; 2]);

#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct CredentialState<S: HasStateApi> {
    /// Metadata associated with the credential.
    metadata:          Metadata,
    /// The `credential_secret` stored in this contract.
    credential_secret: StateBox<Vec<u8>, S>,
}

/// The contract state.
#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S: HasStateApi> {
    /// All verifiable credentials.
    credential_registry: StateMap<PublicKeyEd25519, CredentialState<S>, S>,
}

// Function for creating the contract state.
impl<S: HasStateApi> State<S> {
    /// Creates a new state.
    fn empty(state_builder: &mut StateBuilder<S>) -> Self {
        State {
            credential_registry: state_builder.new_map(),
        }
    }
}

// Errors

/// The custom errors the contract can produce.
#[derive(Serialize, PartialEq, Eq, Reject, SchemaType, Debug)]
enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Failed logging: Log is full.
    LogFull,
    /// Failed logging: Log is malformed.
    LogMalformed,
    /// Failed registering a credential: Another credential was already
    /// registered for the given public key.
    CredentialAlreadyRegisteredForGivenPublicKey,
    /// Failed signature verification: Invalid signature.
    WrongSignature,
    /// Failed signature verification: Signature was intended for a different
    /// contract.
    WrongContract,
    /// Failed signature verification: Signature was intended for a different
    /// entry_point.
    WrongEntryPoint,
    /// Failed signature verification: Signature is expired.
    Expired,
}

type ContractResult<A> = Result<A, CustomContractError>;

/// Mapping the logging errors to CustomContractError.
impl From<LogError> for CustomContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

/// Credential state that is used as the input parameter or the return value for
/// the `store/view` contract functions. It contains the metadata and the
/// credential_secret.
#[derive(Serialize, SchemaType, PartialEq)]
struct SimpleCredentialState {
    /// Metadata associated with the credential.
    metadata:          Metadata,
    /// The credential_secret.
    credential_secret: Vec<u8>,
}

/// The CredentialRegisteredEvent is logged when the `store` function is
/// invoked.
#[derive(Serialize, SchemaType)]
pub struct CredentialRegisteredEvent {
    /// Public_key associated with the stored credential.
    public_key: PublicKeyEd25519,
}

/// Tagged event to be serialized for the event log.
#[derive(SchemaType, Serialize)]
pub enum Event {
    CredentialRegistered(CredentialRegisteredEvent),
}

// Contract functions

/// Initialize a new contract instance.
#[init(contract = "credential-registry-storage", event = "Event")]
fn contract_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    Ok(State::empty(state_builder))
}

/// View the registered credential data.
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "credential-registry-storage",
    name = "view",
    parameter = "PublicKeyEd25519",
    return_value = "SimpleCredentialState",
    error = "CustomContractError"
)]
fn view<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<Option<SimpleCredentialState>> {
    let public_key: PublicKeyEd25519 = ctx.parameter_cursor().get()?;

    Ok(host.state().credential_registry.get(&public_key).map(|credential_state| {
        SimpleCredentialState {
            metadata:          credential_state.metadata,
            credential_secret: credential_state.credential_secret.clone(),
        }
    }))
}

/// Part of the parameter type for the contract function `store`.
/// Specifies the message that is signed.
#[derive(SchemaType, Serialize)]
struct SignedMessage {
    /// The contract_address that the signature is intended for.
    contract_address:  ContractAddress,
    /// A timestamp to make signatures expire.
    timestamp:         Timestamp,
    /// The entry_point that the signature is intended for.
    entry_point:       OwnedEntrypointName,
    /// Metadata associated with the credential.
    metadata:          Metadata,
    /// The serialized credential_secret.
    #[concordium(size_length = 2)]
    credential_secret: Vec<u8>,
}

/// The parameter type for the contract function `store`.
/// Takes a signature, the public_key(signer), and the message that was signed.
#[derive(Serialize, SchemaType)]
pub struct StoreParam {
    /// Signature.
    signature:  SignatureEd25519,
    /// PublicKeyEd25519 that created the above signature.
    public_key: PublicKeyEd25519,
    /// Message that was signed.
    message:    SignedMessage,
}

#[derive(Serialize)]
pub struct PartialStoreParam {
    /// Signature.
    signature:  SignatureEd25519,
    /// PublicKeyEd25519 that created the above signature.
    public_key: PublicKeyEd25519,
}

/// Store credential data.
/// It rejects if:
/// - It fails to parse the parameter.
/// - The signature was intended for a different contract.
/// - The signature was intended for a different `entry_point`.
/// - The signature is expired.
/// - The signature can not be validated.
/// - A credential is already registered for the given `public_key`.
/// - Fails to log event.
#[receive(
    contract = "credential-registry-storage",
    name = "store",
    parameter = "StoreParam",
    error = "CustomContractError",
    crypto_primitives,
    enable_logger,
    mutable
)]
fn store<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<()> {
    // Parse the parameter.
    let mut cursor = ctx.parameter_cursor();
    // The input parameter is `StoreParam` but we only read the initial part of it
    // with `PartialStoreParam`. I.e. we read the `signature` and the
    // `public_key`, but not the `message` here.
    let param: PartialStoreParam = cursor.get()?;

    // We read in the `message` now. `(cursor.size() - cursor.cursor_position()` is
    // the length of the message in bytes.
    let mut message_bytes = vec![0; (cursor.size() - cursor.cursor_position()) as usize];

    cursor.read_exact(&mut message_bytes)?;

    // The plan is to develop the signature schema specific to verifiable
    // credentials in the future but for the time being, we use the signature schema
    // that is already implemented in the Concordium browser wallet. The message
    // signed in the Concordium browser wallet is prepended with the `account`
    // address and 8 zero bytes. Accounts in the Concordium browser wallet can
    // either sign a regular transaction (in that case the prepend is `account`
    // address and the nonce of the account which is by design >= 1) or sign a
    // message (in that case the prepend is `account` address and 8 zero bytes).
    // Hence, the 8 zero bytes ensure that the user does not accidentally sign a
    // transaction. The account nonce is of type u64 (8 bytes).
    let mut msg_prepend = vec![0; 32 + 8];
    // Prepend the `account` address of the signer.
    msg_prepend[0..32].copy_from_slice(&param.public_key.0);
    // Prepend 8 zero bytes.
    msg_prepend[32..40].copy_from_slice(&[0u8; 8]);
    // Calculate the message hash.
    let message_hash =
        crypto_primitives.hash_sha2_256(&[&msg_prepend[0..40], &message_bytes].concat()).0;

    let message: SignedMessage = Cursor::new(&message_bytes).get()?;

    // Check that the signature was intended for this contract.
    ensure_eq!(message.contract_address, ctx.self_address(), CustomContractError::WrongContract);

    // Check signature is not expired.
    ensure!(message.timestamp > ctx.metadata().slot_time(), CustomContractError::Expired);

    // Check signature was intended for this `entry_point`.
    ensure_eq!(
        message.entry_point.as_entrypoint_name(),
        EntrypointName::new_unchecked("store"),
        CustomContractError::WrongEntryPoint
    );

    // Check signature.
    ensure!(
        crypto_primitives.verify_ed25519_signature(
            param.public_key,
            param.signature,
            &message_hash
        ),
        CustomContractError::WrongSignature
    );

    let (state, state_builder) = host.state_and_builder();

    let entry = state.credential_registry.insert(param.public_key, CredentialState {
        metadata:          message.metadata,
        credential_secret: state_builder.new_box(message.credential_secret),
    });

    ensure!(entry.is_none(), CustomContractError::CredentialAlreadyRegisteredForGivenPublicKey);

    // Log the appropriate event
    logger.log(&Event::CredentialRegistered(CredentialRegisteredEvent {
        public_key: param.public_key,
    }))?;

    Ok(())
}

// Tests

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    // private key: 0D24966C4D1AAEA13344B3734B19E82C69B1B4B5DC9AA985B0C71C5D853CA675
    const PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([
        203, 17, 224, 43, 2, 223, 51, 21, 28, 70, 199, 72, 107, 183, 176, 196, 154, 11, 140, 22,
        115, 6, 164, 14, 89, 135, 129, 114, 208, 90, 66, 99,
    ]);
    const SIGNATURE: SignatureEd25519 = SignatureEd25519([
        64, 20, 87, 123, 162, 122, 125, 40, 134, 22, 20, 188, 188, 154, 117, 110, 114, 203, 68,
        160, 199, 217, 181, 85, 233, 150, 105, 166, 73, 197, 59, 10, 56, 9, 48, 14, 153, 75, 4,
        204, 80, 236, 87, 161, 208, 138, 239, 90, 72, 163, 31, 235, 177, 240, 130, 31, 234, 111,
        79, 55, 57, 68, 35, 13,
    ]);
    const CREDENTIAL_SECRET: [u8; 2] = [43, 1];
    const METADATA: Metadata = Metadata([43, 1]);

    // Test initialization succeeds.
    #[concordium_test]
    fn test_init() {
        // Setup the context
        let ctx = TestInitContext::empty();
        let mut builder = TestStateBuilder::new();

        // Call the contract function.
        let result = contract_init(&ctx, &mut builder);

        // Check the result
        let state = result.expect_report("Contract initialization failed");

        // Check the state
        claim!(state.credential_registry.is_empty(), "Expect empty registry");
    }

    /// Test only Setter can setMetadataUrl
    #[concordium_test]
    fn test_store_and_view_function() {
        let mut state_builder = TestStateBuilder::new();

        let state = State::empty(&mut state_builder);

        let mut host = TestHost::new(state, state_builder);

        let crypto_primitives = TestCryptoPrimitives::new();

        // Set up the context
        let mut ctx = TestReceiveContext::empty();

        ctx.set_self_address(ContractAddress {
            index:    0,
            subindex: 0,
        });
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(0));

        // Set up the parameter.
        let signed_message = SignedMessage {
            contract_address:  ContractAddress {
                index:    0,
                subindex: 0,
            },
            timestamp:         Timestamp::from_timestamp_millis(10000000000),
            entry_point:       OwnedEntrypointName::new_unchecked("store".to_string()),
            metadata:          METADATA,
            credential_secret: CREDENTIAL_SECRET.to_vec(),
        };
        let parameter = StoreParam {
            signature:  SIGNATURE,
            public_key: PUBLIC_KEY,
            message:    signed_message,
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();

        // Call the contract 'store' function.
        let result = store(&ctx, &mut host, &mut logger, &crypto_primitives);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "One event should be logged");

        claim_eq!(
            logger.logs[0],
            to_bytes(&Event::CredentialRegistered(CredentialRegisteredEvent {
                public_key: PUBLIC_KEY,
            })),
            "Incorrect event logged"
        );

        // Set up the parameter.
        let parameter_bytes = to_bytes(&PUBLIC_KEY);
        ctx.set_parameter(&parameter_bytes);

        // Call the contract 'view' function.
        let credential_secret = view(&ctx, &host);

        claim_eq!(
            credential_secret.expect_report("Expect credential_secret as return value"),
            Some(SimpleCredentialState {
                metadata:          METADATA,
                credential_secret: CREDENTIAL_SECRET.to_vec(),
            }),
            "Credential_secret should be viewable"
        );
    }
}
