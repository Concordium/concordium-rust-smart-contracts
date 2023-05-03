//! The contract is used for storing credentials for the Web3ID infrastructure.
#![cfg_attr(not(feature = "std"), no_std)]

use concordium_std::*;

/// The contract state.
#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S: HasStateApi> {
    /// All of the token IDs
    credential_registry: StateMap<PublicKeyEd25519, Vec<u8>, S>,
}

// Functions for creating, updating and querying the contract state.
impl<S: HasStateApi> State<S> {
    /// Creates a new state with no tokens.
    fn empty(state_builder: &mut StateBuilder<S>) -> Self {
        State {
            credential_registry: state_builder.new_map(),
        }
    }
}

// Errors

/// The custom errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Failed logging: Log is full.
    LogFull,
    /// Failed logging: Log is malformed.
    LogMalformed,
    /// Failing to mint new tokens because one of the token IDs already exists
    /// in this contract.
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

/// The CredentialRegisteredEvent is logged when the `store` function is
/// invoked.
#[derive(Debug, Serialize, SchemaType)]
pub struct CredentialRegisteredEvent {
    /// Account that signed the `PermitMessage`.
    account: AccountAddress,
    /// The nonce that was used in the `PermitMessage`.
    nonce:   u64,
}

/// Tagged event to be serialized for the event log.
#[derive(SchemaType, Serialize)]
pub enum Event {
    CredentialRegistered(CredentialRegisteredEvent),
}

// Contract functions

/// Initialize contract instance with no token types initially.
#[init(contract = "credential-registry-storage", event = "Event")]
fn contract_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    Ok(State::empty(state_builder))
}

/// View the registered credential data.
#[receive(
    contract = "credential-registry-storage",
    name = "view",
    return_value = "Vec<u8>",
    parameter = "PublicKeyEd25519",
    error = "CustomContractError"
)]
fn view<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<Option<Vec<u8>>> {
    let public_key: PublicKeyEd25519 = ctx.parameter_cursor().get()?;

    Ok(host.state().credential_registry.get(&public_key).map(|payload| payload.clone()))
}

/// Part of the parameter type for the contract function `store`.
/// Specifies the message that is signed.
#[derive(SchemaType, Serialize)]
struct SignedMessage {
    /// The contract_address that the signature is intended for.
    contract_address: ContractAddress,
    /// A timestamp to make signatures expire.
    timestamp:        Timestamp,
    /// The entry_point that the signature is intended for.
    entry_point:      OwnedEntrypointName,
    /// The serialized payload with the credential registry data.
    #[concordium(size_length = 2)]
    payload:          Vec<u8>,
}

/// The parameter type for the contract function `store`.
/// Takes a signature, the public_key(signer), and the message that was signed.
#[derive(Serialize, SchemaType)]
pub struct StoreParam {
    /// Signature
    signature:  SignatureEd25519,
    /// PublicKeyEd25519 that created the above signature.
    public_key: PublicKeyEd25519,
    /// Message that was signed.
    message:    SignedMessage,
}

#[derive(Serialize)]
pub struct PartialStoreParam {
    /// Signature
    signature:  SignatureEd25519,
    /// PublicKeyEd25519 that created the above signature.
    public_key: PublicKeyEd25519,
}

/// Store credential data.
#[receive(
    contract = "credential-registry-storage",
    name = "store",
    parameter = "StoreParam",
    error = "CustomContractError",
    crypto_primitives,
    mutable
)]
fn store<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<()> {
    // Parse the parameter.
    let mut cursor = ctx.parameter_cursor();
    // The input parameter is `PermitParam` but we only read the initial part of it
    // with `PermitParamPartial`. I.e. we read the `signature` and the
    // `signer`, but not the `message` here.
    let param: PartialStoreParam = cursor.get()?;

    // The input parameter is `PermitParam` but we have only read the initial part
    // of it with `PermitParamPartial` so far. We read in the `message` now.
    // `(cursor.size() - cursor.cursor_position()` is the length of the message in
    // bytes.
    let mut message_bytes = vec![0; (cursor.size() - cursor.cursor_position()) as usize];

    cursor.read_exact(&mut message_bytes)?;

    // The message signed in the Concordium browser wallet is prepended with the
    // `account` address and 8 zero bytes. Accounts in the Concordium browser wallet
    // can either sign a regular transaction (in that case the prepend is
    // `account` address and the nonce of the account which is by design >= 1)
    // or sign a message (in that case the prepend is `account` address and 8 zero
    // bytes). Hence, the 8 zero bytes ensure that the user does not accidentally
    // sign a transaction. The account nonce is of type u64 (8 bytes).
    let mut msg_prepend = vec![0; 32 + 8];
    // Prepend the `account` address of the signer.
    msg_prepend[0..32].copy_from_slice(&param.public_key.0);
    // Prepend 8 zero bytes.
    msg_prepend[32..40].copy_from_slice(&[0u8; 8]);
    // Calculate the message hash.
    let message_hash =
        crypto_primitives.hash_sha2_256(&[&msg_prepend[0..40], &message_bytes].concat()).0;

    // Parse the parameter.
    let param: PartialStoreParam = ctx.parameter_cursor().get()?;

    let message: SignedMessage = Cursor::new(&message_bytes).get()?;

    // Check that the signature was intended for this contract.
    ensure_eq!(message.contract_address, ctx.self_address(), CustomContractError::WrongContract);

    // Check signature is not expired.
    ensure!(message.timestamp > ctx.metadata().slot_time(), CustomContractError::Expired);

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

    let entry = host.state_mut().credential_registry.insert(param.public_key, message.payload);

    ensure!(entry.is_none(), CustomContractError::CredentialAlreadyRegisteredForGivenPublicKey);
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
        159, 24, 64, 192, 150, 57, 240, 131, 50, 154, 248, 43, 81, 8, 195, 139, 44, 115, 115, 122,
        5, 45, 84, 150, 70, 196, 192, 167, 179, 89, 36, 112, 59, 194, 131, 144, 79, 1, 182, 174,
        150, 211, 191, 88, 194, 184, 29, 247, 77, 190, 211, 50, 101, 164, 143, 164, 239, 178, 92,
        16, 157, 249, 55, 5,
    ]);

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
    fn test_set_metadata_url() {
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
            contract_address: ContractAddress {
                index:    0,
                subindex: 0,
            },
            timestamp:        Timestamp::from_timestamp_millis(10000000000),
            entry_point:      OwnedEntrypointName::new_unchecked("store".to_string()),
            payload:          vec![43, 1],
        };
        let parameter = StoreParam {
            signature:  SIGNATURE,
            public_key: PUBLIC_KEY,
            message:    signed_message,
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Call the contract function.
        let result = store(&ctx, &mut host, &crypto_primitives);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");
    }
}
