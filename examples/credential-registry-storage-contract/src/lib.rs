//! The contract is used for storing verifiable credentials for the Web3Id
//! infrastructure. The contract stores encrypted credentials (generated with
//! the symmetric AES-256 encryption standard) and a version.
//!
//! The state contains a simple key-value store where each public key
//! can store its associated encrypted credential so that the credential can be
//! recovered by off-chain wallets. The `keys` for the store are the Ed25519
//! public keys and the `values` are the `version + encrypted_credentials`. The
//! version information is used by off-chain tools for decoding the encrypted
//! credential. Only if an off-chain tool has access to the AES secret key, it
//! can decode the credentials in this smart contract (credentials cannot be
//! decoded by third parties to preserve privacy). To enter credentials into
//! this contract, only the associated private key to the public key can
//! authorize the creation of an entry in this smart contract for its key. To
//! authorize the entry the associated private key to the public key signs its
//! version/ encrypted_credential that it wants to store. This ensures that
//! entries are generated/authorized by the public/private key pair that they
//! are associated with. The entries in this contract are immutable and cannot
//! be updated anymore once stored in this contract. Each public/private key
//! pair can authorize/generate up to one entry in this contract.
//!
//! The Concordium wallets generate a new public-private key pair and an
//! AES-256 secret key from a key path (example/dummy key path m/1’/2’/3’/4/0)
//! whenever storing a new verifiable credential. E.g. the first public-private
//! key pair/AES-256 secret key that the wallet creates will be derived from
//! m/1’/2’/3’/4/0, the second public-private key pair/AES-256 secret key that
//! the wallet creates will be derived from m/1’/2’/3’/4/1, … .
//!
//! Issuing of verifiable credentials works as follows:
//! The dApp (run by the issuer of the verifiable credential):
//!    - requests to generate a new public-private key pair/AES-256 secret key
//!      in the wallet
//!    - requests to encrypt the credentials (generated with the AES secret key)
//!    - requests a signed message from the wallet (generated with the private
//!      key)
//! The issuer invokes the 'store' entrypoint in this contract to store the
//! encrypted verifiable credential.
//!
//! Recovering verifiable credentials works as follows:
//! Recovery of credentials in a newly installed wallet on a different device
//! works because the wallet goes through the public keys derived from
//! m/1’/2’/3’/4/0, m/1’/2’/3’/4/1, … until it does not find such a public key
//! registered in this contract anymore. Some margin in the wallet will be
//! implemented to deal with issuers that failed to correctly store/register the
//! verifiable credentials in this contract.
#![cfg_attr(not(feature = "std"), no_std)]

use concordium_std::*;

const SIGNATURE_DOMAIN: &str = "WEB3ID:STORE";

/// Version is a string of two bytes that contain information needed for
/// decoding the credentials.
#[derive(Serial, SchemaType, Clone, Copy, Deserial, PartialEq, Debug)]
struct Version(u16);

/// Part of the contract state.
#[derive(Serial, Deserial, Clone)]
struct CredentialState {
    /// Version of the credential.
    version:              Version,
    /// The `encrypted_credential` stored in this contract.
    encrypted_credential: Vec<u8>,
}

/// The contract state.
#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S: HasStateApi> {
    /// All verifiable credentials.
    credential_registry: StateMap<PublicKeyEd25519, CredentialState, S>,
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
    /// Failed signature verification: Signature is expired.
    Expired,
    /// Failed signature verification: Signed message could not be serialized.
    SerializationError,
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
/// the `store/view` contract functions. It contains the version and the
/// encrypted_credential.
#[derive(Serialize, SchemaType, PartialEq)]
struct SimpleCredentialState {
    /// Version of the credential..
    version:              Version,
    /// The `encrypted_credential`.
    encrypted_credential: Vec<u8>,
}

/// The CredentialRegisteredEvent is logged when the `store` function is
/// invoked.
#[derive(Serialize, SchemaType)]
pub struct CredentialRegisteredEvent {
    /// Public key associated with the stored credential.
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
    return_value = "Option<SimpleCredentialState>",
    error = "CustomContractError"
)]
fn view<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<Option<SimpleCredentialState>> {
    let public_key: PublicKeyEd25519 = ctx.parameter_cursor().get()?;

    Ok(host.state().credential_registry.get(&public_key).map(|credential_state| {
        SimpleCredentialState {
            version:              credential_state.version,
            encrypted_credential: credential_state.encrypted_credential.clone(),
        }
    }))
}

/// The parameter type for the contract function `store`.
#[derive(Serialize, SchemaType, Debug)]
pub struct StoreParam {
    /// Public key that created the above signature.
    public_key: PublicKeyEd25519,
    /// Signature.
    signature:  SignatureEd25519,
    data:       DataToSign,
}

impl StoreParam {
    /// Prepare the message bytes for signature verification
    fn message_bytes(&self, bytes: &mut Vec<u8>) -> ContractResult<()> {
        self.data.serial(bytes).map_err(|_| CustomContractError::SerializationError)?;
        Ok(())
    }
}

/// The parameter type for the contract function `serializationHelper`.
#[derive(Serialize, SchemaType, Debug)]
pub struct DataToSign {
    /// A timestamp to make signatures expire.
    timestamp:            Timestamp,
    /// The contract_address that the signature is intended for.
    contract_address:     ContractAddress,
    /// Version of the credential.
    version:              Version,
    /// The serialized encrypted_credential.
    #[concordium(size_length = 2)]
    encrypted_credential: Vec<u8>,
}

/// Helper function that can be invoked at the front end to serialize
/// the `DataToSign` to be signed by the wallet. The
/// `DataToSign` includes all the input parameters from
/// `StoreParam` except for the `signature` and the `public_key`. We only need
/// the input parameter schema of this function at the front end. The
/// `serializationHelper` function is not executed at any point in time,
/// therefore the logic of the function is irrelevant.
#[receive(
    contract = "credential-registry-storage",
    name = "serializationHelper",
    parameter = "DataToSign"
)]
fn contract_serialization_helper<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    _host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    Ok(())
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
    let param: StoreParam = ctx.parameter_cursor().get()?;

    // Check that the signature was intended for this contract.
    ensure_eq!(param.data.contract_address, ctx.self_address(), CustomContractError::WrongContract);

    // Check signature is not expired.
    ensure!(param.data.timestamp >= ctx.metadata().slot_time(), CustomContractError::Expired);

    // Perepare message bytes as it is signed by the wallet.
    // Note that the message is prepended by a domain separation string.
    let mut message: Vec<u8> = SIGNATURE_DOMAIN.as_bytes().to_vec();
    param.message_bytes(&mut message)?;

    // Check signature.
    ensure!(
        crypto_primitives.verify_ed25519_signature(param.public_key, param.signature, &message),
        CustomContractError::WrongSignature
    );

    let entry = host.state_mut().credential_registry.insert(param.public_key, CredentialState {
        version:              param.data.version,
        encrypted_credential: param.data.encrypted_credential,
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
        13, 222, 247, 236, 178, 112, 59, 144, 60, 211, 81, 134, 97, 201, 22, 173, 36, 199, 164,
        217, 156, 107, 204, 83, 201, 153, 189, 77, 86, 238, 251, 220, 183, 221, 238, 114, 244, 219,
        132, 61, 167, 79, 230, 52, 73, 86, 101, 176, 153, 223, 103, 8, 197, 26, 82, 178, 162, 119,
        204, 239, 82, 114, 25, 7,
    ]);
    const ENCRYPTED_CREDENTIAL: [u8; 2] = [43, 1];
    const VERSION: Version = Version(43 + 256);

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

    /// Test storing and viewing of verifiable credentials
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

        let data = DataToSign {
            contract_address:     ContractAddress {
                index:    0,
                subindex: 0,
            },
            timestamp:            Timestamp::from_timestamp_millis(10000000000),
            version:              VERSION,
            encrypted_credential: ENCRYPTED_CREDENTIAL.to_vec(),
        };

        // Set up the parameter.
        let parameter = StoreParam {
            signature: SIGNATURE,
            public_key: PUBLIC_KEY,
            data,
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
        let result = view(&ctx, &host);

        claim_eq!(
            result.expect_report("Expect credential as return value"),
            Some(SimpleCredentialState {
                version:              VERSION,
                encrypted_credential: ENCRYPTED_CREDENTIAL.to_vec(),
            }),
            "Credential should be viewable"
        );
    }
}
