//! This smart contract implements an example on-chain registry for the public
//! part of verifiable credentials (VCs).
//!
//! # Description
//!
//! The contract keeps track of credential public data, allows for managing the
//! VC life cycle and querying VCs data and status. The intended users are
//! issuers of VCs, holders of VCs, revocation authorities and verifiers.
//!
//! ## Issuer's  functionality
//!
//! - register a new credential;
//! - update an existing credential;
//! - revoke a credential;
//! - restore (cancelling revocation of) a revoked credential;
//! - register a public key;
//! - register a revocation authority key;
//! - update metadata;
//! - add/update credential types.
//!
//! Revocation authorities are some entities chosen by the issuer that have
//! revocation capabilities. Their public keys are registered by the issuer and
//! a revocation authority signs a revocation message with the corresponding
//! private key.
//!
//! ## Holder's functionality
//!
//! - revoke a credential by signing a revocation message.
//!
//! Revocation authority's functionality
//!
//! - revoke a credential by signing a revocation message.
//!
//! ## Verifier's functionality
//!
//! - view credential status to verify VC validity;
//! - view credential data to verify proofs (verifiable presentations) requested
//!   from holders.
use concordium_cis2::*;
use concordium_std::*;

/// The type for a credential identifier.
/// The identifier is generated externally by the issuer.
#[derive(Serialize, SchemaType, PartialEq, Eq, Clone, Copy, Debug)]
struct CredentialID {
    id: u128,
}

/// Credential type is a string that corresponds to the value of the "name"
/// attribute of the credential schema.
type CredentialType = String;

impl From<u128> for CredentialID {
    fn from(id: u128) -> Self {
        CredentialID {
            id,
        }
    }
}

/// A schema reference is a schema URL or DID address pointing to the JSON
/// schema for a verifiable credential.
#[derive(Serialize, SchemaType, PartialEq, Eq, Clone, Debug)]
struct SchemaRef {
    schema_ref: MetadataUrl,
}

impl From<MetadataUrl> for SchemaRef {
    fn from(schema_ref: MetadataUrl) -> Self {
        SchemaRef {
            schema_ref,
        }
    }
}

#[derive(Serialize, SchemaType, PartialEq, Eq, Clone, Copy, Debug)]
pub enum CredentialStatus {
    Active,
    Revoked,
    Expired,
    NotActivated,
}

/// A vector Pedersen commitment and credential type.
#[derive(Serialize, SchemaType, PartialEq, Clone, Debug)]
pub struct CredentialData {
    /// A vector Pedersen commitment to the attributes of the verifiable
    /// credential.
    #[concordium(size_length = 2)]
    commitment:      Vec<u8>,
    /// A type of the credential that is used to identify which schema the
    /// credential is based on.
    credential_type: CredentialType,
}

/// Public data of a verifiable credential.
#[derive(Serial, DeserialWithState, Debug)]
#[concordium(state_parameter = "S")]
pub struct CredentialEntry<S: HasStateApi> {
    /// The holder's identifier is a public key.
    holder_id:        PublicKeyEd25519,
    /// If this flag is set to `true` the holder can send a signed message to
    /// revoke their credential.
    holder_revocable: bool,
    /// The date from which the credential is considered valid. `None`
    /// corresponsds to a credential that is valid immediately after being
    /// issued.
    valid_from:       Option<Timestamp>,
    /// After this date, the credential becomes expired. `None` corresponds to a
    /// credential that cannot expire.
    valid_until:      Option<Timestamp>,
    /// The nonce is used to avoid replay attacks when checking the holder's
    /// signature on a revocation message.
    revocation_nonce: u64,
    /// Revocation flag
    revoked:          bool,
    /// Commitment and schema reference
    /// This data is only needed when credential info is requested. In other
    /// operations, `StateBox` defers loading credential data.
    credential_data:  StateBox<CredentialData, S>,
}

impl<S: HasStateApi> CredentialEntry<S> {
    /// Compute the credential status based on validity dates and the revocation
    /// flag. If a VC is revoked the status will be `Revoked` regardless the
    /// validity dates.
    fn get_status(&self, now: Timestamp) -> CredentialStatus {
        if self.revoked {
            return CredentialStatus::Revoked;
        }
        if let Some(valid_until) = self.valid_until {
            if valid_until < now {
                return CredentialStatus::Expired;
            }
        }
        if let Some(valid_until) = self.valid_from {
            if now < valid_until {
                return CredentialStatus::NotActivated;
            }
        }
        CredentialStatus::Active
    }

    fn info(&self) -> CredentialInfo {
        CredentialInfo {
            holder_id:        self.holder_id,
            holder_revocable: self.holder_revocable,
            commitment:       self.credential_data.commitment.clone(),
            credential_type:  self.credential_data.credential_type.clone(),
            valid_from:       self.valid_from,
            valid_until:      self.valid_until,
        }
    }
}

/// The registry state.
// NOTE: keys are stored in a map to keep the indices of other keys fixed when adding/removing a
// key, as opposed to storing them in a vector. The indices are defined externally to the contract
// by the issuer.
#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
pub struct State<S: HasStateApi> {
    issuer:          AccountAddress,
    issuer_metadata: MetadataUrl,
    issuer_keys:     StateMap<u8, PublicKeyEd25519, S>,
    revocation_keys: StateMap<u8, (PublicKeyEd25519, u64), S>,
    credentials:     StateMap<CredentialID, CredentialEntry<S>, S>,
    schema_registry: StateMap<CredentialType, SchemaRef, S>,
}

/// Contract Errors.
#[derive(Debug, PartialEq, Eq, Reject, Serial, SchemaType)]
enum ContractError {
    #[from(ParseError)]
    ParseParamsError,
    CredentialNotFound,
    CredentialAlreadyExists,
    IncorrectStatusBeforeRevocation,
    IncorrectStatusBeforeRestoring,
    KeyAlreadyExists,
    KeyNotFound,
    SchemaNotFound,
    SchemaAlreadyExists,
    NotAuthorized,
    NonceMismatch,
    WrongContract,
    ExpiredSignature,
    WrongSignature,
    SerializationError,
    LogFull,
    LogMalformed,
}

impl From<LogError> for ContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

type ContractResult<A> = Result<A, ContractError>;

/// Functions for creating, updating and querying the contract state.
impl<S: HasStateApi> State<S> {
    fn new(
        state_builder: &mut StateBuilder<S>,
        issuer: AccountAddress,
        issuer_metadata: MetadataUrl,
    ) -> Self {
        State {
            issuer,
            issuer_metadata,
            schema_registry: state_builder.new_map(),
            issuer_keys: state_builder.new_map(),
            revocation_keys: state_builder.new_map(),
            credentials: state_builder.new_map(),
        }
    }

    fn view_credential_info(
        &self,
        credential_id: CredentialID,
    ) -> ContractResult<CredentialQueryResponse> {
        let entry =
            self.credentials.get(&credential_id).ok_or(ContractError::CredentialNotFound)?;
        let schema_ref = self
            .schema_registry
            .get(&entry.credential_data.credential_type)
            .ok_or(ContractError::SchemaNotFound)?;
        Ok(CredentialQueryResponse {
            credential_info:  entry.info(),
            revocation_nonce: entry.revocation_nonce,
            schema_ref:       schema_ref.clone(),
        })
    }

    fn view_credential_status(
        &self,
        now: Timestamp,
        credential_id: CredentialID,
    ) -> ContractResult<CredentialStatus> {
        self.credentials
            .get(&credential_id)
            .map(|x| x.get_status(now))
            .ok_or(ContractError::CredentialNotFound)
    }

    fn register_credential(
        &mut self,
        credential_id: CredentialID,
        credential_info: &CredentialInfo,
        state_builder: &mut StateBuilder<S>,
    ) -> ContractResult<SchemaRef> {
        let schema = self
            .schema_registry
            .get(&credential_info.credential_type)
            .ok_or(ContractError::SchemaNotFound)?;
        let credential_entry = CredentialEntry {
            holder_id:        credential_info.holder_id,
            holder_revocable: credential_info.holder_revocable,
            valid_from:       credential_info.valid_from,
            valid_until:      credential_info.valid_until,
            credential_data:  state_builder.new_box(CredentialData {
                commitment:      credential_info.commitment.clone(),
                credential_type: credential_info.credential_type.clone(),
            }),
            revocation_nonce: 0,
            revoked:          false,
        };
        let res = self.credentials.insert(credential_id, credential_entry);
        ensure!(res.is_none(), ContractError::CredentialAlreadyExists);
        Ok(schema.clone())
    }

    fn revoke_credential(
        &mut self,
        now: Timestamp,
        credential_id: CredentialID,
    ) -> ContractResult<()> {
        let mut credential =
            self.credentials.get_mut(&credential_id).ok_or(ContractError::CredentialNotFound)?;
        let status = credential.get_status(now);
        ensure!(
            status == CredentialStatus::Active || status == CredentialStatus::NotActivated,
            ContractError::IncorrectStatusBeforeRevocation
        );
        credential.revoked = true;
        Ok(())
    }

    fn restore_credential(
        &mut self,
        now: Timestamp,
        credential_id: CredentialID,
    ) -> ContractResult<()> {
        let mut credential =
            self.credentials.get_mut(&credential_id).ok_or(ContractError::CredentialNotFound)?;
        let status = credential.get_status(now);
        // It is expected that the credential was previously revoked.
        // It can expire by the time of restoring; in this case, it is still marked as
        // `revoked: false`, but the status will be `Expired`.
        ensure!(status == CredentialStatus::Revoked, ContractError::IncorrectStatusBeforeRestoring);
        credential.revoked = false;
        Ok(())
    }

    fn register_issuer_key(&mut self, key_index: u8, pk: PublicKeyEd25519) -> ContractResult<()> {
        let res = self.issuer_keys.insert(key_index, pk);
        ensure!(res.is_none(), ContractError::KeyAlreadyExists);
        Ok(())
    }

    fn remove_issuer_key(&mut self, key_index: u8) -> ContractResult<()> {
        self.issuer_keys.remove(&key_index);
        Ok(())
    }

    fn register_revocation_key(
        &mut self,
        key_index: u8,
        pk: PublicKeyEd25519,
    ) -> ContractResult<()> {
        let res = self.revocation_keys.insert(key_index, (pk, 0));
        ensure!(res.is_none(), ContractError::KeyAlreadyExists);
        Ok(())
    }

    fn view_revocation_key(&self, key_index: u8) -> ContractResult<(PublicKeyEd25519, u64)> {
        self.revocation_keys.get(&key_index).map(|x| *x).ok_or(ContractError::KeyNotFound)
    }

    fn remove_revocation_key(&mut self, key_index: u8) -> ContractResult<()> {
        self.issuer_keys.remove(&key_index);
        Ok(())
    }

    fn view_issuer_keys(&self) -> Vec<(u8, PublicKeyEd25519)> {
        self.issuer_keys.iter().map(|x| (*x.0, *x.1)).collect()
    }

    fn update_issuer_metadata(&mut self, issuer_metadata: &MetadataUrl) {
        self.issuer_metadata = issuer_metadata.clone()
    }

    fn add_schema(&mut self, id: CredentialType, schema_ref: SchemaRef) -> ContractResult<()> {
        let res = self.schema_registry.insert(id, schema_ref);
        ensure!(res.is_none(), ContractError::SchemaAlreadyExists);
        Ok(())
    }

    fn update_schema(&mut self, id: CredentialType, schema_ref: SchemaRef) -> ContractResult<()> {
        let res = self.schema_registry.insert(id, schema_ref);
        ensure!(res.is_some(), ContractError::SchemaNotFound);
        Ok(())
    }
}

/// Data for events of registering and updating a credential.
/// Used by the tagged event `CredentialEvent`.
#[derive(Serialize, SchemaType)]
struct CredentialEventData {
    /// An identifier of a credential being registered/updated.
    credential_id:   CredentialID,
    /// A public key of the credential's holder.
    holder_id:       PublicKeyEd25519,
    /// A reference to the credential JSON schema.
    schema_ref:      SchemaRef,
    /// Type of the credential.
    credential_type: CredentialType,
}

/// A type for specifying who is revoking a credential, when registering a
/// revocation event.
#[derive(Serialize, SchemaType)]
enum Revoker {
    Issuer,
    Holder,
    /// `Other` is used for the cases when the revoker is not the issuer or
    /// holder. In this contract it is a revocation authority, which is
    /// identified using ther public key.
    Other(PublicKeyEd25519),
}

/// A short comment on a reason of revoking or restoring a credential.
/// The string is of a limited size of 256 bytes in order to fit into a single
/// log entry along with other data.
#[derive(Serialize, SchemaType, Clone)]
struct Reason {
    #[concordium(size_length = 1)]
    reason: String,
}

impl From<String> for Reason {
    fn from(reason: String) -> Self {
        Reason {
            reason,
        }
    }
}

/// An untagged revocation event.
/// For a tagged version use `CredentialEvent`.
#[derive(Serialize, SchemaType)]
struct RevokeCredentialEvent {
    /// An identifier of a credential being revoked.
    credential_id: CredentialID,
    /// A public key of the credential's holder.
    holder_id:     PublicKeyEd25519,
    /// Who revokes the credential.
    revoker:       Revoker,
    /// An optional text clarifying the revocation reasons.
    /// The issuer can use this field to comment on the revocation, so the
    /// holder can observe it in the wallet.
    reason:        Option<Reason>,
}

/// An untagged restoration event.
/// For a tagged version use `CredentialEvent`.
#[derive(Serialize, SchemaType)]
struct RestoreCredentialEvent {
    /// An identifier of a credential being restored.
    credential_id: CredentialID,
    /// A public key of the credential's holder.
    holder_id:     PublicKeyEd25519,
    /// An optional text clarifying the restoring reasons.
    reason:        Option<Reason>,
}

#[derive(Debug, Serialize, SchemaType)]
pub struct IssuerMetadataEvent {
    /// The location of the metadata.
    pub metadata_url: MetadataUrl,
}

/// Tagged credential registry event.
/// This version should be used for logging the events.
#[derive(Serialize, SchemaType)]
enum CredentialEvent {
    /// Credential registration event. Logged when an entry in the registry is
    /// created for the first time.
    Register(CredentialEventData),
    /// Credential update event. Logged when updating an existing credential
    /// entry.
    Update(CredentialEventData),
    /// Credential revocation event.
    Revoke(RevokeCredentialEvent),
    /// Credential restoration (reversing revocation) event.
    Restore(RestoreCredentialEvent),
    /// Issuer's metadata changes, including the contract deployment.
    Metadata(IssuerMetadataEvent),
}

/// Init function that creates a fresh registry state given the issuer's
/// metadata
///
/// Logs `IssuerMetadataEvent`
#[init(
    contract = "credential_registry",
    parameter = "MetadataUrl",
    event = "CredentialEvent",
    enable_logger
)]
fn init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
    logger: &mut impl HasLogger,
) -> InitResult<State<S>> {
    let issuer_metadata: MetadataUrl = ctx.parameter_cursor().get()?;
    logger.log(&CredentialEvent::Metadata(IssuerMetadataEvent {
        metadata_url: issuer_metadata.clone(),
    }))?;
    Ok(State::new(state_builder, ctx.init_origin(), issuer_metadata))
}

fn sender_is_issuer<S: HasStateApi>(ctx: &impl HasReceiveContext, state: &State<S>) -> bool {
    ctx.sender().matches_account(&state.issuer)
}

#[derive(Serialize, SchemaType, PartialEq, Eq, Clone, Debug)]
pub struct CredentialInfo {
    /// The holder's identifier is a public key.
    holder_id:        PublicKeyEd25519,
    /// If this flag is set to `true` the holder can send a signed message to
    /// revoke their credential.
    holder_revocable: bool,
    /// A vector Pedersen commitment to the attributes of the verifiable
    /// credential.
    #[concordium(size_length = 2)]
    commitment:       Vec<u8>,
    /// The date from which the credential is considered valid. `None`
    /// corresponsds to a credential that is valid immediately after being
    /// issued.
    valid_from:       Option<Timestamp>,
    /// After this date, the credential becomes expired. `None` corresponds to a
    /// credential that cannot expire.
    valid_until:      Option<Timestamp>,
    /// A type of the credential that is used to identify which schema the
    /// credential is based on.
    credential_type:  CredentialType,
}

/// Response to a credential data query.
#[derive(Serialize, SchemaType, Clone, Debug)]
pub struct CredentialQueryResponse {
    credential_info:  CredentialInfo,
    /// A schema URL or DID address pointing to the JSON schema for a verifiable
    /// credential.
    schema_ref:       SchemaRef,
    /// The nonce is used to avoid replay attacks when checking the holder's
    /// signature on a revocation message.
    revocation_nonce: u64,
}

/// A view entrypoint for looking up an entry in the registry by id.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The credential with the given id does not exist.
#[receive(
    contract = "credential_registry",
    name = "credentialEntry",
    parameter = "CredentialID",
    error = "ContractError",
    return_value = "CredentialQueryResponse"
)]
fn contract_credential_entry<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<CredentialQueryResponse, ContractError> {
    let credential_id = ctx.parameter_cursor().get()?;
    host.state().view_credential_info(credential_id)
}

/// A view entrypoint querying the credential's status.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The credential with the given id does not exist.
#[receive(
    contract = "credential_registry",
    name = "credentialStatus",
    parameter = "CredentialID",
    error = "ContractError",
    return_value = "CredentialStatus"
)]
fn contract_credential_status<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<CredentialStatus, ContractError> {
    let credential_id = ctx.parameter_cursor().get()?;
    let now = ctx.metadata().slot_time();
    let status = host.state().view_credential_status(now, credential_id)?;
    Ok(status)
}

/// Data for registering and updating a credential registy entry.
#[derive(Serial, Deserial, SchemaType)]
pub struct RegisterCredentialParameter {
    /// Credential ID
    credential_id:   CredentialID,
    /// Input data for the credential entry.
    credential_info: CredentialInfo,
}

/// Register a new credential with the given id and data.
/// Logs RegisterCredentialEvent.
///
/// Can be called only by the issuer.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The caller is not the issuer
/// - An entry with the given credential id already exists
/// - Fails to log RegisterCredentialEvent
#[receive(
    contract = "credential_registry",
    name = "registerCredential",
    parameter = "RegisterCredentialParameter",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_register_credential<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    ensure!(sender_is_issuer(ctx, host.state()), ContractError::NotAuthorized);
    let parameter: RegisterCredentialParameter = ctx.parameter_cursor().get()?;
    let (state, state_bulder) = host.state_and_builder();
    let schema = state.register_credential(
        parameter.credential_id,
        &parameter.credential_info,
        state_bulder,
    )?;
    logger.log(&CredentialEvent::Register(CredentialEventData {
        credential_id:   parameter.credential_id,
        holder_id:       parameter.credential_info.holder_id,
        schema_ref:      schema,
        credential_type: parameter.credential_info.credential_type,
    }))?;
    Ok(())
}

/// Metadata of the signature
#[derive(Serialize, SchemaType, Clone, Copy)]
struct SigningData {
    /// The contract_address that the signature is intended for.
    contract_address: ContractAddress,
    /// A nonce to prevent replay attacks.
    nonce:            u64,
    /// A timestamp to make signatures expire.
    timestamp:        Timestamp,
}

const SIGNARUTE_DOMAIN: &str = "WEB3ID:REVOKE";

/// A parameter type for revoking a credential by the holder.
#[derive(Serialize, SchemaType)]
pub struct RevokeCredentialHolderParam {
    /// Id of the credential to revoke.
    credential_id: CredentialID,
    /// Info about the signature.
    signing_data:  SigningData,
    signature:     SignatureEd25519,
    /// (Optional) reason for revoking the credential.
    reason:        Option<Reason>,
}

/// Prepare the message bytes for the holeder
impl RevokeCredentialHolderParam {
    fn message_bytes(&self, bytes: &mut Vec<u8>) -> ContractResult<()> {
        self.credential_id
            .serial::<Vec<_>>(bytes)
            .map_err(|_| ContractError::SerializationError)?;
        self.signing_data.serial(bytes).map_err(|_| ContractError::SerializationError)?;
        self.reason.serial(bytes).map_err(|_| ContractError::SerializationError)?;
        Ok(())
    }
}

/// A parameter type for revoking a credential by the issuer.
#[derive(Serialize, SchemaType)]
pub struct RevokeCredentialIssuerParam {
    /// Id of the credential to revoke.
    credential_id: CredentialID,
    /// (Optional) reason for revoking the credential.
    reason:        Option<Reason>,
}

/// A parameter type for revoking a credential by a revocation authority.
#[derive(Serialize, SchemaType)]
pub struct RevokeCredentialOtherParam {
    /// Id of the credential to revoke.
    credential_id:        CredentialID,
    /// Info about the signature.
    signing_data:         SigningData,
    signature:            SignatureEd25519,
    /// Key index in the revocation keys map
    revocation_key_index: u8,
    /// (Optional) reason for revoking the credential.
    reason:               Option<Reason>,
}

impl RevokeCredentialOtherParam {
    /// Prepare the message bytes for a revocation authority
    fn message_bytes(&self, bytes: &mut Vec<u8>) -> ContractResult<()> {
        self.credential_id
            .serial::<Vec<_>>(bytes)
            .map_err(|_| ContractError::SerializationError)?;
        self.signing_data.serial(bytes).map_err(|_| ContractError::SerializationError)?;
        self.revocation_key_index.serial(bytes).map_err(|_| ContractError::SerializationError)?;
        self.reason.serial(bytes).map_err(|_| ContractError::SerializationError)?;
        Ok(())
    }
}

/// Performs authorization based on the signature and the public key.
/// The message is built from serialized `credential_id` and `signing_data`.
fn authorize_with_signature(
    crypto_primitives: &impl HasCryptoPrimitives,
    ctx: &impl HasReceiveContext,
    nonce: u64,
    public_key: PublicKeyEd25519,
    signing_data: SigningData,
    message: &[u8],
    signature: SignatureEd25519,
) -> Result<(), ContractError> {
    // Check the nonce to prevent replay attacks.
    ensure_eq!(signing_data.nonce, nonce, ContractError::NonceMismatch);

    // Check that the signature was intended for this contract.
    ensure_eq!(signing_data.contract_address, ctx.self_address(), ContractError::WrongContract);

    // Check signature is not expired.
    ensure!(signing_data.timestamp > ctx.metadata().slot_time(), ContractError::ExpiredSignature);

    // Calculate the message hash.
    let message_hash = crypto_primitives.hash_sha2_256(message).0;

    // Check the signature.
    ensure!(
        crypto_primitives.verify_ed25519_signature(public_key, signature, &message_hash),
        ContractError::WrongSignature
    );
    Ok(())
}

/// Revoke a credential as a holder.
///
/// Holder is authenticated by verifying the signature on the input to the
/// entrypoint with the holder's public key. The public key is stored in the
/// credential entry (`holder_id`).
///
/// Note that nonce is used as a general way to prevent replay attacks. In this
/// particular case, tthe revocation can be reversed by the issuer by restoring
/// the revoked credential.
///
/// Logs RevokeCredentialEvent with `Holder` as the revoker.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Signature validation has failed.
/// - An entry with the given credential id does not exist.
/// - The credential status is not one of `Active` or `NotActivated`.
/// - Fails to log RevokeCredentialEvent.
#[receive(
    contract = "credential_registry",
    name = "revokeCredentialHolder",
    parameter = "RevokeCredentialHolderParam",
    error = "ContractError",
    crypto_primitives,
    enable_logger,
    mutable
)]
fn contract_revoke_credential_holder<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> Result<(), ContractError> {
    let parameter: RevokeCredentialHolderParam = ctx.parameter_cursor().get()?;

    let state = host.state_mut();
    let mut registry_entry = state
        .credentials
        .entry(parameter.credential_id)
        .occupied_or(ContractError::CredentialNotFound)?;

    let revoker = Revoker::Holder;

    let signing_data = parameter.signing_data;
    let signature = parameter.signature;

    // Only holder-revocable entries can be revoked by the holder.
    ensure!(registry_entry.holder_revocable, ContractError::NotAuthorized);

    // Update the nonce.
    registry_entry.revocation_nonce += 1;

    // Get the public key and the current nonce.
    let public_key = registry_entry.holder_id;
    let nonce = registry_entry.revocation_nonce;

    // Perepare message bytes as it is signer by the wallet
    // Note that the message is prepended by a domain separation string
    let mut message: Vec<u8> = SIGNARUTE_DOMAIN.as_bytes().to_vec();
    parameter.message_bytes(&mut message)?;

    authorize_with_signature(
        crypto_primitives,
        ctx,
        nonce,
        public_key,
        signing_data,
        &message,
        signature,
    )?;
    let credential_id = parameter.credential_id;
    let now = ctx.metadata().slot_time();
    let holder_id = registry_entry.holder_id;
    drop(registry_entry);

    state.revoke_credential(now, credential_id)?;

    logger.log(&CredentialEvent::Revoke(RevokeCredentialEvent {
        credential_id,
        holder_id,
        reason: parameter.reason,
        revoker,
    }))?;
    Ok(())
}

/// Revoke a credential as an issuer.
/// Can be called by the contrat owner.
///
/// Logs RevokeCredentialEvent with `Issuer` as the revoker.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The caller is not the issuer.
/// - An entry with the given credential id does not exist.
/// - The credential status is not one of `Active` or `NotActivated`.
/// - Fails to log RevokeCredentialEvent.
#[receive(
    contract = "credential_registry",
    name = "revokeCredentialIssuer",
    parameter = "RevokeCredentialIssuerParam",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_revoke_credential_issuer<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    ensure!(sender_is_issuer(ctx, host.state()), ContractError::NotAuthorized);
    let parameter: RevokeCredentialIssuerParam = ctx.parameter_cursor().get()?;

    let state = host.state_mut();
    let registry_entry = state
        .credentials
        .entry(parameter.credential_id)
        .occupied_or(ContractError::CredentialNotFound)?;

    let revoker = Revoker::Issuer;
    let now = ctx.metadata().slot_time();
    let holder_id = registry_entry.holder_id;
    drop(registry_entry);

    let credential_id = parameter.credential_id;

    state.revoke_credential(now, credential_id)?;

    logger.log(&CredentialEvent::Revoke(RevokeCredentialEvent {
        credential_id,
        holder_id,
        reason: parameter.reason,
        revoker,
    }))?;
    Ok(())
}

/// Revoke a credential as a revocation authority.
///
/// A revocation authority is any entity that holds a private key corresponding
/// to a public key registered by the issuer.
///
/// A revocation authority is authenticated by verifying the signature on the
/// input to the entrypoint with the autority's public key.
/// The public key is stored in `revocation_keys`. The index of the key in the
/// list of revocation keys is provided as input.
///
/// Note that a nonce is used as a general way to prevent replay attacks. In
/// this particular case, the revocation is done once, however, the issuer could
/// choose to implement an update method that restores the revoked credential.
///
///  Logs RevokeCredentialEvent with `Other` as the revoker.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - No entry for the key index.
/// - Signature validation has failed.
/// - An entry with the given credential id does not exist
/// - The credential status is not one of `Active` or `NotActivated`
/// - Fails to log RevokeCredentialEvent
#[receive(
    contract = "credential_registry",
    name = "revokeCredentialOther",
    parameter = "RevokeCredentialOtherParam",
    error = "ContractError",
    crypto_primitives,
    enable_logger,
    mutable
)]
fn contract_revoke_credential_other<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> Result<(), ContractError> {
    let parameter: RevokeCredentialOtherParam = ctx.parameter_cursor().get()?;

    let state = host.state_mut();
    let registry_entry = state
        .credentials
        .entry(parameter.credential_id)
        .occupied_or(ContractError::CredentialNotFound)?;
    let holder_id = registry_entry.holder_id;
    drop(registry_entry);

    let key_index = parameter.revocation_key_index;
    let mut entry =
        state.revocation_keys.entry(key_index).occupied_or(ContractError::CredentialNotFound)?;
    // Update the nonce.
    entry.1 += 1;

    let nonce = entry.1;
    let public_key = entry.0;

    // Set the revoker to be the revocation authority.
    let revoker = Revoker::Other(public_key);

    let signing_data = parameter.signing_data;
    let signature = parameter.signature;

    // Perepare message bytes as it is signer by the wallet
    // Note that the message is prepended by a domain separation string
    let mut message: Vec<u8> = SIGNARUTE_DOMAIN.as_bytes().to_vec();
    parameter.message_bytes(&mut message)?;

    authorize_with_signature(
        crypto_primitives,
        ctx,
        nonce,
        public_key,
        signing_data,
        &message,
        signature,
    )?;
    let now = ctx.metadata().slot_time();
    drop(entry);

    let credential_id = parameter.credential_id;

    state.revoke_credential(now, credential_id)?;
    logger.log(&CredentialEvent::Revoke(RevokeCredentialEvent {
        credential_id,
        holder_id,
        reason: parameter.reason,
        revoker,
    }))?;
    Ok(())
}

#[derive(Serial, Deserial, SchemaType)]
pub struct RegisterPublicKeyParameter {
    key_index: u8,
    key:       PublicKeyEd25519,
}

#[derive(Serialize, SchemaType)]
pub struct RegisterPublicKeyParameters(
    #[concordium(size_length = 2)] pub Vec<RegisterPublicKeyParameter>,
);

/// Register the issuer's public keys.
/// These keys are for off-chain use only. The registry is just used as a
/// storage and some credentials issued off-chain can be signed with the
/// issuer's keys.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Some of the key indices already exist.
#[receive(
    contract = "credential_registry",
    name = "registerIssuerKeys",
    parameter = "RegisterPublicKeyParameters",
    error = "ContractError",
    mutable
)]
fn contract_register_issuer_keys<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(), ContractError> {
    ensure!(sender_is_issuer(ctx, host.state()), ContractError::NotAuthorized);
    let RegisterPublicKeyParameters(parameters) = ctx.parameter_cursor().get()?;
    for parameter in parameters {
        host.state_mut().register_issuer_key(parameter.key_index, parameter.key)?;
    }
    Ok(())
}

/// Remove the issuer's public keys.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Some of the key indices does not exist.
#[derive(Serialize, SchemaType)]
pub struct RemovePublicKeyParameters(#[concordium(size_length = 2)] pub Vec<u8>);

#[receive(
    contract = "credential_registry",
    name = "removeIssuerKeys",
    parameter = "RemovePublicKeyParameters",
    error = "ContractError",
    mutable
)]
fn contract_remove_issuer_keys<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(), ContractError> {
    ensure!(sender_is_issuer(ctx, host.state()), ContractError::NotAuthorized);
    let RemovePublicKeyParameters(parameters) = ctx.parameter_cursor().get()?;
    for index in parameters {
        host.state_mut().remove_issuer_key(index)?;
    }
    Ok(())
}

/// Register revocation authorities public keys.
/// These keys are used to authorize the revocation (applies to the whole
/// registry). Only the issuer can call the entrypoint.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Some of the key indices already exist.
/// - The caller is not the issuer.
#[receive(
    contract = "credential_registry",
    name = "registerRevocationKeys",
    parameter = "RegisterPublicKeyParameters",
    error = "ContractError",
    mutable
)]
fn contract_register_revocation_keys<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(), ContractError> {
    ensure!(sender_is_issuer(ctx, host.state()), ContractError::NotAuthorized);
    let RegisterPublicKeyParameters(parameters) = ctx.parameter_cursor().get()?;
    for parameter in parameters {
        host.state_mut().register_revocation_key(parameter.key_index, parameter.key)?;
    }
    Ok(())
}

/// Remove revocation authorities public keys.
/// Only the issuer can call the entrypoint.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Some of the key indices do not exist.
/// - The caller is not the issuer.
#[receive(
    contract = "credential_registry",
    name = "removeRevocationKeys",
    parameter = "RemovePublicKeyParameters",
    error = "ContractError",
    mutable
)]
fn contract_remove_revocation_keys<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(), ContractError> {
    ensure!(sender_is_issuer(ctx, host.state()), ContractError::NotAuthorized);
    let RemovePublicKeyParameters(parameters) = ctx.parameter_cursor().get()?;
    for index in parameters {
        host.state_mut().remove_revocation_key(index)?;
    }
    Ok(())
}

/// A view entrypoint for looking up a revocation key.
/// Returns a public key and the nonce.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The revocation key index does not exist.
#[receive(
    contract = "credential_registry",
    name = "revocationKey",
    parameter = "u8",
    error = "ContractError",
    return_value = "(PublicKeyEd25519, u64)",
    mutable
)]
fn contract_revocation_key<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(PublicKeyEd25519, u64), ContractError> {
    let index = ctx.parameter_cursor().get()?;
    host.state().view_revocation_key(index)
}

/// A view entrypoint that returns a vector of issuer's keys.
#[receive(
    contract = "credential_registry",
    name = "issuerKeys",
    error = "ContractError",
    return_value = "Vec<(u8, PublicKeyEd25519)>"
)]
fn contract_issuer_keys<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<Vec<(u8, PublicKeyEd25519)>, ContractError> {
    let keys = host.state().view_issuer_keys();
    Ok(keys)
}

/// A view entrypoint to get the metadata URL and checksum.
#[receive(
    contract = "credential_registry",
    name = "issuerMetadata",
    error = "ContractError",
    return_value = "MetadataUrl"
)]
fn contract_issuer_metadata<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<MetadataUrl, ContractError> {
    Ok(host.state().issuer_metadata.clone())
}

/// Update issuer's metadata
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The caller is not the issuer.
/// - It fails to log `IssuerMetadataEvent`
#[receive(
    contract = "credential_registry",
    name = "updateIssuerMetadata",
    parameter = "MetadataUrl",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_update_issuer_metadata<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    ensure!(sender_is_issuer(ctx, host.state()), ContractError::NotAuthorized);
    let data = ctx.parameter_cursor().get()?;
    host.state_mut().update_issuer_metadata(&data);
    logger.log(&CredentialEvent::Metadata(IssuerMetadataEvent {
        metadata_url: data,
    }))?;
    Ok(())
}

/// A view entrypoint for querying the issuer account address
#[receive(
    contract = "credential_registry",
    name = "issuer",
    error = "ContractError",
    return_value = "AccountAddress"
)]
fn contract_issuer<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<AccountAddress, ContractError> {
    Ok(host.state().issuer)
}

#[derive(Serial, Deserial, SchemaType)]
struct CredentialSchemaParam {
    schemas: Vec<(CredentialType, SchemaRef)>,
}

/// Add credential schemas.
///
/// Can be called only by the issuer.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The caller is not the issuer.
/// - Some of the schemas are already added.
#[receive(
    contract = "credential_registry",
    name = "addCredentialSchemas",
    parameter = "CredentialSchemaParam",
    error = "ContractError",
    mutable
)]
fn contract_add_credential_schemas<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(), ContractError> {
    ensure!(sender_is_issuer(ctx, host.state()), ContractError::NotAuthorized);
    let data: CredentialSchemaParam = ctx.parameter_cursor().get()?;
    for (id, schema_ref) in data.schemas {
        host.state_mut().add_schema(id, schema_ref)?;
    }
    Ok(())
}

/// Update existing credential schemas.
/// Note that updating the schemas should not break credentials based on these
/// schemas. An intended use case is to update a reference if the URL to the
/// JSON document has changed, but the JSON document itself remains the same.
///
/// Can be called only by the issuer.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The caller is not the issuer.
/// - Some of the schemas are not present.
#[receive(
    contract = "credential_registry",
    name = "updateCredentialSchemas",
    parameter = "CredentialSchemaParam",
    error = "ContractError",
    mutable
)]
fn contract_update_credential_schemas<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(), ContractError> {
    ensure!(sender_is_issuer(ctx, host.state()), ContractError::NotAuthorized);
    let data: CredentialSchemaParam = ctx.parameter_cursor().get()?;
    for (id, schema_ref) in data.schemas {
        host.state_mut().update_schema(id, schema_ref)?;
    }
    Ok(())
}

/// A parameter type for restoring a credential by the issuer.
#[derive(Serialize, SchemaType)]
pub struct RestoreCredentialIssuerParam {
    /// Id of the credential to restore.
    credential_id: CredentialID,
    /// (Optional) reason for restoring the credential.
    reason:        Option<Reason>,
}

/// Restore credential by the issuer.
/// Restoring means reverting revocation.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The caller is not the issuer.
/// - Credential does not exist.
/// - Credential status is different from `Revoked`.
#[receive(
    contract = "credential_registry",
    name = "restoreCredential",
    parameter = "RestoreCredentialIssuerParam",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_restore_credential<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    ensure!(sender_is_issuer(ctx, host.state()), ContractError::NotAuthorized);
    let parameter: RestoreCredentialIssuerParam = ctx.parameter_cursor().get()?;
    let state = host.state_mut();
    let registry_entry = state
        .credentials
        .entry(parameter.credential_id)
        .occupied_or(ContractError::CredentialNotFound)?;

    let now = ctx.metadata().slot_time();
    let holder_id = registry_entry.holder_id;
    drop(registry_entry);

    let credential_id = parameter.credential_id;

    host.state_mut().restore_credential(now, credential_id)?;
    logger.log(&CredentialEvent::Restore(RestoreCredentialEvent {
        credential_id,
        holder_id,
        reason: parameter.reason,
    }))?;
    Ok(())
}

#[concordium_cfg_test]
mod tests {

    use super::*;
    use quickcheck::*;
    use test_infrastructure::*;

    impl Arbitrary for CredentialID {
        fn arbitrary(g: &mut Gen) -> CredentialID {
            CredentialID {
                id: Arbitrary::arbitrary(g),
            }
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            Box::new(self.id.shrink().map(|id| id.into()))
        }
    }

    impl Arbitrary for SchemaRef {
        fn arbitrary(g: &mut Gen) -> SchemaRef {
            (MetadataUrl {
                url:  Arbitrary::arbitrary(g),
                hash: if Arbitrary::arbitrary(g) {
                    Some([0u8; 32].map(|_| Arbitrary::arbitrary(g)))
                } else {
                    None
                },
            })
            .into()
        }
    }

    // It is convenient to use arbitrary data even for simple properites, because it
    // allows us to avoid defining input data manually.
    impl Arbitrary for CredentialInfo {
        fn arbitrary(g: &mut Gen) -> Self {
            CredentialInfo {
                holder_id:        PublicKeyEd25519([0u8; 32].map(|_| Arbitrary::arbitrary(g))),
                holder_revocable: Arbitrary::arbitrary(g),
                commitment:       Arbitrary::arbitrary(g),
                credential_type:  Arbitrary::arbitrary(g),
                valid_from:       Arbitrary::arbitrary(g),
                valid_until:      Arbitrary::arbitrary(g),
            }
        }
    }

    // A wrapper for an array for implementing an `Arbitrary` instance
    #[derive(Clone, Debug)]
    struct Array32u8([u8; 32]);

    impl Arbitrary for Array32u8 {
        fn arbitrary(g: &mut Gen) -> Array32u8 {
            Array32u8([0u8; 32].map(|_| Arbitrary::arbitrary(g)))
        }
    }

    const ISSUER_ACCOUNT: AccountAddress = AccountAddress([0u8; 32]);
    const ISSUER_URL: &str = "https://example-university.com/diplomas/university-vc-metadata.json";
    const ACCOUNT_0: AccountAddress = AccountAddress([0u8; 32]);
    const ADDRESS_0: Address = Address::Account(ACCOUNT_0);
    const PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([
        158, 227, 186, 15, 248, 246, 229, 189, 113, 194, 89, 206, 199, 166, 128, 15, 193, 2, 85,
        21, 217, 50, 11, 44, 140, 144, 10, 192, 191, 58, 124, 77,
    ]);
    const SIGNATURE: SignatureEd25519 = SignatureEd25519([
        20, 81, 176, 61, 69, 213, 173, 93, 241, 158, 23, 201, 244, 38, 69, 168, 3, 17, 96, 73, 34,
        43, 28, 240, 252, 255, 89, 189, 116, 29, 37, 214, 155, 229, 160, 14, 50, 49, 116, 106, 112,
        11, 146, 130, 130, 121, 193, 203, 87, 101, 76, 172, 208, 49, 158, 26, 184, 165, 117, 191,
        149, 86, 227, 8,
    ]);

    /// A helper that returns a credential that is not revoked, cannot expire
    /// and is immediately activated. It is also possible to revoke it by the
    /// holder.
    fn credential_entry<S: HasStateApi>(state_builder: &mut StateBuilder<S>) -> CredentialEntry<S> {
        CredentialEntry {
            credential_data:  state_builder.new_box(CredentialData {
                commitment:      [0u8; 48].to_vec(),
                credential_type: "ExampleSchema".to_string(),
            }),
            valid_from:       None,
            valid_until:      None,
            holder_id:        PUBLIC_KEY,
            holder_revocable: true,
            revocation_nonce: 0,
            revoked:          false,
        }
    }

    fn issuer_metadata() -> MetadataUrl {
        MetadataUrl {
            url:  ISSUER_URL.to_string(),
            hash: None,
        }
    }

    fn get_credential_schema() -> (CredentialType, SchemaRef) {
        ("ExampleSchema".to_string(), SchemaRef {
            schema_ref: MetadataUrl {
                url:  "https://example.com/schema.json".to_string(),
                hash: None,
            },
        })
    }

    #[concordium_test]
    /// Test that initializing the contract succeeds with some state.
    fn test_init() {
        let university_issuer = issuer_metadata();

        let mut ctx = TestInitContext::empty();
        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();

        ctx.set_init_origin(ISSUER_ACCOUNT);

        let parameter_bytes = to_bytes(&university_issuer);
        ctx.set_parameter(&parameter_bytes);

        let state_result = init(&ctx, &mut state_builder, &mut logger);
        state_result.expect_report("Contract initialization results in an error");

        claim_eq!(
            logger.logs[0],
            to_bytes(&CredentialEvent::Metadata(IssuerMetadataEvent {
                metadata_url: university_issuer,
            })),
            "Incorrect issuer metadata event logged"
        );
    }

    /// Not expired and not revoked credential is `Active`
    #[concordium_test]
    fn test_get_status_active() {
        let mut state_builder = TestStateBuilder::new();
        let entry = credential_entry(&mut state_builder);
        let now = Timestamp::from_timestamp_millis(10);
        let expected = CredentialStatus::Active;
        let status = entry.get_status(now);
        claim_eq!(
            status,
            CredentialStatus::Active,
            "Expected status {:?}, got {:?}",
            expected,
            status
        );
    }

    /// If `valid_until` is in the past, the credential is `Expired`, provided
    /// that it wasn't revoked.
    #[concordium_test]
    fn test_get_status_expired() {
        let mut state_builder = TestStateBuilder::new();
        let mut entry = credential_entry(&mut state_builder);
        claim!(!entry.revoked);
        let now = Timestamp::from_timestamp_millis(10);
        // Set `valid_until` to time preceeding `now`.
        entry.valid_until = Some(Timestamp::from_timestamp_millis(0));
        let expected = CredentialStatus::Expired;
        let status = entry.get_status(now);
        claim_eq!(status, expected, "Expected status {:?}, got {:?}", expected, status);
    }

    /// If `valid_from` if in the future, the status is `NotActivated`, provided
    /// that it wasn't revoked.
    #[concordium_test]
    fn test_get_status_not_activated() {
        let mut state_builder = TestStateBuilder::new();
        let mut entry = credential_entry(&mut state_builder);
        claim!(!entry.revoked);
        let now = Timestamp::from_timestamp_millis(10);
        // Set `valid_from` to time ahead of `now`.
        entry.valid_from = Some(Timestamp::from_timestamp_millis(20));
        let expected = CredentialStatus::NotActivated;
        let status = entry.get_status(now);
        claim_eq!(status, expected, "Expected status {:?}, got {:?}", expected, status);
    }

    /// Property: once the `revoked` flag is set to `true`, the status is
    /// always `Revoked` regardless of the valid_from and valid_until values
    #[concordium_quickcheck]
    fn prop_revoked_stays_revoked(data: CredentialInfo, nonce: u64, now: Timestamp) -> bool {
        let mut state_builder = TestStateBuilder::new();
        let entry = CredentialEntry {
            holder_id:        data.holder_id,
            credential_data:  state_builder.new_box(CredentialData {
                commitment:      data.commitment,
                credential_type: data.credential_type,
            }),
            revocation_nonce: nonce,
            holder_revocable: data.holder_revocable,
            valid_from:       data.valid_from,
            valid_until:      data.valid_until,
            revoked:          true,
        };
        entry.get_status(now) == CredentialStatus::Revoked
    }

    /// Property: registering a credential and then querying it results in the
    /// same credential data, which is not revoked and has nonce = `0`
    #[concordium_quickcheck]
    fn prop_register_credential(
        credential_id: CredentialID,
        credential_type: CredentialType,
        schema_ref: SchemaRef,
        mut data: CredentialInfo,
        now: Timestamp,
    ) -> bool {
        // Set credential type consistent with the schema registry
        data.credential_type = credential_type.clone();
        let mut state_builder = TestStateBuilder::new();
        let mut state = State::new(&mut state_builder, ISSUER_ACCOUNT, issuer_metadata());
        let schema_result = state.add_schema(credential_type, schema_ref);
        let register_result = state.register_credential(credential_id, &data, &mut state_builder);
        let query_result = state.view_credential_info(credential_id);
        let status = state.view_credential_status(now, credential_id);
        if let Ok(fetched_data) = query_result {
            schema_result.is_ok()
                && register_result.is_ok()
                && status.map_or(false, |x| x != CredentialStatus::Revoked)
                && (fetched_data.credential_info == data)
                && fetched_data.revocation_nonce == 0
        } else {
            false
        }
    }

    /// Property: if a credential is revoked successfully, the status changes to
    /// `Revoked`. The test is designed in such a way that the revocation is
    /// expeced to succeed.
    #[concordium_quickcheck]
    fn prop_revocation(
        credential_id: CredentialID,
        credential_type: CredentialType,
        schema_ref: SchemaRef,
        mut data: CredentialInfo,
    ) -> bool {
        // Set credential type consistent with the schema registry
        data.credential_type = credential_type.clone();
        let mut state_builder = TestStateBuilder::new();
        let mut state = State::new(&mut state_builder, ISSUER_ACCOUNT, issuer_metadata());
        let schema_result = state.add_schema(credential_type, schema_ref);
        let register_result = state.register_credential(credential_id, &data, &mut state_builder);

        // Make sure that the credential has not expired yet
        let now = Timestamp::from_timestamp_millis(0);
        let revocation_result = state.revoke_credential(now, credential_id);
        let status_result = state.view_credential_status(now, credential_id);
        schema_result.is_ok()
            && register_result.is_ok()
            && revocation_result.is_ok()
            && status_result == Ok(CredentialStatus::Revoked)
    }

    /// Property: revoking and then restoring a credential gives the same status
    /// as before revocation. In this case, restoring always succeeds.
    #[concordium_quickcheck]
    fn prop_revoke_restore(
        credential_id: CredentialID,
        credential_type: CredentialType,
        schema_ref: SchemaRef,
        mut data: CredentialInfo,
    ) -> bool {
        // Set credential type consistent with the schema registry
        data.credential_type = credential_type.clone();
        let mut state_builder = TestStateBuilder::new();
        let mut state = State::new(&mut state_builder, ISSUER_ACCOUNT, issuer_metadata());
        let schema_result = state.add_schema(credential_type, schema_ref);
        let register_result = state.register_credential(credential_id, &data, &mut state_builder);

        // Make sure that the credential has not expired yet
        let now = Timestamp::from_timestamp_millis(0);

        // Get original status
        let original_status = state
            .view_credential_status(now, credential_id)
            .expect_report("Status query expected to succed");

        let revocation_result = state.revoke_credential(now, credential_id);
        let restoring_result = state.restore_credential(now, credential_id);
        let status_after_restoring = state
            .view_credential_status(now, credential_id)
            .expect_report("Status query expected to succed");
        schema_result.is_ok()
            && register_result.is_ok()
            && revocation_result.is_ok()
            && restoring_result.is_ok()
            && original_status == status_after_restoring
    }

    /// Property: registering an issuer key and querying it results in the same
    /// value
    #[concordium_quickcheck]
    fn prop_register_issuer_keys(key_index: u8, pk_bytes: Array32u8) -> bool {
        let mut state_builder = TestStateBuilder::new();
        let Array32u8(bytes) = pk_bytes;
        let pk = PublicKeyEd25519(bytes);
        let mut state = State::new(&mut state_builder, ISSUER_ACCOUNT, issuer_metadata());
        let register_result = state.register_issuer_key(key_index, PublicKeyEd25519(bytes));
        let query_result = state.view_issuer_keys();
        register_result.is_ok() && query_result.contains(&(key_index, pk))
    }

    /// Property: registering a revocation key and querying it results in the
    /// same value
    #[concordium_quickcheck]
    fn prop_register_revocation_key(key_index: u8, pk_bytes: Array32u8) -> bool {
        let mut state_builder = TestStateBuilder::new();
        let Array32u8(bytes) = pk_bytes;
        let pk = PublicKeyEd25519(bytes);
        let mut state = State::new(&mut state_builder, ISSUER_ACCOUNT, issuer_metadata());
        let register_result = state.register_revocation_key(key_index, PublicKeyEd25519(bytes));
        let query_result = state.view_revocation_key(key_index);
        if let Ok(fetched_data) = query_result {
            register_result.is_ok() && fetched_data.0 == pk
        } else {
            false
        }
    }

    /// Test the credential registration entrypoint.
    #[concordium_test]
    fn test_contract_register_credential() {
        let credential_id = 123123123.into();
        let now = Timestamp::from_timestamp_millis(0);
        let contract = ContractAddress {
            index:    0,
            subindex: 0,
        };
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_owner(ACCOUNT_0);
        ctx.set_self_address(contract);
        ctx.set_metadata_slot_time(now);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::new(&mut state_builder, ISSUER_ACCOUNT, issuer_metadata());
        let mut host = TestHost::new(state, state_builder);

        let entry = credential_entry(host.state_builder());

        // Create input parameters.

        let param = RegisterCredentialParameter {
            credential_id,
            credential_info: entry.info(),
        };
        let parameter_bytes = to_bytes(&param);
        ctx.set_parameter(&parameter_bytes);

        // Create a credential schema
        let (credential_type, schema_ref) = get_credential_schema();
        host.state_mut()
            .add_schema(credential_type.clone(), schema_ref.clone())
            .expect_report("Schema registration failed");

        // Create a credential
        let res = contract_register_credential(&ctx, &mut host, &mut logger);

        // Check that it was registered successfully
        claim!(res.is_ok(), "Credential registration failed");
        let fetched: CredentialQueryResponse = host
            .state()
            .view_credential_info(credential_id)
            .expect_report("Credential is expected to exist");
        claim_eq!(fetched.credential_info, entry.info(), "Credential info expected to be equal");
        claim_eq!(fetched.revocation_nonce, 0, "Revocation nonce expected to be 0");

        let status = host
            .state()
            .view_credential_status(now, credential_id)
            .expect_report("Status query expected to succeed");
        claim_eq!(status, CredentialStatus::Active);

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&CredentialEvent::Register(CredentialEventData {
                credential_id,
                holder_id: PUBLIC_KEY,
                schema_ref,
                credential_type
            })),
            "Incorrect register credential event logged"
        );
    }

    /// Test the revoke credential entrypoint, when the holder revokes the
    /// credential.
    #[concordium_test]
    fn test_revoke_by_holder() {
        let credential_id = 123123123.into();
        let now = Timestamp::from_timestamp_millis(0);
        let contract = ContractAddress {
            index:    0,
            subindex: 0,
        };
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_owner(ISSUER_ACCOUNT);
        ctx.set_invoker(ISSUER_ACCOUNT);
        ctx.set_self_address(contract);
        ctx.set_metadata_slot_time(now);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::new(&mut state_builder, ISSUER_ACCOUNT, issuer_metadata());
        let mut host = TestHost::new(state, state_builder);

        let (state, state_builder) = host.state_and_builder();
        let entry = credential_entry(state_builder);
        let credential_info = entry.info();

        claim!(
            credential_info.holder_revocable,
            "Initial credential expected to be holder-revocable"
        );

        // Create a credential schema
        let (credential_type, schema_ref) = get_credential_schema();
        state
            .add_schema(credential_type, schema_ref.clone())
            .expect_report("Schema registration failed");

        // Create a credential the holder is going to revoke
        let res = state.register_credential(credential_id, &credential_info, state_builder);

        // Check that it was registered successfully
        claim!(res.is_ok(), "Credential registration failed");

        // Create singing data
        let signing_data = SigningData {
            contract_address: contract,
            nonce:            1,
            timestamp:        Timestamp::from_timestamp_millis(10000000000),
        };

        // Create input parematers for revocation.

        let revocation_reason = "Just because";

        let revoke_param = RevokeCredentialHolderParam {
            credential_id,
            signing_data,
            signature: SIGNATURE,
            reason: Some(revocation_reason.to_string().into()),
        };

        let parameter_bytes = to_bytes(&revoke_param);
        ctx.set_parameter(&parameter_bytes);

        let crypto_primitives = TestCryptoPrimitives::new();
        // Inovke `permit` function.
        let result: ContractResult<()> =
            contract_revoke_credential_holder(&ctx, &mut host, &mut logger, &crypto_primitives);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection: {:?}", result);

        // Check the status.
        let status = host
            .state()
            .view_credential_status(now, credential_id)
            .expect_report("Credential is expected to exist");
        claim_eq!(status, CredentialStatus::Revoked);

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&CredentialEvent::Revoke(RevokeCredentialEvent {
                credential_id,
                holder_id: PUBLIC_KEY,
                revoker: Revoker::Holder,
                reason: Some(revocation_reason.to_string().into())
            })),
            "Incorrect revoke credential event logged"
        );
    }

    /// Test the restore credential entrypoint.
    #[concordium_test]
    fn test_contract_restore_credential() {
        let credential_id = 123123123.into();
        let now = Timestamp::from_timestamp_millis(0);
        let contract = ContractAddress {
            index:    0,
            subindex: 0,
        };
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_owner(ACCOUNT_0);
        ctx.set_self_address(contract);
        ctx.set_metadata_slot_time(now);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::new(&mut state_builder, ISSUER_ACCOUNT, issuer_metadata());
        let mut host = TestHost::new(state, state_builder);

        let (state, state_builder) = host.state_and_builder();
        let entry = credential_entry(state_builder);
        let credential_info = entry.info();

        // Create a credential schema
        let (credential_type, schema_ref) = get_credential_schema();
        state
            .add_schema(credential_type, schema_ref.clone())
            .expect_report("Schema registration failed");

        // Create a credential the issuer is going to restore
        let res = state.register_credential(credential_id, &credential_info, state_builder);

        // Check that it was registered successfully
        claim!(res.is_ok(), "Credential registration failed");

        // Make sure the credeintial has `Revoked` status
        let revoke_res = state.revoke_credential(now, credential_id);

        // Check that the credential was revoked successfully.
        claim!(revoke_res.is_ok(), "Credential revocation failed");

        // Create input parameters.

        let param = RestoreCredentialIssuerParam {
            credential_id,
            reason: None,
        };
        let parameter_bytes = to_bytes(&param);
        ctx.set_parameter(&parameter_bytes);

        // Check the status before restoring.
        let status = host
            .state()
            .view_credential_status(now, credential_id)
            .expect_report("Credential is expected to exist");
        claim_eq!(status, CredentialStatus::Revoked, "Expected Revoked");

        // Call the restore credential entrypoint
        let res = contract_restore_credential(&ctx, &mut host, &mut logger);

        // Check that it was restored succesfully
        claim!(res.is_ok(), "Credential restoring failed");
        // Check the status after restoring.
        let status = host
            .state()
            .view_credential_status(now, credential_id)
            .expect_report("Credential is expected to exist");
        claim_eq!(status, CredentialStatus::Active, "Expected Active");

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&CredentialEvent::Restore(RestoreCredentialEvent {
                credential_id,
                holder_id: PUBLIC_KEY,
                reason: None
            })),
            "Incorrect revoke credential event logged"
        );
    }
}