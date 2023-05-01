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
//! - registration of a new credential;
//! - updating an existing credential;
//! - revoking a credential;
//! - register a public key;
//! - register a revocation authority key.
//!
//! Revocation authorities are some entities chosen by the issuer that has
//! revocation capabilities. Their public keys are registered by the issuer and
//! a revocation authority signs a revocation message with the corresponding
//! secret key.
//!
//! ## Holder's functionality
//!
//! - revoking a credential by signing a revocation message.
//!
//! Revocation authority's functionality
//!
//! - revoking a credential by signing a revocation message.
//!
//! ## Verifier's functionality
//!
//! - view credential status to verify VC validity.
//! - view credential data to verify proofs (verifiable presentations) requested
//!   from holders.
use concordium_cis2::*;
use concordium_std::*;
use core::fmt::Debug;

/// The type for a credential identifier.
/// The uuidv4 identifier is generated externally by the issuer.
/// The schema for the identifier does not support the usual textual
/// representation of uuid, it is treated as a `u128` number.
#[derive(Serialize, SchemaType, PartialEq, Eq, Clone, Copy, Debug)]
struct Uuidv4 {
    id: u128,
}

impl From<u128> for Uuidv4 {
    fn from(id: u128) -> Self {
        Uuidv4 {
            id,
        }
    }
}

/// A schema reference is a schema URL or DID address pointing to the JSON
/// schema for a verifiable credential.
#[derive(Serialize, SchemaType, PartialEq, Clone, Debug)]
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

/// Public verifiable credential data
#[derive(Serialize, SchemaType, PartialEq, Clone, Debug)]
pub struct CredentialData {
    /// The holder's identifier is a public key.
    holder_id:        PublicKeyEd25519,
    /// If this flag is set to `true` the holder can send a signed message to
    /// revoke their credential.
    holder_revocable: bool,
    /// A vector Pedersen comminment to the attributes of the verifiable
    /// credential.
    commitment:       Vec<u8>,
    /// A reference to the credential's JSON schema. It also sevres as the
    /// credential type.
    schema_ref:       SchemaRef,
    /// The date from which the credential is considered valid. `None`
    /// corresponsds to a credential that is valid immediately after being
    /// issued.
    valid_from:       Option<Timestamp>,
    /// After this date, the credential becomes expired. `None` corresponds to a
    /// credential that cannot expire.
    valid_until:      Option<Timestamp>,
}

/// Public verifiable credential data, revocation flag and nonce
#[derive(Serialize, SchemaType, PartialEq, Clone, Debug)]
pub struct CredentialEntry {
    credential_data:  CredentialData,
    /// The nonce is used to avoid replay attacks when checking the holder's
    /// signature on a revocation message.
    revocation_nonce: u64,
    // Revocation flag
    revoked:          bool,
}

impl CredentialEntry {
    /// Compute the credential status based on validity dates and the revocation
    /// flag. If a VC is revoked the status will be `Revoked` regardless the
    /// validity dates.
    fn get_status(&self, now: Timestamp) -> CredentialStatus {
        if self.revoked {
            return CredentialStatus::Revoked;
        }
        if let Some(valid_until) = self.credential_data.valid_until {
            if valid_until < now {
                return CredentialStatus::Expired;
            }
        }
        if let Some(valid_until) = self.credential_data.valid_from {
            if now < valid_until {
                return CredentialStatus::NotActivated;
            }
        }
        CredentialStatus::Active
    }
}

/// The registry state.
// NOTE: keys are stored in a map, so one can refer to the keys by "names" in this case represented
// by numbers. The keys could be removed and added, but external references (e.g. in DIDs) should
// still be valid (unless a key was deliberatly removed)
#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
pub struct State<S> {
    issuer_metadata: MetadataUrl,
    issuer_keys:     StateMap<u8, PublicKeyEd25519, S>,
    revocation_keys: StateMap<u8, (PublicKeyEd25519, u64), S>,
    credentials:     StateMap<Uuidv4, CredentialEntry, S>,
}

/// Contract Errors.
#[derive(Debug, PartialEq, Eq, Reject, Serial, SchemaType)]
enum ContractError {
    #[from(ParseError)]
    ParseParamsError,
    CredentialNotFound,
    CredentialAlreadyExists,
    IncorrectStatusBeforeRevocation,
    KeyAlreadyExists,
    KeyNotFound,
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
    fn new(state_builder: &mut StateBuilder<S>, issuer_metadata: MetadataUrl) -> Self {
        State {
            issuer_metadata,
            issuer_keys: state_builder.new_map(),
            revocation_keys: state_builder.new_map(),
            credentials: state_builder.new_map(),
        }
    }

    fn view_credential_data(&self, credential_id: Uuidv4) -> ContractResult<CredentialEntry> {
        self.credentials
            .get(&credential_id)
            .map(|x| x.clone())
            .ok_or(ContractError::CredentialNotFound)
    }

    fn view_credential_status(
        &self,
        now: Timestamp,
        credential_id: Uuidv4,
    ) -> ContractResult<CredentialStatus> {
        self.credentials
            .get(&credential_id)
            .map(|x| x.get_status(now))
            .ok_or(ContractError::CredentialNotFound)
    }

    fn register_credential(
        &mut self,
        credential_id: Uuidv4,
        credential_data: &CredentialData,
    ) -> ContractResult<()> {
        let credential_entry = CredentialEntry {
            credential_data:  credential_data.clone(),
            revocation_nonce: 0,
            revoked:          false,
        };
        let res = self.credentials.insert(credential_id, credential_entry);
        ensure!(res.is_none(), ContractError::CredentialAlreadyExists);
        Ok(())
    }

    fn update_credential(
        &mut self,
        credential_id: Uuidv4,
        credential_data: &CredentialData,
    ) -> ContractResult<()> {
        let mut registry_entry =
            self.credentials.entry(credential_id).occupied_or(ContractError::CredentialNotFound)?;
        registry_entry.credential_data = credential_data.clone();
        Ok(())
    }

    fn revoke_credential(&mut self, now: Timestamp, credential_id: Uuidv4) -> ContractResult<()> {
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

    fn view_issuer_metadata(&self) -> MetadataUrl { self.issuer_metadata.clone() }

    fn update_issuer_metadata(&mut self, issuer_metadata: &MetadataUrl) {
        self.issuer_metadata = issuer_metadata.clone()
    }
}

/// Data for events of registering and updating a credential.
/// Used by the tagged event `CredentialEvent`.
#[derive(Serialize, SchemaType)]
struct CredentialEventData {
    /// An identifier of a credential being registered/updated.
    credential_id: Uuidv4,
    /// A public key of the credential's holder.
    holder_id:     PublicKeyEd25519,
    /// A reference to the credential JSON schema.
    schema_ref:    SchemaRef,
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

/// Revocation reason.
/// The string is of a limited size of 256 bytes in order to fit into a single
/// log entry along with other data logged on revocation.
#[derive(Serialize, SchemaType)]
struct RevokeReason {
    #[concordium(size_length = 1)]
    reason: String,
}

impl From<String> for RevokeReason {
    fn from(reason: String) -> Self {
        RevokeReason {
            reason,
        }
    }
}

/// An untagged revocation event.
/// For a tagged version use `CredentialEvent`.
#[derive(Serialize, SchemaType)]
struct RevokeCredentialEvent {
    /// An identifier of a credential being revoked.
    credential_id: Uuidv4,
    /// A public key of the credential's holder.
    holder_id:     PublicKeyEd25519,
    /// Who revokes the credential.
    revoker:       Revoker,
    /// An optional text clarifying the revocation reasons.
    /// The issuer can use this field to comment on the revocation, so the
    /// holder can observe it in the wallet.
    reason:        Option<RevokeReason>,
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
    /// Credentila revocation event.
    Revoke(RevokeCredentialEvent),
}

/// Init function that creates a fresh registry state given the issuer's
/// metadata
#[init(contract = "credential_registry", parameter = "MetadataUrl", event = "CredentialEvent")]
fn init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    let issuer_metadata: MetadataUrl = ctx.parameter_cursor().get()?;
    Ok(State::new(state_builder, issuer_metadata))
}

fn sender_is_owner(ctx: &impl HasReceiveContext) -> bool {
    ctx.sender().matches_account(&ctx.owner())
}

/// Response to a credential data query.
#[derive(Serialize, SchemaType)]
pub struct CredentialEntryResponse {
    /// The holder's identifier is a public key.
    holder_id:        PublicKeyEd25519,
    /// If this flag is set to `true` the holder can send a signed message to
    /// revoke their credential.
    holder_revocable: bool,
    /// A vector Pedersen comminment to the attributes of the verifiable
    /// credential.
    commitment:       Vec<u8>,
    /// A reference to the credential's JSON schema. It also sevres as the
    /// credential type.
    schema_ref:       SchemaRef,
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
    // Revocation flag
    revoked:          bool,
}

/// A view entrypoint for looking up an entry in the registry by id.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The credential with the given id does not exist.
#[receive(
    contract = "credential_registry",
    name = "viewCredentialEntry",
    parameter = "Uuidv4",
    error = "ContractError",
    return_value = "CredentialEntry"
)]
fn contract_view_credential_entry<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<CredentialEntryResponse, ContractError> {
    let credential_id = ctx.parameter_cursor().get()?;
    let data = host.state().view_credential_data(credential_id)?;
    Ok(CredentialEntryResponse {
        holder_id:        data.credential_data.holder_id,
        holder_revocable: data.credential_data.holder_revocable,
        commitment:       data.credential_data.commitment,
        schema_ref:       data.credential_data.schema_ref,
        valid_from:       data.credential_data.valid_from,
        valid_until:      data.credential_data.valid_until,
        revocation_nonce: data.revocation_nonce,
        revoked:          data.revoked,
    })
}

/// A view entrypoint querying the credential's status.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The credential with the given id does not exist.
#[receive(
    contract = "credential_registry",
    name = "viewCredentialStatus",
    parameter = "Uuidv4",
    error = "ContractError",
    return_value = "CredentialStatus"
)]
fn contract_view_credential_status<S: HasStateApi>(
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
pub struct CredentialDataParameter {
    credential_id:   Uuidv4,
    credential_data: CredentialData,
}

/// Register a new credential with the given id and data.
/// Logs RegisterCredentialEvent.
///
/// Can be called by the owner only.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The caller is not the contract's owner
/// - An entry with the given credential id already exists
/// - Fails to log RegisterCredentialEvent
#[receive(
    contract = "credential_registry",
    name = "registerCredential",
    parameter = "CredentialDataParameter",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_register_credeintial<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    ensure!(sender_is_owner(ctx), ContractError::NotAuthorized);
    let parameter: CredentialDataParameter = ctx.parameter_cursor().get()?;
    host.state_mut().register_credential(parameter.credential_id, &parameter.credential_data)?;
    logger.log(&CredentialEvent::Register(CredentialEventData {
        credential_id: parameter.credential_id,
        holder_id:     parameter.credential_data.holder_id,
        schema_ref:    parameter.credential_data.schema_ref,
    }))?;
    Ok(())
}

/// Update an existing credential with the given id and data.
/// Logs UpdateCredentialEvent.
///
/// Can be called only by the owner.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The caller is not the contract's owner
/// - An entry with the given credential id does not exist
/// - Fails to log UpdateCredentialEvent
#[receive(
    contract = "credential_registry",
    name = "updateCredential",
    parameter = "CredentialDataParameter",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_update_credential<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    ensure!(sender_is_owner(ctx), ContractError::NotAuthorized);
    let parameter: CredentialDataParameter = ctx.parameter_cursor().get()?;
    host.state_mut().update_credential(parameter.credential_id, &parameter.credential_data)?;
    logger.log(&CredentialEvent::Update(CredentialEventData {
        credential_id: parameter.credential_id,
        holder_id:     parameter.credential_data.holder_id,
        schema_ref:    parameter.credential_data.schema_ref,
    }))?;
    Ok(())
}

#[derive(Serialize, SchemaType)]
struct SigningData {
    /// The contract_address that the signature is intended for.
    contract_address: ContractAddress,
    /// A nonce to prevent replay attacks.
    nonce:            u64,
    /// A timestamp to make signatures expire.
    timestamp:        Timestamp,
}

/// The parameter type for the contract function `revokeCredential`.
/// Contains credential id, and optionally a signature with some meta
/// information.
/// If `signed` is present, the message is formed from the bytes of
/// `credential_id` and fields of `SigningData`.
/// If `revocation_key_index` is present, it is used for authorization,
/// otherwize the holder's key is used.
#[derive(Serialize, SchemaType)]
pub struct RevokeCredentialParam {
    credential_id:        Uuidv4,
    signed:               Option<(SigningData, SignatureEd25519)>,
    revocation_key_index: Option<u8>,
    reason:               Option<RevokeReason>,
}

/// Performs authorization based on the signature and the public key
/// The message is build from serialized `credential_id` and `signing_data`
fn authorize_with_signature(
    crypto_primitives: &impl HasCryptoPrimitives,
    ctx: &impl HasReceiveContext,
    nonce: u64,
    public_key: PublicKeyEd25519,
    credential_id: Uuidv4,
    signing_data: SigningData,
    signature: SignatureEd25519,
) -> Result<(), ContractError> {
    // Check the nonce to prevent replay attacks.
    ensure_eq!(signing_data.nonce, nonce, ContractError::NonceMismatch);

    // Check that the signature was intended for this contract.
    ensure_eq!(signing_data.contract_address, ctx.self_address(), ContractError::WrongContract);

    // Check signature is not expired.
    ensure!(signing_data.timestamp > ctx.metadata().slot_time(), ContractError::ExpiredSignature);

    // Prepare the message, as it is signed by the wallet.
    // Note that the message is prepended by the account address sending the
    // transaction and 8 zero bytes.
    // TODO: change this if we decide how to the wallet sings the message with a key
    // generated for a credential (not an account key)
    let mut msg_prepend = Vec::with_capacity(32 + 8);
    unsafe { msg_prepend.set_len(msg_prepend.capacity()) };
    msg_prepend[0..32].copy_from_slice(ctx.invoker().as_ref());
    msg_prepend[32..40].copy_from_slice(&[0u8; 8]);

    let mut message_bytes = Vec::new();
    credential_id
        .serial::<Vec<_>>(&mut message_bytes)
        .map_err(|_| ContractError::SerializationError)?;
    signing_data.serial(&mut message_bytes).map_err(|_| ContractError::SerializationError)?;

    // Calculate the message hash.
    let message_hash =
        crypto_primitives.hash_sha2_256(&[&msg_prepend[0..40], &message_bytes].concat()).0;

    // Check signature.
    ensure!(
        crypto_primitives.verify_ed25519_signature(public_key, signature, &message_hash),
        ContractError::WrongSignature
    );
    Ok(())
}

/// Revoke a credential.
///
/// Authentication depends on who is revoking.
///
/// - If the message is not signed, it is assumed that the issuer is calling the
///   entrypoint.
///  In this case, check whether the caller is if the caller is the contract's
/// owner.
/// - If the message is signed and no key index is given, it is assumed that the
///   holder is calling the entrypoint.
///  In this case, verify the signature with the holder's public key, which is
/// stored in the credential entry (`holder_id`).
/// - If the message is signed and a key index is given, it is assumed that a
///   revocation authority is calling the entrypoint.
///  In this case, verify the signature with the revocation authority's public
/// key, which is stored in `revocation_keys`.
///
///  Logs RevokeCredentialEvent with the revoker defined as it is described
/// above.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Depening on the authentication
///     - issuer: The caller is not the contract's owner
///     - holder: signature validation has failed
///     - revocation authority: no entry for the key index or signature
///       validation has failed
/// - An entry with the given credential id does not exist
/// - The credential status is not one of `Active` or `NotActivated`
/// - Fails to log RevokeCredentialEvent
#[receive(
    contract = "credential_registry",
    name = "revokeCredential",
    parameter = "RevokeCredentialParam",
    error = "ContractError",
    crypto_primitives,
    enable_logger,
    mutable
)]
fn contract_revoke_credeintial<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> Result<(), ContractError> {
    let parameter: RevokeCredentialParam = ctx.parameter_cursor().get()?;

    let state = host.state_mut();
    let mut registry_entry = state
        .credentials
        .entry(parameter.credential_id)
        .occupied_or(ContractError::CredentialNotFound)?;

    // By default, the issuer is the revoker
    let mut revoker = Revoker::Issuer;

    // Authorization depends on whether the calls is signed
    match parameter.signed {
        None => {
            // Not signed - authorize the owner (issuer).
            ensure!(sender_is_owner(ctx), ContractError::NotAuthorized)
        }
        Some((signing_data, signature)) => {
            // Signed - check the revocation key.
            match parameter.revocation_key_index {
                None => {
                    // No revocation key index - authorize the holder.

                    // Set the revoker to be the holder.
                    revoker = Revoker::Holder;

                    // Only holder-revocable entries can be revoked by the holder.
                    ensure!(
                        registry_entry.credential_data.holder_revocable,
                        ContractError::NotAuthorized
                    );

                    // Update the nonce.
                    registry_entry.revocation_nonce += 1;

                    // Get the public key and the current nonce.
                    let public_key = registry_entry.credential_data.holder_id;
                    let nonce = registry_entry.revocation_nonce;

                    authorize_with_signature(
                        crypto_primitives,
                        ctx,
                        nonce,
                        public_key,
                        parameter.credential_id,
                        signing_data,
                        signature,
                    )?;
                }

                Some(key_index) => {
                    // Revocation key index is present - authorize the revocation authority.

                    let mut entry = state
                        .revocation_keys
                        .entry(key_index)
                        .occupied_or(ContractError::CredentialNotFound)?;

                    // Update the nonce.
                    entry.1 += 1;

                    let nonce = entry.1;
                    let public_key = entry.0;

                    // Set the revoker to be the revocation authority.
                    revoker = Revoker::Other(public_key);

                    authorize_with_signature(
                        crypto_primitives,
                        ctx,
                        nonce,
                        public_key,
                        parameter.credential_id,
                        signing_data,
                        signature,
                    )?;
                }
            }
        }
    }
    let credential_id = ctx.parameter_cursor().get()?;
    let now = ctx.metadata().slot_time();
    let holder_id = registry_entry.credential_data.holder_id;
    drop(registry_entry);
    state.revoke_credential(now, credential_id)?;
    logger.log(&RevokeCredentialEvent {
        credential_id,
        holder_id,
        reason: parameter.reason,
        revoker,
    })?;
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
    ensure!(sender_is_owner(ctx), ContractError::NotAuthorized);
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
    ensure!(sender_is_owner(ctx), ContractError::NotAuthorized);
    let RemovePublicKeyParameters(parameters) = ctx.parameter_cursor().get()?;
    for index in parameters {
        host.state_mut().remove_issuer_key(index)?;
    }
    Ok(())
}

/// Register revocation authorities public keys.
/// These keys are used to authorize the revocation (applies to the whole
/// registry). Only the owner can call the entrypoint.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Some of the key indices already exist.
/// - The caller is not the contract's owner.
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
    ensure!(sender_is_owner(ctx), ContractError::NotAuthorized);
    let RegisterPublicKeyParameters(parameters) = ctx.parameter_cursor().get()?;
    for parameter in parameters {
        host.state_mut().register_revocation_key(parameter.key_index, parameter.key)?;
    }
    Ok(())
}

/// Remove revocation authorities public keys.
/// Only the owner can call the entrypoint.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Some of the key indices do not exist.
/// - The caller is not the contract's owner.
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
    ensure!(sender_is_owner(ctx), ContractError::NotAuthorized);
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
    name = "viewRevocationKey",
    parameter = "u8",
    error = "ContractError",
    return_value = "Vec<(PublicKeyEd25519, u64)>",
    mutable
)]
fn contract_view_revocation_key<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(PublicKeyEd25519, u64), ContractError> {
    let index = ctx.parameter_cursor().get()?;
    host.state().view_revocation_key(index)
}

/// A view entrypoint that returns a vector of issuer's keys.
#[receive(
    contract = "credential_registry",
    name = "viewIssuerKeys",
    error = "ContractError",
    return_value = "Vec<(u8, PublicKeyEd25519)>"
)]
fn contract_view_issuer_keys<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<Vec<(u8, PublicKeyEd25519)>, ContractError> {
    let keys = host.state().view_issuer_keys();
    Ok(keys)
}

/// A vew entrypoint to get the metadata URL and checksum.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "credential_registry",
    name = "viewIssuerMetadata",
    error = "ContractError",
    return_value = "MetadataUrl"
)]
fn contract_view_issuer_metadata<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<MetadataUrl, ContractError> {
    Ok(host.state().view_issuer_metadata())
}

/// Update issuer's metadata
///
/// It rejects if:
///  - It fails to parse the parameter.
#[receive(
    contract = "credential_registry",
    name = "updateIssuerMetadata",
    parameter = "MetadataUrl",
    error = "ContractError",
    mutable
)]
fn contract_update_issuer_metadata<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(), ContractError> {
    ensure!(sender_is_owner(ctx), ContractError::NotAuthorized);
    let data = ctx.parameter_cursor().get()?;
    host.state_mut().update_issuer_metadata(&data);
    Ok(())
}

#[concordium_cfg_test]
mod tests {

    use super::*;
    use quickcheck::*;
    use test_infrastructure::*;

    impl Arbitrary for Uuidv4 {
        fn arbitrary(g: &mut Gen) -> Uuidv4 {
            Uuidv4 {
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
    impl Arbitrary for CredentialData {
        fn arbitrary(g: &mut Gen) -> CredentialData {
            CredentialData {
                holder_id:        PublicKeyEd25519([0u8; 32].map(|_| Arbitrary::arbitrary(g))),
                holder_revocable: Arbitrary::arbitrary(g),
                commitment:       Arbitrary::arbitrary(g),
                schema_ref:       Arbitrary::arbitrary(g),
                valid_from:       Arbitrary::arbitrary(g),
                valid_until:      Arbitrary::arbitrary(g),
            }
        }
    }

    impl Arbitrary for CredentialEntry {
        fn arbitrary(g: &mut Gen) -> CredentialEntry {
            CredentialEntry {
                credential_data:  Arbitrary::arbitrary(g),
                revocation_nonce: Arbitrary::arbitrary(g),
                revoked:          Arbitrary::arbitrary(g),
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

    const ISSUER_URL: &str = "https://example-university.com/diplomas/university-vc-metadata.json";
    const ACCOUNT_0: AccountAddress = AccountAddress([0u8; 32]);
    const ADDRESS_0: Address = Address::Account(ACCOUNT_0);
    const ACCOUNT_1: AccountAddress = AccountAddress([1u8; 32]);
    const PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([
        173, 21, 96, 108, 100, 77, 217, 90, 201, 81, 175, 214, 5, 35, 177, 170, 240, 206, 97, 142,
        229, 137, 217, 215, 110, 203, 231, 175, 119, 21, 48, 162,
    ]);
    const SIGNATURE: SignatureEd25519 = SignatureEd25519([
        105, 208, 126, 24, 233, 10, 86, 192, 92, 237, 158, 194, 166, 11, 70, 7, 167, 163, 80, 225,
        211, 21, 91, 219, 24, 175, 25, 16, 111, 18, 140, 255, 1, 5, 248, 175, 85, 20, 232, 140, 86,
        196, 81, 192, 75, 123, 125, 197, 89, 227, 230, 118, 121, 18, 230, 240, 242, 82, 99, 232,
        75, 118, 41, 12,
    ]);

    /// A helper that returns a credential that is not revoked, cannot expire
    /// and is immediately activated.
    fn credential_entry() -> CredentialEntry {
        CredentialEntry {
            credential_data:  CredentialData {
                holder_id:        PUBLIC_KEY,
                holder_revocable: true,
                commitment:       [0u8; 48].to_vec(),
                schema_ref:       (MetadataUrl {
                    url:  "".into(),
                    hash: None,
                })
                .into(),
                valid_from:       None,
                valid_until:      None,
            },
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

    #[concordium_test]
    /// Test that initializing the contract succeeds with some state.
    fn test_init() {
        let university_issuer = issuer_metadata();

        let mut ctx = TestInitContext::empty();

        let mut state_builder = TestStateBuilder::new();

        let parameter_bytes = to_bytes(&university_issuer);
        ctx.set_parameter(&parameter_bytes);

        let state_result = init(&ctx, &mut state_builder);
        state_result.expect_report("Contract initialization results in an error");
    }

    /// Not expired and not revoked credential is `Active`
    #[concordium_test]
    fn test_get_status_active() {
        let entry = credential_entry();
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
        let mut entry = credential_entry();
        claim!(!entry.revoked);
        let now = Timestamp::from_timestamp_millis(10);
        // Set `valid_until` to time preceeding `now`.
        entry.credential_data.valid_until = Some(Timestamp::from_timestamp_millis(0));
        let expected = CredentialStatus::Expired;
        let status = entry.get_status(now);
        claim_eq!(status, expected, "Expected status {:?}, got {:?}", expected, status);
    }

    /// If `valid_from` if in the future, the status is `NotActivated`, provided
    /// that it wasn't revoked.
    #[concordium_test]
    fn test_get_status_not_activated() {
        let mut entry = credential_entry();
        claim!(!entry.revoked);
        let now = Timestamp::from_timestamp_millis(10);
        // Set `valid_from` to time ahead of `now`.
        entry.credential_data.valid_from = Some(Timestamp::from_timestamp_millis(20));
        let expected = CredentialStatus::NotActivated;
        let status = entry.get_status(now);
        claim_eq!(status, expected, "Expected status {:?}, got {:?}", expected, status);
    }

    /// Property: once the `revoked` flag is set to `true`, the status is
    /// always `Revoked` regardless of the valid_from and valid_until values
    #[concordium_quickcheck]
    fn prop_revoked_stays_revoked(mut entry: CredentialEntry, now: Timestamp) -> bool {
        entry.revoked = true;
        entry.get_status(now) == CredentialStatus::Revoked
    }

    /// Property: registering a credential and then querying it results in the
    /// same credential data, which is not revoked and has nonce = `0`
    #[concordium_quickcheck]
    fn prop_register_view_credential(credential_id: Uuidv4, data: CredentialData) -> bool {
        let mut state_builder = TestStateBuilder::new();
        let mut state = State::new(&mut state_builder, issuer_metadata());
        let register_result = state.register_credential(credential_id, &data);
        let query_result = state.view_credential_data(credential_id);
        if let Ok(fetched_data) = query_result {
            register_result.is_ok()
                && (fetched_data.credential_data == data)
                && !fetched_data.revoked
                && fetched_data.revocation_nonce == 0
        } else {
            false
        }
    }

    /// Property: updating an existing credential and then querying it results
    /// in the same credential data. The update keeps intact the revocation
    /// flag and nonce.
    #[concordium_quickcheck]
    fn prop_update_view_credential(
        credential_id: Uuidv4,
        initial_entry: CredentialEntry,
        data: CredentialData,
    ) -> bool {
        let mut state_builder = TestStateBuilder::new();
        let mut state = State::new(&mut state_builder, issuer_metadata());
        state.credentials.insert(credential_id, initial_entry.clone());
        let register_result = state.update_credential(credential_id, &data);
        let query_result = state.view_credential_data(credential_id);
        if let Ok(fetched_data) = query_result {
            register_result.is_ok()
                && (fetched_data.credential_data == data)
                && (fetched_data.revoked == initial_entry.revoked)
                && (fetched_data.revocation_nonce == initial_entry.revocation_nonce)
        } else {
            false
        }
    }

    /// Property: if a credential is revoked successfully, the status changes to
    /// `Revoked`
    #[concordium_quickcheck]
    fn prop_revocation(credential_id: Uuidv4, data: CredentialData) -> TestResult {
        let mut state_builder = TestStateBuilder::new();
        let mut state = State::new(&mut state_builder, issuer_metadata());
        let register_result = state.register_credential(credential_id, &data);

        // make sure that the credential has not expired yet
        let now = Timestamp::from_timestamp_millis(0);
        let revocation_result = state.revoke_credential(now, credential_id);
        if register_result.is_err() || revocation_result.is_err() {
            // discard the test if the precondition is not satisfied
            return TestResult::discard();
        }
        let status_result = state.view_credential_status(now, credential_id);
        TestResult::from_bool(status_result == Ok(CredentialStatus::Revoked))
    }

    /// Property: registering an issuer key and querying it results in the same
    /// value
    #[concordium_quickcheck]
    fn prop_register_view_issuer_keys(key_index: u8, pk_bytes: Array32u8) -> bool {
        let mut state_builder = TestStateBuilder::new();
        let Array32u8(bytes) = pk_bytes;
        let pk = PublicKeyEd25519(bytes);
        let mut state = State::new(&mut state_builder, issuer_metadata());
        let register_result = state.register_issuer_key(key_index, PublicKeyEd25519(bytes));
        let query_result = state.view_issuer_keys();
        register_result.is_ok() && query_result.contains(&(key_index, pk))
    }

    /// Property: registering a revocation key and querying it results in the
    /// same value
    #[concordium_quickcheck]
    fn prop_register_view_revocation_key(key_index: u8, pk_bytes: Array32u8) -> bool {
        let mut state_builder = TestStateBuilder::new();
        let Array32u8(bytes) = pk_bytes;
        let pk = PublicKeyEd25519(bytes);
        let mut state = State::new(&mut state_builder, issuer_metadata());
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
        let state = State::new(&mut state_builder, issuer_metadata());
        let mut host = TestHost::new(state, state_builder);

        // Create input parameters.

        let param = CredentialDataParameter {
            credential_id,
            credential_data: credential_entry().credential_data,
        };
        let parameter_bytes = to_bytes(&param);
        ctx.set_parameter(&parameter_bytes);

        // Create a credential
        let res = contract_register_credeintial(&ctx, &mut host, &mut logger);

        // Check that it was registered successfully
        claim!(res.is_ok(), "Credential registration failed");
        let fetched = host
            .state()
            .view_credential_data(credential_id)
            .expect_report("Credential is expected to exist");
        claim_eq!(fetched.credential_data, credential_entry().credential_data);

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&CredentialEvent::Register(CredentialEventData {
                credential_id,
                holder_id: PUBLIC_KEY,
                schema_ref: (MetadataUrl {
                    url:  "".into(),
                    hash: None,
                })
                .into()
            })),
            "Incorrect register credential event logged"
        );
    }

    /// Test the credential update entrypoint.
    #[concordium_test]
    fn test_contract_update_credential() {
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
        let state = State::new(&mut state_builder, issuer_metadata());
        let mut host = TestHost::new(state, state_builder);

        // Create a credential to update
        let res = host
            .state_mut()
            .register_credential(credential_id, &credential_entry().credential_data);

        // Check that it was registered successfully
        claim!(res.is_ok(), "Credential registration failed");

        claim!(
            credential_entry().credential_data.holder_revocable,
            "Initial credential expected to be holder-revocable"
        );

        // Create input parameters.

        let mut new_credential_data = credential_entry().credential_data;
        new_credential_data.holder_revocable = false;

        let param = CredentialDataParameter {
            credential_id,
            credential_data: new_credential_data.clone(),
        };
        let parameter_bytes = to_bytes(&param);
        ctx.set_parameter(&parameter_bytes);

        // Create a credential
        let res = contract_update_credential(&ctx, &mut host, &mut logger);

        // Check that it was update successfully
        claim!(res.is_ok(), "Credential update failed");
        let fetched = host
            .state()
            .view_credential_data(credential_id)
            .expect_report("Credential is expected to exist");
        claim_eq!(fetched.credential_data, new_credential_data, "Data was not updated properly");

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&CredentialEvent::Update(CredentialEventData {
                credential_id,
                holder_id: PUBLIC_KEY,
                schema_ref: (MetadataUrl {
                    url:  "".into(),
                    hash: None,
                })
                .into()
            })),
            "Incorrect update credential event logged"
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
        ctx.set_owner(ACCOUNT_0);
        ctx.set_invoker(ACCOUNT_1);
        ctx.set_self_address(contract);
        ctx.set_metadata_slot_time(now);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::new(&mut state_builder, issuer_metadata());
        let mut host = TestHost::new(state, state_builder);

        claim!(
            credential_entry().credential_data.holder_revocable,
            "Initial credential expected to be holder-revocable"
        );

        // Create a credential the holder is going to revoke
        let res = host
            .state_mut()
            .register_credential(credential_id, &credential_entry().credential_data);

        // Check that it was registered successfully
        claim!(res.is_ok(), "Credential registration failed");

        // Create singing data
        let signig_data = SigningData {
            contract_address: contract,
            nonce:            1,
            timestamp:        Timestamp::from_timestamp_millis(10000000000),
        };

        // Create input parematers for revocation.

        let revocation_reason = "Just because";

        let revoke_param = RevokeCredentialParam {
            credential_id,
            signed: Some((signig_data, SIGNATURE)),
            revocation_key_index: None,
            reason: Some(revocation_reason.to_string().into()),
        };

        let parameter_bytes = to_bytes(&revoke_param);
        ctx.set_parameter(&parameter_bytes);

        let crypto_primitives = TestCryptoPrimitives::new();
        // Inovke `permit` function.
        let result: ContractResult<()> =
            contract_revoke_credeintial(&ctx, &mut host, &mut logger, &crypto_primitives);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection: {:?}", result);

        // Check the state.
        let status = host
            .state()
            .view_credential_status(now, credential_id)
            .expect_report("Credential is expected to exist");
        claim_eq!(status, CredentialStatus::Revoked);

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&RevokeCredentialEvent {
                credential_id,
                holder_id: PUBLIC_KEY,
                revoker: Revoker::Holder,
                reason: Some(revocation_reason.to_string().into())
            }),
            "Incorrect revoke credential event logged"
        );
    }
}
