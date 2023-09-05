//! This smart contract implements an example on-chain registry for the public
//! part of verifiable credentials (VCs).
//!
//! # Description
//!
//! The contract keeps track of credentials' public data, allows managing the
//! VC life cycle. and querying VCs data and status. The intended users are
//! issuers of VCs, holders of VCs, revocation authorities, and verifiers.
//!
//! When initializing a contract, the issuer provides a type and a schema
//! reference for the credentials in the registry. The schema reference points
//! to a JSON document describing the structure of verifiable credentials in the
//! registry (attributes and their types). If the issuer wants to issue
//! verifiable credentials of several types, they can deploy several instances
//! of this contract with different credential types.
//!
//! ## Issuer's  functionality
//!
{% if revocable_by_others %}//! - register/remove revocation authority keys;{% else %}//!{% endif %}
//! - register a new credential;
//! - revoke a credential;
//! - update the issuer's metadata;
//! - update the credential metadata;
{% if restorable %}//! - update credential schema reference;
//! - restore (cancel revocation of) a revoked credential.{% else %}//! - update credential schema reference.{% endif %}
//!
//! ## Holder's functionality
//!
//! - revoke a credential by signing a revocation message.
//!{% if revocable_by_others %}
//! ## Revocation authority's functionality
//!
//! Revocation authorities are some entities chosen by the issuer that have
//! revocation capabilities. Their public keys are registered by the issuer and
//! a revocation authority signs a revocation message with the corresponding
//! private key.
//!
//! - revoke a credential by signing a revocation message.{%endif%}
//!
//! ## Verifier's functionality
//!
//! - view credential status to verify VC validity;
//! - view credential data to verify proofs (verifiable presentations) requested
//!   from holders.
use concordium_std::*;

/// Credential type is a string that corresponds to the value of the "name"
/// attribute of the JSON credential schema.
#[derive(Serialize, SchemaType, PartialEq, Eq, Clone, Debug)]
struct CredentialType {
    #[concordium(size_length = 1)]
    credential_type: String,
}

/// A schema reference is a schema URL pointing to the JSON
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

/// Public data of a verifiable credential.
#[derive(Serial, DeserialWithState, Debug)]
#[concordium(state_parameter = "S")]
pub struct CredentialEntry<S: HasStateApi> {
    /// If this flag is set to `true` the holder can send a signed message to
    /// revoke their credential.
    holder_revocable: bool,
    /// The date from which the credential is considered valid.
    valid_from:       Timestamp,
    /// After this date, the credential becomes expired. `None` corresponds to a
    /// credential that cannot expire.
    valid_until:      Option<Timestamp>,
    /// The nonce is used to avoid replay attacks when checking the holder's
    /// signature on a revocation message.
    revocation_nonce: u64,
    /// Revocation flag
    revoked:          bool,
    /// Metadata URL of the credential (not to be confused with the metadata URL
    /// of the **issuer**).
    /// This data is only needed when credential info is requested. In other
    /// operations, `StateBox` defers loading the metadata url.
    metadata_url:     StateBox<MetadataUrl, S>,
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
        if now < self.valid_from {
            return CredentialStatus::NotActivated;
        }
        CredentialStatus::Active
    }

    fn info(&self, holder_id: CredentialHolderId) -> CredentialInfo {
        CredentialInfo {
            holder_id,
            holder_revocable: self.holder_revocable,
            valid_from: self.valid_from,
            valid_until: self.valid_until,
            metadata_url: self.metadata_url.clone(),
        }
    }
}

/// The registry state.
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
pub struct State<S: HasStateApi> {
    /// An account address of the issuer. It is used for authorization in
    /// entrypoints that can be called only by the issuer.
    issuer_account:      AccountAddress,
    /// The issuer's public key. It is used by off-chain code to verify
    /// signatures on credential data.
    issuer_key:          PublicKeyEd25519,
    /// A reference to the issuer metadata.
    issuer_metadata:     MetadataUrl,{% if revocable_by_others %}
    /// The currently active set of revocation keys.
    revocation_keys:     StateMap<PublicKeyEd25519, u64, S>,
    /// All revocation keys that have been used at any point in the past.
    all_revocation_keys: StateSet<PublicKeyEd25519, S>,{% endif %}
    /// Mapping of credential holders to entries.
    credentials:         StateMap<PublicKeyEd25519, CredentialEntry<S>, S>,
    /// A string representing the credential type. This string corresponds to
    /// the credential schema name in the JSON representation.
    credential_type:     CredentialType,
    /// A reference to a JSON document containing the credential schema for the
    /// given credential type.
    credential_schema:   SchemaRef,
}

/// Contract Errors.
#[derive(Debug, PartialEq, Eq, Reject, Serial, SchemaType)]
enum ContractError {
    #[from(ParseError)]
    ParseParamsError,
    CredentialNotFound,
    CredentialAlreadyExists,
    IncorrectStatusBeforeRevocation,
{% if restorable %}
    IncorrectStatusBeforeRestoring,
{% endif %}{% if revocable_by_others %}
    KeyAlreadyExists,
    KeyDoesNotExist,
{% else %}
    NotSupported,
{% endif %}
    NotAuthorized,
    NonceMismatch,
    WrongContract,
    WrongEntrypoint,
    ExpiredSignature,
    WrongSignature,
    SerializationError,
    LogFull,
    LogMalformed,

    ContractInvocationError,
    FailedUpgradeMissingModule,
    FailedUpgradeMissingContract,
    FailedUpgradeUnsupportedModuleVersion,
}

/// Mapping errors related to logging to ContractError.
impl From<LogError> for ContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

type ContractResult<A> = Result<A, ContractError>;

/// Credentials are identified by a holder's public key.
/// Each time a credential is issued, a fresh key pair is generated.
type CredentialHolderId = PublicKeyEd25519;

/// Functions for creating, updating and querying the contract state.
impl<S: HasStateApi> State<S> {
    fn new(
        state_builder: &mut StateBuilder<S>,
        issuer_account: AccountAddress,
        issuer_key: PublicKeyEd25519,
        issuer_metadata: MetadataUrl,
        credential_type: CredentialType,
        credential_schema: SchemaRef,
    ) -> Self {
        State {
            issuer_account,
            issuer_key,
            issuer_metadata,{% if revocable_by_others %}
            revocation_keys: state_builder.new_map(),
            all_revocation_keys: state_builder.new_set(),{% endif %}
            credentials: state_builder.new_map(),
            credential_type,
            credential_schema,
        }
    }

    fn view_credential_info(
        &self,
        credential_id: CredentialHolderId,
    ) -> ContractResult<CredentialQueryResponse> {
        let entry =
            self.credentials.get(&credential_id).ok_or(ContractError::CredentialNotFound)?;
        Ok(CredentialQueryResponse {
            credential_info:  entry.info(credential_id),
            revocation_nonce: entry.revocation_nonce,
            schema_ref:       self.credential_schema.clone(),
        })
    }

    fn view_credential_status(
        &self,
        now: Timestamp,
        credential_id: CredentialHolderId,
    ) -> ContractResult<CredentialStatus> {
        self.credentials
            .get(&credential_id)
            .map(|x| x.get_status(now))
            .ok_or(ContractError::CredentialNotFound)
    }

    fn register_credential(
        &mut self,
        credential_info: &CredentialInfo,
        state_builder: &mut StateBuilder<S>,
    ) -> ContractResult<()> {
        let credential_entry = CredentialEntry {
            holder_revocable: credential_info.holder_revocable,
            valid_from:       credential_info.valid_from,
            valid_until:      credential_info.valid_until,
            metadata_url:     state_builder.new_box(credential_info.metadata_url.clone()),
            revocation_nonce: 0,
            revoked:          false,
        };
        let res = self.credentials.insert(credential_info.holder_id, credential_entry);
        ensure!(res.is_none(), ContractError::CredentialAlreadyExists);
        Ok(())
    }

    fn update_credential_metadata(
        &mut self,
        credential_id: &CredentialHolderId,
        metadata: MetadataUrl,
    ) -> ContractResult<()> {
        if let Some(mut entry) = self.credentials.get_mut(credential_id) {
            *entry.metadata_url = metadata;
            Ok(())
        } else {
            Err(ContractError::CredentialNotFound)
        }
    }

    fn revoke_credential(
        &mut self,
        now: Timestamp,
        credential_id: CredentialHolderId,
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
{% if restorable %}
    fn restore_credential(
        &mut self,
        now: Timestamp,
        credential_id: CredentialHolderId,
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
    }{% endif %}
{% if revocable_by_others %}
    fn register_revocation_key(&mut self, pk: PublicKeyEd25519) -> ContractResult<()> {
        let res = self.all_revocation_keys.insert(pk);
        ensure!(res, ContractError::KeyAlreadyExists);
        let res = self.revocation_keys.insert(pk, 0);
        ensure!(res.is_none(), ContractError::KeyAlreadyExists);
        Ok(())
    }

    fn view_revocation_keys(&self) -> Vec<(PublicKeyEd25519, u64)> {
        self.revocation_keys.iter().map(|(pk, nonce)| (*pk, *nonce)).collect()
    }

    fn remove_revocation_key(&mut self, pk: PublicKeyEd25519) -> ContractResult<()> {
        if self.revocation_keys.get(&pk).is_none() {
            Err(ContractError::KeyDoesNotExist)
        } else {
            self.revocation_keys.remove(&pk);
            Ok(())
        }
    }{% endif %}
}

/// Data for events of registering and updating a credential.
/// Used by the tagged event `CredentialEvent`.
#[derive(Serialize, SchemaType)]
struct CredentialEventData {
    /// A public key of the credential's holder.
    holder_id:       PublicKeyEd25519,
    /// A reference to the credential JSON schema.
    schema_ref:      SchemaRef,
    /// Type of the credential.
    credential_type: CredentialType,
    /// The original credential's metadata.
    metadata_url:    MetadataUrl,
}

/// A type for specifying who is revoking a credential, when registering a
/// revocation event.
#[derive(Serialize, SchemaType)]
enum Revoker {
    Issuer,
    Holder,{% if revocable_by_others %}
    /// `Other` is used for the cases when the revoker is not the issuer or
    /// holder. In this contract it is a revocation authority, which is
    /// identified using a public key.
    Other(PublicKeyEd25519),{% endif %}
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
    /// A public key of the credential's holder.
    holder_id: CredentialHolderId,
    /// Who revokes the credential.
    revoker:   Revoker,
    /// An optional text clarifying the revocation reasons.
    /// The issuer can use this field to comment on the revocation, so the
    /// holder can observe it in the wallet.
    reason:    Option<Reason>,
}{% if restorable %}

/// An untagged restoration event.
/// For a tagged version use `CredentialEvent`.
#[derive(Serialize, SchemaType)]
struct RestoreCredentialEvent {
    /// A public key of the credential's holder.
    holder_id: CredentialHolderId,
    /// An optional text clarifying the restoring reasons.
    reason:    Option<Reason>,
}{% endif %}

/// An untagged credential metadata event. Emitted when updating the credential
/// metadata. For a tagged version use `CredentialEvent`.
#[derive(Serialize, SchemaType)]
struct CredentialMetadataEvent {
    credential_id: CredentialHolderId,
    metadata_url:  MetadataUrl,
}

/// The schema reference has been updated for the credential type.
#[derive(Serialize, SchemaType)]
struct CredentialSchemaRefEvent {
    credential_type: CredentialType,
    schema_ref:      SchemaRef,
}

#[derive(Serialize, SchemaType)]
enum RevocationKeyAction {
    Register,
    Remove,
}

/// An untagged revocation key event.
/// Emitted when keys are registered and removed.
/// For a tagged version use `CredentialEvent`.
#[derive(Serialize, SchemaType)]
struct RevocationKeyEvent {
    /// The public key that is registered/removed
    key:    PublicKeyEd25519,
    /// A register/remove action.
    action: RevocationKeyAction,
}

/// Tagged credential registry event.
/// This version should be used for logging the events.
enum CredentialEvent {
    /// Credential registration event. Logged when an entry in the registry is
    /// created for the first time.
    Register(CredentialEventData),
    /// Credential revocation event.
    Revoke(RevokeCredentialEvent),
    {% if restorable %}/// Credential restoration (reversing revocation) event.
    Restore(RestoreCredentialEvent),{% endif %}
    /// Issuer's metadata changes, including the contract deployment.
    IssuerMetadata(MetadataUrl),
    /// Credential's metadata changes.
    CredentialMetadata(CredentialMetadataEvent),
    /// Credential's schema changes.
    Schema(CredentialSchemaRefEvent),
    /// Revocation key changes
    RevocationKey(RevocationKeyEvent),
}

// Implementing a custom schemaType use tags required by CIS-4.
impl schema::SchemaType for CredentialEvent {
    fn get_type() -> schema::Type {
        schema::Type::TaggedEnum(collections::BTreeMap::from([
            (
                249,
                (
                    "Register".to_string(),
                    schema::Fields::Named(Vec::from([
                        ("holder_id".to_string(), PublicKeyEd25519::get_type()),
                        ("schema_ref".to_string(), SchemaRef::get_type()),
                        ("credential_type".to_string(), CredentialType::get_type()),
                        ("metadata_url".to_string(), MetadataUrl::get_type()),
                    ])),
                ),
            ),
            (
                248,
                (
                    "Revoke".to_string(),
                    schema::Fields::Named(Vec::from([
                        ("holder_id".to_string(), CredentialHolderId::get_type()),
                        ("revoker".to_string(), Revoker::get_type()),
                        ("reason".to_string(), Option::<Reason>::get_type()),
                    ])),
                ),
            ),
            (
                247,
                (
                    "IssuerMetadata".to_string(),
                    schema::Fields::Named(Vec::from([
                        ("url".to_string(), schema::Type::String(schema::SizeLength::U16)),
                        ("hash".to_string(), Option::<HashSha2256>::get_type()),
                    ])),
                ),
            ),
            (
                246,
                (
                    "CredentialMetadata".to_string(),
                    schema::Fields::Named(Vec::from([
                        ("credential_id".to_string(), CredentialHolderId::get_type()),
                        ("metadata_url".to_string(), MetadataUrl::get_type()),
                    ])),
                ),
            ),
            (
                245,
                (
                    "Schema".to_string(),
                    schema::Fields::Named(Vec::from([
                        ("credential_type".to_string(), CredentialType::get_type()),
                        ("schema_ref".to_string(), SchemaRef::get_type()),
                    ])),
                ),
            ),
            (
                244,
                (
                    "RevocationKey".to_string(),
                    schema::Fields::Named(Vec::from([
                        ("key".to_string(), PublicKeyEd25519::get_type()),
                        ("action".to_string(), RevocationKeyAction::get_type()),
                    ])),
                ),
            ),{% if restorable %}
            (
                0, // Restore event is not covered by CIS-4; it gets `0` tag.
                (
                    "Restore".to_string(),
                    schema::Fields::Named(Vec::from([
                        ("holder_id".to_string(), CredentialHolderId::get_type()),
                        ("reason".to_string(), Option::<Reason>::get_type()),
                    ])),
                ),
            ),{% endif %}
        ]))
    }
}

impl Serial for CredentialEvent {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        match self {
            // CIS-4 standard events are numbered from 249 counting down
            CredentialEvent::Register(data) => {
                249u8.serial(out)?;
                data.serial(out)
            }
            CredentialEvent::Revoke(data) => {
                248u8.serial(out)?;
                data.serial(out)
            }
            CredentialEvent::IssuerMetadata(data) => {
                247u8.serial(out)?;
                data.serial(out)
            }
            CredentialEvent::CredentialMetadata(data) => {
                246u8.serial(out)?;
                data.serial(out)
            }
            CredentialEvent::Schema(data) => {
                245u8.serial(out)?;
                data.serial(out)
            }
            CredentialEvent::RevocationKey(data) => {
                244u8.serial(out)?;
                data.serial(out)
            }{% if restorable %}
            // Restore event is not covered by CIS-4; it gets `0` tag.
            CredentialEvent::Restore(data) => {
                0u8.serial(out)?;
                data.serial(out)
            }{% endif %}
        }
    }
}

impl Deserial for CredentialEvent {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        match source.get()? {
            249u8 => Ok(Self::Register(source.get()?)),
            248u8 => Ok(Self::Revoke(source.get()?)),
            247u8 => Ok(Self::IssuerMetadata(source.get()?)),
            246u8 => Ok(Self::CredentialMetadata(source.get()?)),
            245u8 => Ok(Self::Schema(source.get()?)),
            244u8 => Ok(Self::RevocationKey(source.get()?)),
{% if restorable %}            0u8 => Ok(Self::Restore(source.get()?)),{% endif %}
            _ => Err(ParseError {}),
        }
    }
}

#[derive(Serialize, SchemaType)]
pub struct InitParams {
    /// The issuer's metadata.
    issuer_metadata: MetadataUrl,
    /// The type of credentials for this registry.
    credential_type: CredentialType,
    /// The credential schema for this registry.
    schema:          SchemaRef,
    /// The issuer for the registry. If `None`, the `init_origin` is used as
    /// `issuer`.
    issuer_account:  Option<AccountAddress>,
    /// The issuer's public key.
    issuer_key:      PublicKeyEd25519,{% if revocable_by_others %}
    /// Revocation keys available right after initialization.
    #[concordium(size_length = 1)]
    revocation_keys: Vec<PublicKeyEd25519>,{% endif %}
}

/// Init function that creates a fresh registry state given the required
/// initialisation data.
{% if revocable_by_others %}///
/// Logs `CredentialEvent::IssuerMetadata`, `CredentialEvent::RevocationKey`
/// (with the `Register` action) for each key in the input, and
/// `CredentialEvent::Schema` for each schema in the input.
///
/// It rejects if:
///   - Fails to parse the input parameter.
///   - Fails to log the events.
///   - Fails to register any of the initial revocation keys.{% else %}
/// Logs `CredentialEvent::IssuerMetadata`, and `CredentialEvent::Schema`
/// for each schema in the input.
///
/// It rejects if:
///   - Fails to parse the input parameter.
///   - Fails to log the events.{% endif %}
#[init(
    contract = "credential_registry",
    parameter = "InitParams",
    event = "CredentialEvent",
    enable_logger
)]
fn init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
    logger: &mut impl HasLogger,
) -> InitResult<State<S>> {
    let parameter: InitParams = ctx.parameter_cursor().get()?;
    logger.log(&CredentialEvent::IssuerMetadata(parameter.issuer_metadata.clone()))?;
{% if revocable_by_others %}
    let mut state = State::new(
        state_builder,
        parameter.issuer_account.unwrap_or_else(|| ctx.init_origin()),
        parameter.issuer_key,
        parameter.issuer_metadata,
        parameter.credential_type.clone(),
        parameter.schema.clone(),
    );

    for pk in parameter.revocation_keys {
        state.register_revocation_key(pk)?;
        logger.log(&CredentialEvent::RevocationKey(RevocationKeyEvent {
            key:    pk,
            action: RevocationKeyAction::Register,
        }))?;
    }{% else %}
    let state = State::new(
        state_builder,
        parameter.issuer_account.unwrap_or_else(|| ctx.init_origin()),
        parameter.issuer_key,
        parameter.issuer_metadata,
        parameter.credential_type.clone(),
        parameter.schema.clone(),
    );
{% endif %}

    logger.log(&CredentialEvent::Schema(CredentialSchemaRefEvent {
        credential_type: parameter.credential_type,
        schema_ref:      parameter.schema,
    }))?;
    Ok(state)
}

/// Check whether the transaction `sender` is the issuer.
fn sender_is_issuer<S: HasStateApi>(ctx: &impl HasReceiveContext, state: &State<S>) -> bool {
    ctx.sender().matches_account(&state.issuer_account)
}

#[derive(Serialize, SchemaType, PartialEq, Eq, Clone, Debug)]
pub struct CredentialInfo {
    /// The holder's identifier is a public key.
    holder_id:        CredentialHolderId,
    /// If this flag is set to `true` the holder can send a signed message to
    /// revoke their credential.
    holder_revocable: bool,
    /// The date from which the credential is considered valid.
    valid_from:       Timestamp,
    /// After this date, the credential becomes expired. `None` corresponds to a
    /// credential that cannot expire.
    valid_until:      Option<Timestamp>,
    /// Link to the metadata of this credential.
    metadata_url:     MetadataUrl,
}

/// Parameters for registering a credential
#[derive(Serialize, SchemaType, Clone, Debug)]
pub struct RegisterCredentialParam {
    /// Public credential data.
    credential_info: CredentialInfo,
    /// Any additional data required by the issuer in the registration process.
    /// This data is not used in this contract. However, it is part of the CIS-4
    /// standard that this contract implements; `auxiliary_data` can be
    /// used, for example, to implement signature-based authentication.
    #[concordium(size_length = 2)]
    auxiliary_data:  Vec<u8>,
}

/// Response to a credential data query.
#[derive(Serialize, SchemaType, Clone, Debug)]
pub struct CredentialQueryResponse {
    credential_info:  CredentialInfo,
    /// A schema URL pointing to the JSON schema for a verifiable
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
    parameter = "CredentialHolderId",
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
    parameter = "CredentialHolderId",
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

/// Register a new credential with the given id and data.
/// Logs RegisterCredentialEvent.
///
/// Can be called only by the issuer.
///
/// Logs `CredentialEvent::Register`.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The caller is not the issuer.
/// - An entry with the given credential id already exists.
/// - Fails to log the event.
#[receive(
    contract = "credential_registry",
    name = "registerCredential",
    parameter = "RegisterCredentialParam",
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
    let parameter: RegisterCredentialParam = ctx.parameter_cursor().get()?;
    let credential_info = parameter.credential_info;
    let (state, state_builder) = host.state_and_builder();
    state.register_credential(&credential_info, state_builder)?;
    logger.log(&CredentialEvent::Register(CredentialEventData {
        holder_id:       credential_info.holder_id,
        schema_ref:      state.credential_schema.clone(),
        credential_type: state.credential_type.clone(),
        metadata_url:    credential_info.metadata_url,
    }))?;
    Ok(())
}

/// Metadata of the signature.
#[derive(Serialize, SchemaType, Clone)]
struct SigningData {
    /// The contract_address that the signature is intended for.
    contract_address: ContractAddress,
    /// The entry_point that the signature is intended for.
    entry_point:      OwnedEntrypointName,
    /// A nonce to prevent replay attacks.
    nonce:            u64,
    /// A timestamp to make signatures expire.
    timestamp:        Timestamp,
}

/// A message prefix for revocation requests by holders and revocation
/// authorities.
const SIGNARUTE_DOMAIN: &str = "WEB3ID:REVOKE";

/// A parameter type for revoking a credential by the holder.
#[derive(Serialize, SchemaType)]
pub struct RevokeCredentialHolderParam {
    signature: SignatureEd25519,
    data:      RevocationDataHolder,
}

/// Prepare the message bytes for the holder
impl RevokeCredentialHolderParam {
    fn message_bytes(&self, bytes: &mut Vec<u8>) -> ContractResult<()> {
        self.data.serial(bytes).map_err(|_| ContractError::SerializationError)
    }
}

/// The parameter type for the contract function
/// `serializationHelperHolderRevoke`.
#[derive(Serialize, SchemaType)]
pub struct RevocationDataHolder {
    /// Id of the credential to revoke.
    credential_id: CredentialHolderId,
    /// Info about the signature.
    signing_data:  SigningData,
    /// (Optional) reason for revoking the credential.
    reason:        Option<Reason>,
}

/// Helper function that can be invoked at the front end to serialize
/// the `RevocationDataholder` to be signed by the wallet. The
/// `RevocationDataHolder` includes all the input parameters from
/// `RevokeCredentialHolderParam` except for the `signature`. We only need
/// the input parameter schema of this function at the front end. The
/// `serializationHelperHolderRevoke` function is not executed at any point in
/// time, therefore the logic of the function is irrelevant.
#[receive(
    contract = "credential_registry",
    name = "serializationHelperHolderRevoke",
    parameter = "RevocationDataHolder"
)]
fn contract_serialization_helper_holder_revoke<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    _host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    Ok(())
}

/// A parameter type for revoking a credential by the issuer.
#[derive(Serialize, SchemaType)]
pub struct RevokeCredentialIssuerParam {
    /// Id of the credential to revoke.
    credential_id:  CredentialHolderId,
    /// (Optional) reason for revoking the credential.
    reason:         Option<Reason>,
    /// Any additional data required by the issuer in the registration process.
    /// This data is not used in this contract. However, it is part of the CIS-4
    /// standard that this contract implements; `auxiliary_data` can be
    /// used, for example, to implement signature-based authentication.
    #[concordium(size_length = 2)]
    auxiliary_data: Vec<u8>,
}

/// A parameter type for revoking a credential by a revocation authority.
#[derive(Serialize, SchemaType)]
pub struct RevokeCredentialOtherParam {
    signature: SignatureEd25519,
    data:      RevocationDataOther,
}
{% if revocable_by_others %}
impl RevokeCredentialOtherParam {
    /// Prepare the message bytes for a revocation authority
    fn message_bytes(&self, bytes: &mut Vec<u8>) -> ContractResult<()> {
        self.data.serial(bytes).map_err(|_| ContractError::SerializationError)
    }
}
{% endif %}
#[derive(Serialize, SchemaType)]
pub struct RevocationDataOther {
    /// Id of the credential to revoke.
    credential_id:  CredentialHolderId,
    /// Info about the signature.
    signing_data:   SigningData,
    /// The key with which the revocation payload is signed.
    revocation_key: PublicKeyEd25519,
    /// (Optional) reason for revoking the credential.
    reason:         Option<Reason>,
}

/// Helper function that can be invoked at the front end to serialize
/// the `RevocationDataOther` to be signed by the wallet. The
/// `RevocationDataOther` includes all the input parameters from
/// `RevokeCredentialOtherParam` except for the `signature`. We only need
/// the input parameter schema of this function at the front end. The
/// `serializationHelperOtherRevoke` function is not executed at any point in
/// time, therefore the logic of the function is irrelevant.
#[receive(
    contract = "credential_registry",
    name = "serializationHelperOtherRevoke",
    parameter = "RevocationDataOther"
)]
fn contract_serialization_helper_hother_revoke<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    _host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    Ok(())
}

/// Performs authorization based on the signature and the public key.
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

    // Check that the signature was intended for entrypoint.
    ensure_eq!(signing_data.entry_point, ctx.named_entrypoint(), ContractError::WrongEntrypoint);

    // Check signature is not expired.
    ensure!(signing_data.timestamp > ctx.metadata().slot_time(), ContractError::ExpiredSignature);

    // Check the signature.
    ensure!(
        crypto_primitives.verify_ed25519_signature(public_key, signature, message),
        ContractError::WrongSignature
    );
    Ok(())
}

/// Revoke a credential as a holder.
///
/// The holder is authenticated by verifying the signature on the input to the
/// entrypoint with the holder's public key. The public key is used as the
/// credential identifier.
///
/// Note that nonce is used as a general way to prevent replay attacks. The
/// issuer can choose to implement a function that restores the revoked
/// credential.
///
/// Logs `CredentialEvent::Revoke` with `Holder` as the revoker.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - An entry with the given credential id does not exist.
/// - A redential is not holder-revocable.
/// - Signature validation has failed, meaning that some of the following has
///   happened: nonce is incorrect, the signed message was not intended for this
///   contract/entrypoint, the signature has expired or the signature
///   verification has failed.
/// - The credential status is not one of `Active` or `NotActivated`.
/// - Fails to log the event.
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
        .entry(parameter.data.credential_id)
        .occupied_or(ContractError::CredentialNotFound)?;

    let revoker = Revoker::Holder;

    let signature = parameter.signature;

    // Only holder-revocable entries can be revoked by the holder.
    ensure!(registry_entry.holder_revocable, ContractError::NotAuthorized);

    // Get the public key and the current nonce.
    let public_key = parameter.data.credential_id;
    let nonce = registry_entry.revocation_nonce;

    // Update the nonce.
    registry_entry.revocation_nonce += 1;

    // Perepare message bytes as it is signed by the wallet
    // Note that the message is prepended by a domain separation string
    let mut message: Vec<u8> = SIGNARUTE_DOMAIN.as_bytes().to_vec();
    parameter.message_bytes(&mut message)?;
    authorize_with_signature(
        crypto_primitives,
        ctx,
        nonce,
        public_key,
        parameter.data.signing_data,
        &message,
        signature,
    )?;
    let credential_id = parameter.data.credential_id;
    let now = ctx.metadata().slot_time();
    drop(registry_entry);

    state.revoke_credential(now, credential_id)?;

    logger.log(&CredentialEvent::Revoke(RevokeCredentialEvent {
        holder_id: public_key,
        reason: parameter.data.reason,
        revoker,
    }))?;
    Ok(())
}

/// Revoke a credential as an issuer.
///
/// Can be called only by the issuer.
///
/// Logs `CredentialEvent::Revoke` with `Issuer` as the revoker.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The caller is not the issuer.
/// - An entry with the given credential id does not exist.
/// - The credential status is not one of `Active` or `NotActivated`.
/// - Fails to log the event.
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
    let holder_id = parameter.credential_id;
    drop(registry_entry);

    let credential_id = parameter.credential_id;

    state.revoke_credential(now, credential_id)?;

    logger.log(&CredentialEvent::Revoke(RevokeCredentialEvent {
        holder_id,
        reason: parameter.reason,
        revoker,
    }))?;
    Ok(())
}
{% if revocable_by_others %}
/// Revoke a credential as a revocation authority.
///
/// A revocation authority is any entity that holds a private key corresponding
/// to a public key registered by the issuer.
///
/// A revocation authority is authenticated by verifying the signature on the
/// input to the entrypoint with the authority's public key.
/// The public key is stored in `revocation_keys`.
///
/// Note that a nonce is used as a general way to prevent replay attacks. The
/// issuer can choose to implement a function that restores the revoked
/// credential.
///
///  Logs `CredentialEvent::Revoke` with `Other` as the revoker.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - An entry with the given credential id does not exist
/// - The revocation key could not be found.
/// - Signature validation has failed, meaning that some of the following has
///   happened: nonce is incorrect, the signed message was not intended for this
///   contract/entrypoint, the signature has expired or the signature
///   verification has failed.
/// - The credential status is not one of `Active` or `NotActivated`
/// - Fails to log the event.
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
        .entry(parameter.data.credential_id)
        .occupied_or(ContractError::CredentialNotFound)?;
    let holder_id = parameter.data.credential_id;
    drop(registry_entry);

    let public_key = parameter.data.revocation_key;
    let mut entry =
        state.revocation_keys.entry(public_key).occupied_or(ContractError::KeyDoesNotExist)?;

    // Get the current nonce value
    let nonce = *entry;

    // Update the nonce in the state.
    *entry += 1;

    // Set the revoker to be the revocation authority.
    let revoker = Revoker::Other(public_key);

    let signature = parameter.signature;

    // Prepare message bytes as it is signed by the wallet
    // Note that the message is prepended by a domain separation string
    let mut message: Vec<u8> = SIGNARUTE_DOMAIN.as_bytes().to_vec();
    parameter.message_bytes(&mut message)?;

    authorize_with_signature(
        crypto_primitives,
        ctx,
        nonce,
        public_key,
        parameter.data.signing_data,
        &message,
        signature,
    )?;
    let now = ctx.metadata().slot_time();
    drop(entry);

    let credential_id = parameter.data.credential_id;

    state.revoke_credential(now, credential_id)?;
    logger.log(&CredentialEvent::Revoke(RevokeCredentialEvent {
        holder_id,
        reason: parameter.data.reason,
        revoker,
    }))?;
    Ok(())
}
{% else %}
/// Revoke a credential as a revocation authority.
/// 
/// This contract does not support revoking credentials by anyone other than
/// the issuer or the holder. The CIS-4 standard requires to have such an
/// entrypoint. Therefore, it is present, but always returns an error.
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
    _ctx: &impl HasReceiveContext,
    _host: &mut impl HasHost<State<S>, StateApiType = S>,
    _logger: &mut impl HasLogger,
    _crypto_primitives: &impl HasCryptoPrimitives,
) -> Result<(), ContractError> {
    Err(ContractError::NotSupported)
}
{% endif %}
#[derive(Serialize, SchemaType)]
pub struct RegisterPublicKeyParameters {
    #[concordium(size_length = 2)]
    pub keys:       Vec<PublicKeyEd25519>,
    /// Any additional data required for registering keys.
    /// This data is not used in this contract. However, it is part of the CIS-4
    /// standard that this contract implements; `auxiliary_data` can be
    /// used, for example, to implement signature-based authentication.
    #[concordium(size_length = 2)]
    auxiliary_data: Vec<u8>,
}

#[derive(Serialize, SchemaType)]
pub struct RemovePublicKeyParameters {
    #[concordium(size_length = 2)]
    pub keys:       Vec<PublicKeyEd25519>,
    /// Any additional data required for removing keys.
    /// This data is not used in this contract. However, it is part of the CIS-4
    /// standard that this contract implements; `auxiliary_data` can be
    /// used, for example, to implement signature-based authentication.
    #[concordium(size_length = 2)]
    auxiliary_data: Vec<u8>,
}
{% if revocable_by_others %}
/// Register revocation authorities public keys.
///
/// These keys are used to authorize the revocation (applies to the whole
/// registry). The contract keeps track of all keys ever seen by this contract.
/// Some keys can be removed from the available keys, but registering them again
/// is not possible. This prevents resetting the key's nonce.
///
/// Only the issuer can call the entrypoint.
///
/// Logs `CredentialEvent::RevocationKey` with the `Register` action.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Some of the keys were previously used with this contract.
/// - The caller is not the issuer.
/// - Fails to log the event for any key in the input.
#[receive(
    contract = "credential_registry",
    name = "registerRevocationKeys",
    parameter = "RegisterPublicKeyParameters",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_register_revocation_keys<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    ensure!(sender_is_issuer(ctx, host.state()), ContractError::NotAuthorized);
    let RegisterPublicKeyParameters {
        keys,
        ..
    } = ctx.parameter_cursor().get()?;
    for key in keys {
        host.state_mut().register_revocation_key(key)?;
        logger.log(&CredentialEvent::RevocationKey(RevocationKeyEvent {
            key,
            action: RevocationKeyAction::Register,
        }))?;
    }
    Ok(())
}{% else %}
/// Register revocation authorities public keys.
/// 
/// This contract does not support revoking credentials by anyone other than
/// the issuer or the holder. The CIS-4 standard requires to have such an
/// entrypoint. Therefore, it is present, but always returns an error.
#[receive(
    contract = "credential_registry",
    name = "registerRevocationKeys",
    parameter = "RegisterPublicKeyParameters",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_register_revocation_keys<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    _host: &mut impl HasHost<State<S>, StateApiType = S>,
    _logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    Err(ContractError::NotSupported)
}
{% endif %}
{% if revocable_by_others %}
/// Remove revocation authorities public keys.
///
/// Note that it is not possible to register the same key after removing it.
/// This prevents resetting the key's nonce.
///
/// Only the issuer can call the entrypoint.
///
/// Logs `CredentialEvent::RevocationKey` with the `Remove` action.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Some of the keys do not exist.
/// - The caller is not the issuer.
/// - Fails to log the event for any key in the input.
#[receive(
    contract = "credential_registry",
    name = "removeRevocationKeys",
    parameter = "RemovePublicKeyParameters",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_remove_revocation_keys<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    ensure!(sender_is_issuer(ctx, host.state()), ContractError::NotAuthorized);
    let RemovePublicKeyParameters {
        keys,
        ..
    } = ctx.parameter_cursor().get()?;
    for key in keys {
        host.state_mut().remove_revocation_key(key)?;
        logger.log(&CredentialEvent::RevocationKey(RevocationKeyEvent {
            key,
            action: RevocationKeyAction::Remove,
        }))?;
    }
    Ok(())
}
{% else %}
/// Remove revocation authorities public keys.
/// 
/// This contract does not support revoking credentials by anyone other than
/// the issuer or the holder. The CIS-4 standard requires to have such an
/// entrypoint. Therefore, it is present, but always returns an error.
#[receive(
    contract = "credential_registry",
    name = "removeRevocationKeys",
    parameter = "RemovePublicKeyParameters",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_remove_revocation_keys<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    _host: &mut impl HasHost<State<S>, StateApiType = S>,
    _logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    Err(ContractError::NotSupported)
}
{% endif %}{% if revocable_by_others %}
/// A view entrypoint returning currently available revocation keys.
/// Returns a public key and the nonce.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "credential_registry",
    name = "revocationKeys",
    error = "ContractError",
    return_value = "Vec<(PublicKeyEd25519, u64)>"
)]
fn contract_revocation_keys<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<Vec<(PublicKeyEd25519, u64)>, ContractError> {
    Ok(host.state().view_revocation_keys())
}
{% else %}
/// A view entrypoint returning currently available revocation keys.
/// 
/// This contract does not support revoking credentials by anyone other than
/// the issuer or the holder. The CIS-4 standard requires to have such an
/// entrypoint. Therefore, it is present, but always returns an error.
#[receive(
    contract = "credential_registry",
    name = "revocationKeys",
    error = "ContractError",
    return_value = "Vec<(PublicKeyEd25519, u64)>"
)]
fn contract_revocation_keys<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    _host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<Vec<(PublicKeyEd25519, u64)>, ContractError> {
    Err(ContractError::NotSupported)
}
{% endif %}
/// A response type for the registry metadata request.
#[derive(Serialize, SchemaType)]
struct MetadataResponse {
    /// A reference to the issuer's metadata.
    issuer_metadata:   MetadataUrl,
    /// The type of credentials used.
    credential_type:   CredentialType,
    /// A reference to the JSON schema corresponding to this type.
    credential_schema: SchemaRef,
}

/// A view entrypoint to get the registry metadata.
#[receive(
    contract = "credential_registry",
    name = "registryMetadata",
    error = "ContractError",
    return_value = "MetadataResponse"
)]
fn contract_registry_metadata<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<MetadataResponse, ContractError> {
    let state = host.state();
    Ok(MetadataResponse {
        issuer_metadata:   state.issuer_metadata.clone(),
        credential_type:   state.credential_type.clone(),
        credential_schema: state.credential_schema.clone(),
    })
}

/// Update issuer's metadata.
///
/// Can be called only by the issuer.
///
/// Logs `CredentialEvent::IssuerMetadata`.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The caller is not the issuer.
/// - It fails to log the event.
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
    let data: MetadataUrl = ctx.parameter_cursor().get()?;
    host.state_mut().issuer_metadata = data.clone();
    logger.log(&CredentialEvent::IssuerMetadata(data))?;
    Ok(())
}

/// A view entrypoint for querying the issuer's public key.
#[receive(
    contract = "credential_registry",
    name = "issuer",
    error = "ContractError",
    return_value = "PublicKeyEd25519"
)]
fn contract_issuer<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<PublicKeyEd25519, ContractError> {
    Ok(host.state().issuer_key)
}

/// Update the credential schema reference.
/// Note that updating the schema should not break credentials based on it.
/// An intended use case is to update a reference if the URL to the
/// JSON document has changed, but the JSON document itself remains the same.
///
/// Logs `CredentialEvent::Schema`.
///
/// Can be called only by the issuer.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The caller is not the issuer.
#[receive(
    contract = "credential_registry",
    name = "updateCredentialSchema",
    parameter = "SchemaRef",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_update_credential_schema<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    ensure!(sender_is_issuer(ctx, host.state()), ContractError::NotAuthorized);
    let schema_ref: SchemaRef = ctx.parameter_cursor().get()?;
    let state = host.state_mut();
    state.credential_schema = schema_ref.clone();
    logger.log(&CredentialEvent::Schema(CredentialSchemaRefEvent {
        credential_type: state.credential_type.clone(),
        schema_ref,
    }))?;
    Ok(())
}

#[derive(Serialize, SchemaType)]
struct CredentialMetadataParam {
    /// The id of the credential to update.
    credential_id: CredentialHolderId,
    /// The new metadata URL.
    metadata_url:  MetadataUrl,
}

/// Update existing credential metadata URL.
///
/// Can be called only by the issuer.
///
/// Logs `redentialEvent::CredentialMetadata`.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The caller is not the issuer.
/// - Some of the credentials are not present.
/// - Fails to log the event for any of the input credentials.
#[receive(
    contract = "credential_registry",
    name = "updateCredentialMetadata",
    parameter = "Vec<CredentialMetadataParam>",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_update_credential_metadata<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    ensure!(sender_is_issuer(ctx, host.state()), ContractError::NotAuthorized);
    let data: Vec<CredentialMetadataParam> = ctx.parameter_cursor().get()?;
    for CredentialMetadataParam {
        credential_id,
        metadata_url,
    } in data
    {
        host.state_mut().update_credential_metadata(&credential_id, metadata_url.clone())?;
        logger.log(&CredentialEvent::CredentialMetadata(CredentialMetadataEvent {
            credential_id,
            metadata_url,
        }))?;
    }
    Ok(())
}
{% if restorable %}
/// A parameter type for restoring a credential by the issuer.
#[derive(Serialize, SchemaType)]
pub struct RestoreCredentialIssuerParam {
    /// Id of the credential to restore.
    credential_id: CredentialHolderId,
    /// (Optional) reason for restoring the credential.
    reason:        Option<Reason>,
}

/// Restore credential by the issuer.
/// Restoring means reverting revocation.
///
/// Can be called only by the issuer.
///
/// Logs `CredentialEvent::Restore`.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The caller is not the issuer.
/// - Credential does not exist.
/// - Credential status is different from `Revoked`.
/// - Fails to log the event.
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
    let holder_id = parameter.credential_id;
    drop(registry_entry);

    let credential_id = parameter.credential_id;

    host.state_mut().restore_credential(now, credential_id)?;
    logger.log(&CredentialEvent::Restore(RestoreCredentialEvent {
        holder_id,
        reason: parameter.reason,
    }))?;
    Ok(())
}
{% endif %}
/// The parameter type for the contract function `upgrade`.
/// Takes the new module and optionally an entrypoint to call in the new module
/// after triggering the upgrade. The upgrade is reverted if the entrypoint
/// fails. This is useful for doing migration in the same transaction triggering
/// the upgrade.
#[derive(Debug, Serialize, SchemaType)]
struct UpgradeParams {
    /// The new module reference.
    module:  ModuleReference,
    /// Optional entrypoint to call in the new module after upgrade.
    migrate: Option<(OwnedEntrypointName, OwnedParameter)>,
}

/// Mapping errors related to contract invocations to ContractError.
impl<T> From<CallContractError<T>> for ContractError {
    fn from(_cce: CallContractError<T>) -> Self { Self::ContractInvocationError }
}

/// Mapping errors related to contract upgrades to ContractError.
impl From<UpgradeError> for ContractError {
    #[inline(always)]
    fn from(ue: UpgradeError) -> Self {
        match ue {
            UpgradeError::MissingModule => Self::FailedUpgradeMissingModule,
            UpgradeError::MissingContract => Self::FailedUpgradeMissingContract,
            UpgradeError::UnsupportedModuleVersion => Self::FailedUpgradeUnsupportedModuleVersion,
        }
    }
}

/// Upgrade this smart contract instance to a new module and call optionally a
/// migration function after the upgrade.
///
/// It rejects if:
/// - Sender is not the issuer.
/// - It fails to parse the parameter.
/// - If the upgrade fails.
/// - If the migration invoke fails.
///
/// This function is marked as `low_level`. This is **necessary** since the
/// high-level mutable functions store the state of the contract at the end of
/// execution. This conflicts with migration since the shape of the state
/// **might** be changed by the migration function. If the state is then written
/// by this function it would overwrite the state stored by the migration
/// function.
#[receive(
    contract = "credential_registry",
    name = "upgrade",
    parameter = "UpgradeParams",
    error = "ContractError",
    low_level
)]
fn contract_upgrade<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<S>,
) -> ContractResult<()> {
    // Read the top-level contract state.
    let state: State<S> = host.state().read_root()?;

    // Check that only the issuer is authorized to upgrade the smart contract.
    ensure!(sender_is_issuer(ctx, &state), ContractError::NotAuthorized);
    // Parse the parameter.
    let params: UpgradeParams = ctx.parameter_cursor().get()?;
    // Trigger the upgrade.
    host.upgrade(params.module)?;
    // Call the migration function if provided.
    if let Some((func, parameters)) = params.migrate {
        host.invoke_contract_raw(
            &ctx.self_address(),
            parameters.as_parameter(),
            func.as_entrypoint_name(),
            Amount::zero(),
        )?;
    }
    Ok(())
}

#[concordium_cfg_test]
mod tests {

    use super::*;
    use quickcheck::*;
    use test_infrastructure::*;

    // Define `Arbitrary` instances for data types used in the contract.
    // The instances are used for randomized by property-based testing.

    // It is convenient to use arbitrary data even for simple properties, because it
    // allows us to avoid defining input data manually.

    impl Arbitrary for CredentialType {
        fn arbitrary(g: &mut Gen) -> Self {
            CredentialType {
                credential_type: Arbitrary::arbitrary(g),
            }
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            Box::new(self.credential_type.shrink().map(|s| CredentialType {
                credential_type: s,
            }))
        }
    }

    impl Arbitrary for SchemaRef {
        fn arbitrary(g: &mut Gen) -> Self {
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

    impl Arbitrary for CredentialInfo {
        fn arbitrary(g: &mut Gen) -> Self {
            CredentialInfo {
                holder_id:        PublicKeyEd25519([0u8; 32].map(|_| Arbitrary::arbitrary(g))),
                holder_revocable: Arbitrary::arbitrary(g),
                valid_from:       Arbitrary::arbitrary(g),
                valid_until:      Arbitrary::arbitrary(g),
                metadata_url:     MetadataUrl {
                    url:  Arbitrary::arbitrary(g),
                    hash: if Arbitrary::arbitrary(g) {
                        Some([0u8; 32].map(|_| Arbitrary::arbitrary(g)))
                    } else {
                        None
                    },
                },
            }
        }
    }

    const ISSUER_ACCOUNT: AccountAddress = AccountAddress([0u8; 32]);
    const ISSUER_METADATA_URL: &str = "https://example-university.com/university.json";
    const CREDANIAL_METADATA_URL: &str =
        "https://example-university.com/diplomas/university-vc-metadata.json";
    const CREDENTIAL_TYPE: &str = "UniversityDegreeCredential";
    const CREDENTIAL_SCHEMA_URL: &str =
        "https://credentials-schemas.com/JsonSchema2023-education-certificate.json";
    const ACCOUNT_0: AccountAddress = AccountAddress([0u8; 32]);
    const ADDRESS_0: Address = Address::Account(ACCOUNT_0);
    // Seed: 2FEE333FAD122A45AAB7BEB3228FA7858C48B551EA8EBC49D2D56E2BA22049FF
    const PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([
        172, 5, 96, 236, 139, 208, 146, 88, 124, 42, 62, 124, 86, 108, 35, 242, 32, 11, 7, 48, 193,
        61, 177, 220, 104, 169, 145, 4, 8, 1, 236, 112,
    ]);
    const SIGNATURE: SignatureEd25519 = SignatureEd25519([
        254, 138, 58, 131, 209, 45, 191, 52, 98, 228, 26, 234, 155, 245, 244, 226, 0, 153, 104,
        111, 201, 136, 243, 167, 251, 116, 110, 206, 172, 223, 41, 180, 90, 22, 63, 43, 157, 129,
        226, 75, 49, 33, 155, 76, 160, 133, 127, 146, 150, 80, 199, 201, 80, 98, 179, 43, 46, 46,
        211, 222, 185, 216, 12, 4,
    ]);

    /// A helper that returns a credential that is not revoked, cannot expire
    /// and is immediately activated. It is also possible to revoke it by the
    /// holder.
    fn credential_entry<S: HasStateApi>(state_builder: &mut StateBuilder<S>) -> CredentialEntry<S> {
        CredentialEntry {
            metadata_url:     state_builder.new_box(MetadataUrl {
                url:  CREDANIAL_METADATA_URL.into(),
                hash: None,
            }),
            valid_from:       Timestamp::from_timestamp_millis(0),
            valid_until:      None,
            holder_revocable: true,
            revocation_nonce: 0,
            revoked:          false,
        }
    }

    fn issuer_metadata() -> MetadataUrl {
        MetadataUrl {
            url:  ISSUER_METADATA_URL.to_string(),
            hash: None,
        }
    }

    fn get_credential_schema() -> (CredentialType, SchemaRef) {
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

    #[concordium_test]
    /// Test that initializing the contract succeeds with some state.
    fn test_init() {
        let mut ctx = TestInitContext::empty();
        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();

        ctx.set_init_origin(ISSUER_ACCOUNT);

        let schema = get_credential_schema();

        let parameter_bytes = to_bytes(&InitParams {
            issuer_metadata: issuer_metadata(),
            issuer_account:  ISSUER_ACCOUNT.into(),
            issuer_key:      PUBLIC_KEY,{% if revocable_by_others %}
            revocation_keys: vec![PUBLIC_KEY],{% endif %}
            credential_type: schema.0.clone(),
            schema:          schema.1.clone(),
        });
        ctx.set_parameter(&parameter_bytes);

        let state_result = init(&ctx, &mut state_builder, &mut logger);
        let state = state_result.expect_report("Contract initialization results in an error");

        // Check that the initial parameters are in the state.
        claim_eq!(state.credential_schema, schema.1, "Incorrect schema in the state");
        claim_eq!(state.issuer_account, ISSUER_ACCOUNT, "Incorrect issuer in the state");
        claim_eq!(
            state.issuer_metadata,
            issuer_metadata(),
            "Incorrect issuer metadata in the state"
        );

        // Check that the correct events were logged.
{% if revocable_by_others %}
        claim_eq!(logger.logs.len(), 3, "Incorrect number of logged events");
{% else %}
        claim_eq!(logger.logs.len(), 2, "Incorrect number of logged events");
{% endif %}
        claim_eq!(
            logger.logs[0],
            to_bytes(&CredentialEvent::IssuerMetadata(issuer_metadata())),
            "Incorrect issuer metadata event logged"
        );
{% if revocable_by_others %}
        claim_eq!(
            logger.logs[1],
            to_bytes(&CredentialEvent::RevocationKey(RevocationKeyEvent {
                key:    PUBLIC_KEY,
                action: RevocationKeyAction::Register,
            })),
            "Incorrect revocation key event logged"
        );
{% endif %}
        claim_eq!(
            {% if revocable_by_others %}logger.logs[2],{% else %}logger.logs[1],{% endif %}
            to_bytes(&CredentialEvent::Schema(CredentialSchemaRefEvent {
                credential_type: schema.0,
                schema_ref:      schema.1,
            })),
            "Incorrect schema event logged"
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
        entry.valid_from = Timestamp::from_timestamp_millis(20);
        let expected = CredentialStatus::NotActivated;
        let status = entry.get_status(now);
        claim_eq!(status, expected, "Expected status {:?}, got {:?}", expected, status);
    }

    /// Property: once the `revoked` flag is set to `true`, the status is
    /// always `Revoked` regardless of the valid_from and valid_until values
    #[concordium_quickcheck(num_tests = 500)]
    fn prop_revoked_stays_revoked(data: CredentialInfo, nonce: u64, now: Timestamp) -> bool {
        let mut state_builder = TestStateBuilder::new();
        let entry = CredentialEntry {
            metadata_url:     state_builder.new_box(data.metadata_url),
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
    #[concordium_quickcheck(num_tests = 500)]
    fn prop_register_credential(
        credential_type: CredentialType,
        schema_ref: SchemaRef,
        data: CredentialInfo,
        now: Timestamp,
    ) -> bool {
        let credential_id = data.holder_id;
        let mut state_builder = TestStateBuilder::new();
        let mut state = State::new(
            &mut state_builder,
            ISSUER_ACCOUNT,
            PUBLIC_KEY,
            issuer_metadata(),
            credential_type,
            schema_ref.clone(),
        );
        let register_result = state.register_credential(&data, &mut state_builder);
        let query_result = state.view_credential_info(credential_id);
        let status = state.view_credential_status(now, credential_id);
        if let Ok(fetched_data) = query_result {
            register_result.is_ok()
                && status.map_or(false, |x| x != CredentialStatus::Revoked)
                && fetched_data.credential_info == data
                && fetched_data.schema_ref == schema_ref
                && fetched_data.revocation_nonce == 0
        } else {
            false
        }
    }

    /// Property: if a credential is revoked successfully, the status changes to
    /// `Revoked`. The test is designed in such a way that the revocation is
    /// expeced to succeed.
    #[concordium_quickcheck(num_tests = 500)]
    fn prop_revocation(
        credential_type: CredentialType,
        schema_ref: SchemaRef,
        data: CredentialInfo,
    ) -> bool {
        let credential_id = data.holder_id;
        let mut state_builder = TestStateBuilder::new();
        let mut state = State::new(
            &mut state_builder,
            ISSUER_ACCOUNT,
            PUBLIC_KEY,
            issuer_metadata(),
            credential_type,
            schema_ref,
        );

        let register_result = state.register_credential(&data, &mut state_builder);

        // Make sure that the credential has not expired yet
        let now = Timestamp::from_timestamp_millis(0);
        let revocation_result = state.revoke_credential(now, credential_id);
        let status_result = state.view_credential_status(now, credential_id);
        register_result.is_ok()
            && revocation_result.is_ok()
            && status_result == Ok(CredentialStatus::Revoked)
    }{% if restorable %}

    /// Property: revoking and then restoring a credential gives the same status
    /// as before revocation. In this case, restoring always succeeds.
    #[concordium_quickcheck(num_tests = 500)]
    fn prop_revoke_restore(
        credential_type: CredentialType,
        schema_ref: SchemaRef,
        data: CredentialInfo,
    ) -> bool {
        let credential_id = data.holder_id;
        let mut state_builder = TestStateBuilder::new();
        let mut state = State::new(
            &mut state_builder,
            ISSUER_ACCOUNT,
            PUBLIC_KEY,
            issuer_metadata(),
            credential_type,
            schema_ref,
        );

        let register_result = state.register_credential(&data, &mut state_builder);

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
        register_result.is_ok()
            && revocation_result.is_ok()
            && restoring_result.is_ok()
            && original_status == status_after_restoring
    }{% endif %}
{% if revocable_by_others %}
    /// Property: registering a revocation key in fresh state and querying it
    /// results in the same value
    #[concordium_quickcheck(num_tests = 500)]
    fn prop_register_revocation_key(
        pk: PublicKeyEd25519,
        credential_type: CredentialType,
        schema_ref: SchemaRef,
    ) -> bool {
        let mut state_builder = TestStateBuilder::new();
        let mut state = State::new(
            &mut state_builder,
            ISSUER_ACCOUNT,
            PUBLIC_KEY,
            issuer_metadata(),
            credential_type,
            schema_ref,
        );
        let register_result = state.register_revocation_key(pk);
        let query_result =
            state.view_revocation_keys().iter().any(|(stored_pk, _)| stored_pk == &pk);
        if query_result {
            register_result.is_ok()
        } else {
            false
        }
    }
{% endif %}
    /// Test the credential registration entrypoint.
    #[concordium_test]
    fn test_contract_register_credential() {
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
        let (credential_type, schema_ref) = get_credential_schema();
        let state = State::new(
            &mut state_builder,
            ISSUER_ACCOUNT,
            PUBLIC_KEY,
            issuer_metadata(),
            credential_type.clone(),
            schema_ref.clone(),
        );
        let mut host = TestHost::new(state, state_builder);

        let entry = credential_entry(host.state_builder());

        // Create input parameters.

        let param = RegisterCredentialParam {
            credential_info: entry.info(PUBLIC_KEY),
            auxiliary_data:  Vec::new(),
        };
        let parameter_bytes = to_bytes(&param);
        ctx.set_parameter(&parameter_bytes);

        // Create a credential
        let res = contract_register_credential(&ctx, &mut host, &mut logger);

        // Check that it was registered successfully
        claim!(res.is_ok(), "Credential registration failed: {:?}", res);
        let fetched: CredentialQueryResponse = host
            .state()
            .view_credential_info(PUBLIC_KEY)
            .expect_report("Credential is expected to exist");
        claim_eq!(
            fetched.credential_info,
            entry.info(PUBLIC_KEY),
            "Credential info expected to be equal"
        );
        claim_eq!(fetched.revocation_nonce, 0, "Revocation nonce expected to be 0");

        let status = host
            .state()
            .view_credential_status(now, PUBLIC_KEY)
            .expect_report("Status query expected to succeed");
        claim_eq!(status, CredentialStatus::Active);

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&CredentialEvent::Register(CredentialEventData {
                holder_id: PUBLIC_KEY,
                schema_ref,
                credential_type,
                metadata_url: MetadataUrl {
                    url:  CREDANIAL_METADATA_URL.into(),
                    hash: None,
                },
            })),
            "Incorrect register credential event logged"
        );
    }

    /// Test the revoke credential entrypoint, when the holder revokes the
    /// credential.
    #[concordium_test]
    fn test_revoke_by_holder() {
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
        ctx.set_named_entrypoint(OwnedEntrypointName::new_unchecked(
            "revokeCredentialHolder".into(),
        ));
        ctx.set_metadata_slot_time(now);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let (credential_type, schema_ref) = get_credential_schema();
        let state = State::new(
            &mut state_builder,
            ISSUER_ACCOUNT,
            PUBLIC_KEY,
            issuer_metadata(),
            credential_type,
            schema_ref,
        );
        let mut host = TestHost::new(state, state_builder);

        let (state, state_builder) = host.state_and_builder();
        let entry = credential_entry(state_builder);
        let credential_info = entry.info(PUBLIC_KEY);

        claim!(
            credential_info.holder_revocable,
            "Initial credential expected to be holder-revocable"
        );

        // Create a credential the holder is going to revoke
        let res = state.register_credential(&credential_info, state_builder);

        // Check that it was registered successfully
        claim!(res.is_ok(), "Credential registration failed");

        // Create singing data
        let signing_data = SigningData {
            contract_address: contract,
            entry_point:      OwnedEntrypointName::new_unchecked("revokeCredentialHolder".into()),
            nonce:            0,
            timestamp:        Timestamp::from_timestamp_millis(10000000000),
        };

        // Create input parameters for revocation.

        let revocation_reason = "Just because";

        let revoke_param = RevokeCredentialHolderParam {
            signature: SIGNATURE,
            data:      RevocationDataHolder {
                credential_id: PUBLIC_KEY,
                signing_data,
                reason: Some(revocation_reason.to_string().into()),
            },
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
            .view_credential_status(now, PUBLIC_KEY)
            .expect_report("Credential is expected to exist");
        claim_eq!(status, CredentialStatus::Revoked);

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&CredentialEvent::Revoke(RevokeCredentialEvent {
                holder_id: PUBLIC_KEY,
                revoker:   Revoker::Holder,
                reason:    Some(revocation_reason.to_string().into()),
            })),
            "Incorrect revoke credential event logged"
        );
    }{% if restorable %}

    /// Test the restore credential entrypoint.
    #[concordium_test]
    fn test_contract_restore_credential() {
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
        let (credential_type, schema_ref) = get_credential_schema();
        let state = State::new(
            &mut state_builder,
            ISSUER_ACCOUNT,
            PUBLIC_KEY,
            issuer_metadata(),
            credential_type,
            schema_ref,
        );
        let mut host = TestHost::new(state, state_builder);

        let (state, state_builder) = host.state_and_builder();
        let entry = credential_entry(state_builder);
        let credential_info = entry.info(PUBLIC_KEY);

        // Create a credential the issuer is going to restore
        let res = state.register_credential(&credential_info, state_builder);

        // Check that it was registered successfully
        claim!(res.is_ok(), "Credential registration failed");

        // Make sure the credential has the `Revoked` status
        let revoke_res = state.revoke_credential(now, PUBLIC_KEY);

        // Check that the credential was revoked successfully.
        claim!(revoke_res.is_ok(), "Credential revocation failed");

        // Create input parameters.

        let param = RestoreCredentialIssuerParam {
            credential_id: PUBLIC_KEY,
            reason:        None,
        };
        let parameter_bytes = to_bytes(&param);
        ctx.set_parameter(&parameter_bytes);

        // Check the status before restoring.
        let status = host
            .state()
            .view_credential_status(now, PUBLIC_KEY)
            .expect_report("Credential is expected to exist");
        claim_eq!(status, CredentialStatus::Revoked, "Expected Revoked");

        // Call the restore credential entrypoint
        let res = contract_restore_credential(&ctx, &mut host, &mut logger);

        // Check that it was restored succesfully
        claim!(res.is_ok(), "Credential restoring failed");
        // Check the status after restoring.
        let status = host
            .state()
            .view_credential_status(now, PUBLIC_KEY)
            .expect_report("Credential is expected to exist");
        claim_eq!(status, CredentialStatus::Active, "Expected Active");

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&CredentialEvent::Restore(RestoreCredentialEvent {
                holder_id: PUBLIC_KEY,
                reason:    None,
            })),
            "Incorrect revoke credential event logged"
        );
    }{% endif %}
}
