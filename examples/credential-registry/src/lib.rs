//! # Credential registry
use concordium_cis2::MetadataUrl;
use concordium_std::*;
use core::fmt::Debug;

#[derive(Serialize, SchemaType)]
struct RegisterCredentialEvent {
    credential_id: Uuidv4,
    holder_id:     PublicKeyEd25519,
    schema_ref:    String,
}

#[derive(Serialize, SchemaType)]
struct UpdateCredentialEvent {
    credential_id: Uuidv4,
    holder_id:     PublicKeyEd25519,
    schema_ref:    String,
}

#[derive(Serialize, SchemaType)]
enum Revoker {
    Issuer,
    Holder,
    Other(PublicKeyEd25519),
}

#[derive(Serialize, SchemaType)]
struct RevokeCredentialEvent {
    credential_id: Uuidv4,
    holder_id:     PublicKeyEd25519,
    revoker:       Revoker,
    reason:        Option<String>,
}

type Uuidv4 = u128;

#[derive(Serialize, SchemaType, PartialEq, Eq, Clone, Copy, Debug)]
pub enum CredentialStatus {
    Active,
    Revoked,
    Expired,
    NotActivated,
}

#[derive(Serialize, SchemaType, PartialEq, Eq, Clone, Debug)]
pub struct CredentialData {
    holder_id:            PublicKeyEd25519,
    is_holder_revocable:  bool,
    commitment:           [u8; 48],
    schema:               String,
    serialization_schema: Vec<String>,
    valid_from:           Option<Timestamp>,
    valid_until:          Option<Timestamp>,
}

#[derive(Serialize, SchemaType, PartialEq, Eq, Clone, Debug)]
pub struct CredentialEntry {
    credential_data:  CredentialData,
    revocation_nonce: u64,
    is_revoked:       bool,
}

impl CredentialEntry {
    fn get_status(&self, now: Timestamp) -> CredentialStatus {
        if self.is_revoked {
            return CredentialStatus::Revoked;
        }
        if self.credential_data.valid_until.map_or(false, |x| (x < now) && !self.is_revoked) {
            return CredentialStatus::Expired;
        }
        if self.credential_data.valid_from.map_or(false, |x| now < x) {
            return CredentialStatus::NotActivated;
        }
        CredentialStatus::Active
    }
}

/// The registry state
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

/// Errors.
#[derive(Debug, PartialEq, Eq, Reject, Serial, SchemaType)]
enum ContractError {
    /// Failed parsing the parameter.
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

// Functions for creating, updating and querying the contract state.
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
            is_revoked:       false,
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
        self.credentials
            .get_mut(&credential_id)
            .map(|mut x| x.credential_data = credential_data.clone());
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
        credential.is_revoked = true;
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

/// Init function that creates a new smart contract.
#[init(contract = "credential_registry")]
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

#[receive(
    contract = "credential_registry",
    name = "viewCredentialEntry",
    parameter = "Uuid",
    error = "ContractError",
    return_value = "CredentialEntry"
)]
fn contract_view_credential_entry<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<CredentialEntry, ContractError> {
    let credential_id = ctx.parameter_cursor().get()?;
    let data = host.state().view_credential_data(credential_id)?;
    Ok(data)
}

#[receive(
    contract = "credential_registry",
    name = "viewCredentialStatus",
    parameter = "Uuid",
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

#[derive(Serial, Deserial, SchemaType)]
pub struct CredentialDataParameter {
    credential_id:   Uuidv4,
    credential_data: CredentialData,
}

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
    logger.log(&RegisterCredentialEvent {
        credential_id: parameter.credential_id,
        holder_id:     parameter.credential_data.holder_id,
        schema_ref:    parameter.credential_data.schema,
    })?;
    Ok(())
}

#[receive(
    contract = "credential_registry",
    name = "updateCredential",
    parameter = "CredentialDataParameter",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_update_credeintial<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> Result<(), ContractError> {
    ensure!(sender_is_owner(ctx), ContractError::NotAuthorized);
    let parameter: CredentialDataParameter = ctx.parameter_cursor().get()?;
    host.state_mut().update_credential(parameter.credential_id, &parameter.credential_data)?;
    logger.log(&UpdateCredentialEvent {
        credential_id: parameter.credential_id,
        holder_id:     parameter.credential_data.holder_id,
        schema_ref:    parameter.credential_data.schema,
    })?;
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
    reason:               Option<String>,
}

/// Performs authorization based on the signature and a public key
///
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
                        registry_entry.credential_data.is_holder_revocable,
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

#[derive(Serialize, SchemaType)]
pub struct RemovePublicKeyParameters(#[concordium(size_length = 2)] pub Vec<u8>);

#[receive(
    contract = "credential_registry",
    name = "removeIssuerKeys",
    parameter = "RemovePublicKeyParameters",
    error = "ContractError",
    mutable
)]
fn contract_remove_issuer_key<S: HasStateApi>(
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

#[receive(
    contract = "credential_registry",
    name = "viewRevocationKey",
    parameter = "u8",
    error = "ContractError",
    mutable
)]
fn contract_view_revocation_key<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(PublicKeyEd25519, u64), ContractError> {
    let index = ctx.parameter_cursor().get()?;
    host.state().view_revocation_key(index)
}

#[receive(
    contract = "credential_registry",
    name = "viewIssuerKeys",
    error = "ContractError",
    return_value = "Vec<PublicKeyEd25519>"
)]
fn contract_view_issuer_keys<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<Vec<(u8, PublicKeyEd25519)>, ContractError> {
    let keys = host.state().view_issuer_keys();
    Ok(keys)
}

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

/// View function that returns the content of the state.
#[receive(contract = "credential_registry", name = "view", return_value = "State")]
fn view<'b, S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &'b impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<&'b State<S>> {
    Ok(host.state())
}

#[concordium_cfg_test]
mod tests {

    use super::*;
    use quickcheck::*;
    use test_infrastructure::*;

    const ATTR_NAMES: [&str; 8] = [
        "dob",
        "first_name",
        "points",
        "education",
        "Use%various^chars",
        "$somehting",
        "path.to.a.field",
        "123",
    ];

    // Generate a random string with the probability 1/8, otherwise pick a name from
    // a predefined list
    fn arbitrary_attr_name(g: &mut Gen) -> String {
        let i: u32 = Arbitrary::arbitrary(g);
        match i % 8 {
            j @ 0..=7 => ATTR_NAMES[j as usize].to_string(),
            _ => Arbitrary::arbitrary(g),
        }
    }

    // Generate up to 16 attributes in a serialization schema
    fn arbitrary_serialization_schema(g: &mut Gen) -> Vec<String> {
        let mut v = Vec::new();
        let n: u32 = Arbitrary::arbitrary(g);
        for _ in 0..n % 16 {
            v.push(arbitrary_attr_name(g));
        }
        v
    }

    // It is convenient to use arbitrary data even for simple properites, because it
    // allows us to avoid defining input data manually.
    impl Arbitrary for CredentialData {
        fn arbitrary(g: &mut Gen) -> CredentialData {
            CredentialData {
                holder_id:            PublicKeyEd25519([0u8; 32].map(|_| Arbitrary::arbitrary(g))),
                is_holder_revocable:  Arbitrary::arbitrary(g),
                commitment:           [0u8; 48].map(|_| Arbitrary::arbitrary(g)),
                schema:               Arbitrary::arbitrary(g),
                serialization_schema: arbitrary_serialization_schema(g),
                valid_from:           Arbitrary::arbitrary(g),
                valid_until:          Arbitrary::arbitrary(g),
            }
        }
    }

    impl Arbitrary for CredentialEntry {
        fn arbitrary(g: &mut Gen) -> CredentialEntry {
            CredentialEntry {
                credential_data:  Arbitrary::arbitrary(g),
                revocation_nonce: Arbitrary::arbitrary(g),
                is_revoked:       Arbitrary::arbitrary(g),
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

    fn credential_entry() -> CredentialEntry {
        CredentialEntry {
            credential_data:  CredentialData {
                holder_id:            PublicKeyEd25519([0u8; 32]),
                is_holder_revocable:  true,
                commitment:           [0u8; 48],
                schema:               "".into(),
                serialization_schema: Vec::new(),
                valid_from:           None,
                valid_until:          None,
            },
            revocation_nonce: 0,
            is_revoked:       false,
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

    #[concordium_test]
    fn test_get_status_expired() {
        let mut entry = credential_entry();
        let now = Timestamp::from_timestamp_millis(10);
        entry.credential_data.valid_until = Some(Timestamp::from_timestamp_millis(0));
        let expected = CredentialStatus::Expired;
        let status = entry.get_status(now);
        claim_eq!(
            entry.get_status(now),
            CredentialStatus::Expired,
            "Expected status {:?}, got {:?}",
            expected,
            status
        );
    }

    #[concordium_test]
    fn test_get_status_not_activated() {
        let mut entry = credential_entry();
        let now = Timestamp::from_timestamp_millis(10);
        entry.credential_data.valid_from = Some(Timestamp::from_timestamp_millis(20));
        let expected = CredentialStatus::NotActivated;
        let status = entry.get_status(now);
        claim_eq!(
            entry.get_status(now),
            expected,
            "Expected status {:?}, got {:?}",
            expected,
            status
        );
    }

    #[concordium_test]
    fn test_get_status_revoked_expired_still_revoked() {
        let mut entry = credential_entry();
        let now = Timestamp::from_timestamp_millis(10);
        entry.is_revoked = true;
        entry.credential_data.valid_until = Some(Timestamp::from_timestamp_millis(0));
        let expected = CredentialStatus::Revoked;
        let status = entry.get_status(now);
        claim_eq!(
            entry.get_status(now),
            expected,
            "Expected status {:?}, got {:?}",
            expected,
            status
        );
    }

    // Property: once the `is_revoked` flag is set to `true`, the status is always
    // `Revoked` regardless of values of valid_from and valid_until
    #[concordium_quickcheck]
    fn prop_revoked_stays_revoked(mut entry: CredentialEntry, now: Timestamp) -> bool {
        entry.is_revoked = true;
        entry.get_status(now) == CredentialStatus::Revoked
    }

    // Property: registering a credential and then querying it results in the same
    // credential data, which is not revoked and has nonce = `0`
    #[concordium_quickcheck]
    fn prop_register_view_credential(credential_id: Uuidv4, data: CredentialData) -> bool {
        let mut state_builder = TestStateBuilder::new();
        let mut state = State::new(&mut state_builder, issuer_metadata());
        let register_result = state.register_credential(credential_id, &data);
        let query_result = state.view_credential_data(credential_id);
        if let Ok(fetched_data) = query_result {
            register_result.is_ok()
                && (fetched_data.credential_data == data)
                && !fetched_data.is_revoked
                && fetched_data.revocation_nonce == 0
        } else {
            false
        }
    }

    // Property: updating an existing credential and then querying it results in the
    // same credential data. The update keeps intact the revocation flag and
    // nonce.
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
                && (fetched_data.is_revoked == initial_entry.is_revoked)
                && (fetched_data.revocation_nonce == initial_entry.revocation_nonce)
        } else {
            false
        }
    }

    // Property: if a credential is revoked successfully, the status changes to
    // `Revoked`
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

    // Property: registering an issuer key and querying it results in the same value
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

    // Property: registering a revocation key and querying it results in the same
    // value
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
}
