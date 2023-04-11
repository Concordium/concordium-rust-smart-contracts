//! # Credential registry
use concordium_std::*;
use core::fmt::Debug;

#[derive(Serialize, SchemaType, Clone)]
pub struct IssuerMetadata {
    name: String,
    url:  Option<String>,
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
    revocable:            bool,
    commitment:           [u8; 48],
    schema:               String,
    serialization_schema: Vec<String>,
    valid_from:           Option<Timestamp>,
    valid_until:          Option<Timestamp>,
    is_revoked:           bool,
}

impl CredentialData {
    fn get_status(&self, now: Timestamp) -> CredentialStatus {
        if self.is_revoked {
            return CredentialStatus::Revoked;
        }
        if self.valid_until.map_or(false, |x| (x < now) && !self.is_revoked) {
            return CredentialStatus::Expired;
        }
        if self.valid_from.map_or(false, |x| (now > x)) {
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
    issuer_metadata: IssuerMetadata,
    issuer_keys:     StateMap<u32, PublicKeyEd25519, S>,
    revocation_keys: StateMap<u32, PublicKeyEd25519, S>,
    credentials:     StateMap<Uuidv4, CredentialData, S>,
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
    NotAuthorized,
}

type ContractResult<A> = Result<A, ContractError>;

// Functions for creating, updating and querying the contract state.
impl<S: HasStateApi> State<S> {
    fn new(state_builder: &mut StateBuilder<S>, issuer_metadata: IssuerMetadata) -> Self {
        State {
            issuer_metadata,
            issuer_keys: state_builder.new_map(),
            revocation_keys: state_builder.new_map(),
            credentials: state_builder.new_map(),
        }
    }

    fn get_credential_data(&self, credential_id: Uuidv4) -> ContractResult<CredentialData> {
        self.credentials
            .get(&credential_id)
            .map(|x| x.clone())
            .ok_or(ContractError::CredentialNotFound)
    }

    fn get_credential_status(
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
        let res = self.credentials.insert(credential_id, credential_data.clone());
        if res.is_some() {
            Err(ContractError::CredentialAlreadyExists)
        } else {
            Ok(())
        }
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

    fn register_issuer_key(&mut self, key_index: u32, pk: PublicKeyEd25519) -> ContractResult<()> {
        let res = self.issuer_keys.insert(key_index, pk);
        if res.is_some() {
            Err(ContractError::KeyAlreadyExists)
        } else {
            Ok(())
        }
    }

    fn remove_issuer_key(&mut self, key_index: u32) -> ContractResult<()> {
        self.issuer_keys.remove(&key_index);
        Ok(())
    }

    fn register_revocation_key(
        &mut self,
        key_index: u32,
        pk: PublicKeyEd25519,
    ) -> ContractResult<()> {
        let res = self.revocation_keys.insert(key_index, pk);
        if res.is_some() {
            Err(ContractError::KeyAlreadyExists)
        } else {
            Ok(())
        }
    }

    fn remove_revocation_key(&mut self, key_index: u32) -> ContractResult<()> {
        self.issuer_keys.remove(&key_index);
        Ok(())
    }

    fn get_issuer_keys(&self) -> Vec<(u32, PublicKeyEd25519)> {
        self.issuer_keys.iter().map(|x| (*x.0, *x.1)).collect()
    }

    fn get_issuer_metadata(&self) -> IssuerMetadata { self.issuer_metadata.clone() }

    fn update_issuer_metadata(&mut self, issuer_metadata: &IssuerMetadata) {
        self.issuer_metadata = issuer_metadata.clone()
    }
}

/// Init function that creates a new smart contract.
#[init(contract = "credential_registry")]
fn init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    let issuer_metadata: IssuerMetadata = ctx.parameter_cursor().get()?;
    Ok(State::new(state_builder, issuer_metadata))
}

fn sender_is_owner(ctx: &impl HasReceiveContext) -> bool {
    ctx.sender().matches_account(&ctx.owner())
}

#[receive(
    contract = "credential_registry",
    name = "getCredentialData",
    parameter = "Uuid",
    error = "ContractError",
    return_value = "CredentialData"
)]
fn contract_get_credential_data<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<CredentialData, ContractError> {
    let credential_id = ctx.parameter_cursor().get()?;
    let data = host.state().get_credential_data(credential_id)?;
    Ok(data)
}

#[receive(
    contract = "credential_registry",
    name = "getCredentialStatus",
    parameter = "Uuid",
    error = "ContractError",
    return_value = "CredentialStatus"
)]
fn contract_get_credential_status<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<CredentialStatus, ContractError> {
    let credential_id = ctx.parameter_cursor().get()?;
    let now = ctx.metadata().slot_time();
    let status = host.state().get_credential_status(now, credential_id)?;
    Ok(status)
}

#[derive(Serial, Deserial, SchemaType)]
pub struct RegisterCredentialParameter {
    credential_id:   Uuidv4,
    credential_data: CredentialData,
}

#[receive(
    contract = "credential_registry",
    name = "registerCredential",
    parameter = "RegisterCredentialParameter",
    error = "ContractError",
    mutable
)]
fn contract_register_credeintial<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(), ContractError> {
    ensure!(sender_is_owner(ctx), ContractError::NotAuthorized);
    let parameter: RegisterCredentialParameter = ctx.parameter_cursor().get()?;
    host.state_mut().register_credential(parameter.credential_id, &parameter.credential_data)
}

#[receive(
    contract = "credential_registry",
    name = "revokeCredential",
    parameter = "Uuid",
    error = "ContractError",
    mutable
)]
fn contract_revoke_credeintial<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(), ContractError> {
    ensure!(sender_is_owner(ctx), ContractError::NotAuthorized);
    // TODO add signature-based authentication
    let credential_id = ctx.parameter_cursor().get()?;
    let now = ctx.metadata().slot_time();
    host.state_mut().revoke_credential(now, credential_id)
}

#[derive(Serial, Deserial, SchemaType)]
pub struct RegisterKeyParameter {
    key_index: u32,
    key:       PublicKeyEd25519,
}

#[receive(
    contract = "credential_registry",
    name = "registerIssuerKey",
    parameter = "RegisterKeyParameter",
    error = "ContractError",
    mutable
)]
fn contract_register_issuer_key<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(), ContractError> {
    ensure!(sender_is_owner(ctx), ContractError::NotAuthorized);
    let parameter: RegisterKeyParameter = ctx.parameter_cursor().get()?;
    host.state_mut().register_issuer_key(parameter.key_index, parameter.key)
}

#[receive(
    contract = "credential_registry",
    name = "removeIssuerKey",
    parameter = "u32",
    error = "ContractError",
    mutable
)]
fn contract_remove_issuer_key<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(), ContractError> {
    ensure!(sender_is_owner(ctx), ContractError::NotAuthorized);
    let index = ctx.parameter_cursor().get()?;
    host.state_mut().remove_issuer_key(index)
}

#[receive(
    contract = "credential_registry",
    name = "registerRevocationKey",
    parameter = "RegisterKeyParameter",
    error = "ContractError",
    mutable
)]
fn contract_register_revocation_key<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(), ContractError> {
    ensure!(sender_is_owner(ctx), ContractError::NotAuthorized);
    let parameter: RegisterKeyParameter = ctx.parameter_cursor().get()?;
    host.state_mut().register_revocation_key(parameter.key_index, parameter.key)
}

#[receive(
    contract = "credential_registry",
    name = "removeRevocationKey",
    parameter = "u32",
    error = "ContractError",
    mutable
)]
fn contract_remove_revocation_key<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> Result<(), ContractError> {
    ensure!(sender_is_owner(ctx), ContractError::NotAuthorized);
    let index = ctx.parameter_cursor().get()?;
    host.state_mut().remove_revocation_key(index)
}

#[receive(
    contract = "credential_registry",
    name = "getIssuerKeys",
    error = "ContractError",
    return_value = "Vec<PublicKeyEd25519>"
)]
fn contract_get_issuer_keys<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<Vec<(u32, PublicKeyEd25519)>, ContractError> {
    let keys = host.state().get_issuer_keys();
    Ok(keys)
}

#[receive(
    contract = "credential_registry",
    name = "getIssuerMetadata",
    error = "ContractError",
    return_value = "IssuerMetadata"
)]
fn contract_get_issuer_metadata<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> Result<IssuerMetadata, ContractError> {
    Ok(host.state().get_issuer_metadata())
}

#[receive(
    contract = "credential_registry",
    name = "updateIssuerMetadata",
    parameter = "IssuerMetadata",
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

    impl Arbitrary for CredentialData {
        fn arbitrary(g: &mut Gen) -> CredentialData {
            CredentialData {
                holder_id:            PublicKeyEd25519([0u8; 32].map(|_| Arbitrary::arbitrary(g))),
                revocable:            Arbitrary::arbitrary(g),
                commitment:           [0u8; 48].map(|_| Arbitrary::arbitrary(g)),
                schema:               Arbitrary::arbitrary(g),
                serialization_schema: Arbitrary::arbitrary(g),
                valid_from:           Arbitrary::arbitrary(g),
                valid_until:          Arbitrary::arbitrary(g),
                is_revoked:           Arbitrary::arbitrary(g),
            }
        }
    }

    const ISSUER_NAME: &str = "Example University";
    const ISSUER_URL: &str = "https://example-university.com";

    fn issuer_metadata() -> IssuerMetadata {
        IssuerMetadata {
            name: ISSUER_NAME.to_string(),
            url:  Some(ISSUER_URL.to_string()),
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
        state_result.expect_report("Contract initialization results in error");
    }

    // Property: registering a credential and then querying it results in the same
    // credential object.
    #[concordium_quickcheck(num_tests = 20)]
    fn prop_register_get_credential(credential_id: Uuidv4, data: CredentialData) -> bool {
        let mut state_builder = TestStateBuilder::new();
        let mut state = State::new(&mut state_builder, issuer_metadata());
        let register_result = state.register_credential(credential_id, &data);
        let query_result = state.get_credential_data(credential_id);
        if let Ok(fetched_data) = query_result {
            register_result.is_ok() && (fetched_data == data)
        } else {
            false
        }
    }

    // Property: if a credential is revoked successfully, the status changes to
    // `Revoked`
    #[concordium_quickcheck(num_tests = 20)]
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
        let status_result = state.get_credential_status(now, credential_id);
        TestResult::from_bool(status_result == Ok(CredentialStatus::Revoked))
    }
}
