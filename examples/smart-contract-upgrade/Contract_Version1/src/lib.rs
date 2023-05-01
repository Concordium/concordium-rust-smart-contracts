//! An example contract that can be upgraded. The contract has a function to
//! upgrade the smart contract instance to a new module and call optionally a
//! migration function after the upgrade. To use this example, deploy
//! `Contract_Version1` and then upgrade the smart contract instance to
//! `Contract_Version2` by invoking the `upgrade` function with the below JSON
//! inputParameter:
//!
//! {"migrate": {"Some": [["migration",""]]},"module":
//! <ModuleReferenceContract_Version2>}
//!
//! `Contract_Version2` includes a `migration` function
//! that converts the shape of the smart contract state from `Contract_Version1`
//! to `Contract_Version2`.
use concordium_std::*;

/// The smart contract state.
#[derive(Serialize, SchemaType, Clone)]
pub struct State {
    admin:                    AccountAddress,
    not_to_be_migrated_state: String,
    to_be_migrated_state:     String,
}

/// The parameter type for the contract function `upgrade`.
/// Takes the new module and optionally an entrypoint to call in the new module
/// after triggering the upgrade. The upgrade is reverted if the entrypoint
/// fails. This is useful for doing migration in the same transaction triggering
/// the upgrade.
#[derive(Serialize, SchemaType)]
struct UpgradeParams {
    /// The new module reference.
    module:  ModuleReference,
    /// Optional entrypoint to call in the new module after upgrade.
    migrate: Option<(OwnedEntrypointName, OwnedParameter)>,
}

/// Smart contract errors.
#[derive(PartialEq, Eq, Reject, Serial, SchemaType)]
enum CostumContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParamsError,
    /// Invoker to entrypoint is unauthorized.
    Unauthorized,
    /// Failed to invoke a contract.
    InvokeContractError,
    /// Upgrade failed because the new module does not exist.
    FailedUpgradeMissingModule,
    /// Upgrade failed because the new module does not contain a contract with a
    /// matching name.
    FailedUpgradeMissingContract,
    /// Upgrade failed because the smart contract version of the module is not
    /// supported.
    FailedUpgradeUnsupportedModuleVersion,
}

/// Mapping errors related to contract upgrades to CustomContractError.
impl From<UpgradeError> for CostumContractError {
    #[inline(always)]
    fn from(ue: UpgradeError) -> Self {
        match ue {
            UpgradeError::MissingModule => Self::FailedUpgradeMissingModule,
            UpgradeError::MissingContract => Self::FailedUpgradeMissingContract,
            UpgradeError::UnsupportedModuleVersion => Self::FailedUpgradeUnsupportedModuleVersion,
        }
    }
}

/// Mapping errors related to contract invocations to CustomContractError.
impl<T> From<CallContractError<T>> for CostumContractError {
    fn from(_cce: CallContractError<T>) -> Self { Self::InvokeContractError }
}

type ContractResult<A> = Result<A, CostumContractError>;

/// Init function that creates a new smart contract.
#[init(contract = "smart_contract_upgrade")]
fn contract_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<State> {
    Ok(State {
        admin:                    ctx.init_origin(),
        not_to_be_migrated_state: "This state should NOT be migrated as part of the smart \
                                   contract upgrade."
            .to_string(),
        to_be_migrated_state:     "This state should be migrated as part of the smart contract \
                                   upgrade."
            .to_string(),
    })
}

/// View function that returns the content of the state.
#[receive(contract = "smart_contract_upgrade", name = "view", return_value = "State")]
fn view<'b, S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &'b impl HasHost<State, StateApiType = S>,
) -> ReceiveResult<&'b State> {
    Ok(host.state())
}

/// Upgrade this smart contract instance to a new module and call optionally a
/// migration function after the upgrade.
///
/// It rejects if:
/// - Sender is not the admin of the contract instance.
/// - It fails to parse the parameter.
/// - If the ugrade fails.
/// - If the migration invoke fails.
///
/// This function is marked as `low_level`. This is **necessary** since the
/// high-level mutable functions store the state of the contract at the end of
/// execution. This conflicts with migration since the shape of the state
/// **might** be changed by the migration function. If the state is then written
/// by this function it would overwrite the state stored by the migration
/// function.
#[receive(
    contract = "smart_contract_upgrade",
    name = "upgrade",
    parameter = "UpgradeParams",
    error = "CostumContractError",
    low_level
)]
fn contract_upgrade<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<S>,
) -> ContractResult<()> {
    // Read the top-level contract state.
    let state: State = host.state().read_root()?;

    // Check that only the admin is authorized to upgrade the smart contract.
    ensure!(ctx.sender().matches_account(&state.admin), CostumContractError::Unauthorized);
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

/// Transfer the admin address to a new admin address.
///
/// It rejects if:
/// - Sender is not the current admin of the contract instance.
/// - It fails to parse the parameter.
#[receive(
    contract = "smart_contract_upgrade",
    name = "updateAdmin",
    parameter = "AccountAddress",
    error = "CostumContractError",
    mutable
)]
fn contract_update_admin<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> ContractResult<()> {
    // Check that only the current admin is authorized to update the admin address.
    ensure!(ctx.sender().matches_account(&host.state().admin), CostumContractError::Unauthorized);

    // Parse the parameter.
    let new_admin = ctx.parameter_cursor().get()?;

    // Update the admin variable.
    host.state_mut().admin = new_admin;

    Ok(())
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    const ADMIN_ACCOUNT: AccountAddress = AccountAddress([0u8; 32]);
    const ADMIN_ADDRESS: Address = Address::Account(ADMIN_ACCOUNT);

    #[concordium_test]
    fn test_upgradability() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);
        ctx.set_owner(ADMIN_ACCOUNT);

        let self_address = ContractAddress::new(0, 0);
        ctx.set_self_address(self_address);

        let new_module_ref = ModuleReference::from([0u8; 32]);
        let migration_entrypoint = OwnedEntrypointName::new_unchecked("migration".into());

        let mut ctx = TestInitContext::empty();

        ctx.set_init_origin(ADMIN_ACCOUNT);

        let mut state_builder = TestStateBuilder::new();

        let state = contract_init(&ctx, &mut state_builder).unwrap();

        // and parameter.
        let parameter = UpgradeParams {
            module:  new_module_ref,
            migrate: Some((
                migration_entrypoint.clone(),
                OwnedParameter::new_unchecked(Vec::new()),
            )),
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

        // let mut host = TestHost::new(TestStateApi::new(), state_builder);

        // let host = TestHost::new(state, state_builder);

        // host.setup_mock_upgrade(new_module_ref, Ok(()));
        // host.setup_mock_entrypoint(self_address, migration_entrypoint,
        // MockFn::returning_ok(()));

        // let result = contract_upgrade(&ctx, &mut host);

        // claim_eq!(result, Ok(()));
    }
}
