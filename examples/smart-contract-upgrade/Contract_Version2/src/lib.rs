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
    admin:     AccountAddress,
    old_state: String,
    new_state: String,
}

/// The old smart contract state from `Contract_Version1`.
#[derive(Serialize, SchemaType, Clone)]
pub struct OldState {
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
    _ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<()> {
    Ok(())
}

/// View function that returns the content of the state.
#[receive(contract = "smart_contract_upgrade", name = "view", return_value = "State")]
fn contract_view<'b, S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &'b impl HasHost<State, StateApiType = S>,
) -> ReceiveResult<&'b State> {
    Ok(host.state())
}

/// Migration function that should be called as part of the `upgrade` invoke in
/// `Contract_Version1`. This function converts the shape of the smart contract
/// state from `Contract_Version1` to `Contract_Version2`.
///
/// It rejects if:
/// - Sender is not this smart contract instance.
/// - It fails to read the state root.
#[receive(
    contract = "smart_contract_upgrade",
    name = "migration",
    error = "CostumContractError",
    low_level
)]
fn contract_migration<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<S>,
) -> ContractResult<()> {
    // Check that only this contract instance can call this function.
    ensure!(ctx.sender().matches_contract(&ctx.self_address()), CostumContractError::Unauthorized);

    // Read the old top-level contract state.
    let state: OldState = host.state().read_root()?;

    let new_state = State {
        admin:     state.admin,
        old_state: state.to_be_migrated_state,
        new_state: "This is the new state.".to_string(),
    };

    host.state_mut().write_root(&new_state);
    host.commit_state();

    Ok(())
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

// TODO: Add tests once the new integration testing library is released.
