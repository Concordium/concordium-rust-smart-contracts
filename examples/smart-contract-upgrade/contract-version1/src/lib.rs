//! An example contract (`contract-version1`) that can be upgraded. The contract
//! has a function to upgrade the smart contract instance to a new module and
//! call optionally a migration function after the upgrade. To use this example,
//! deploy `contract-version1` and then upgrade the smart contract instance to
//! `contract-version2` by invoking the `upgrade` function with the below JSON
//! inputParameter:
//!
//! ```json
//! {
//!   "migrate": {
//!     "Some": [
//!       [
//!         "migration",
//!         ""
//!       ]
//!     ]
//!   },
//!   "module": "<ModuleReferenceContractVersion2>"
//! }
//! ```
//!
//! `contract-version2` includes a `migration` function
//! that converts the shape of the smart contract state from `contract-version1`
//! to `contract-version2`.
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
pub struct UpgradeParams {
    /// The new module reference.
    pub module:  ModuleReference,
    /// Optional entrypoint to call in the new module after upgrade.
    pub migrate: Option<(OwnedEntrypointName, OwnedParameter)>,
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
fn contract_view<'b, S: HasStateApi>(
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
