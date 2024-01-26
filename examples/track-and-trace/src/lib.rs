//! # Implementation of a simple track-and-trace contract.
//!
//! ## Grant and Revoke roles:
//! The contract has access control roles. The available roles are ADMIN (can
//! grant/revoke roles, create a new item, and update the status of an item),
//! PRODUCER (can update the status of an item from `Produced` to `InTransit`),
//! TRANSPORTER (can update the status of an item from `InTransit` to
//! `InStore`), and SELLER (can update the status of an item from `InStore` to
//! `Sold`). Several addresses can have the same role and an address can have
//! several roles.
//!
//! ## State machine:
//! The track-and-trace contract is modeled based on a state machine. The flow
//! of the state machine is as follows: The ADMIN creates a new item with status
//! `Produced`. Each new item is assigned the `next_item_id`. The `next_item_id`
//! value is sequentially increased by 1 in the contract's state. The different
//! roles can update the item's status based on the rules of the state machine
//! as follows: Produced -> InTransit -> InStore -> Sold. The ADMIN role is an
//! exception and can set an item's status to any value at any time ignoring the
//! state machine rules.
#![cfg_attr(not(feature = "std"), no_std)]
use concordium_cis2::*;
use concordium_std::{collections::BTreeMap, *};

/// Event tags.
pub const ITEM_CREATED_EVENT_TAG: u8 = 0;
pub const ITEM_STATUS_CHANGED_EVENT_TAG: u8 = 1;
pub const GRANT_ROLE_EVENT_TAG: u8 = 2;
pub const REVOKE_ROLE_EVENT_TAG: u8 = 3;

/// Custom type for the item id.
type ItemID = u64;

/// Tagged events to be serialized for the event log.
#[derive(Debug, Serial, Deserial, PartialEq, Eq)]
pub enum Event {
    /// The event tracks when an item is created.
    ItemCreated(ItemCreatedEvent),
    /// The event tracks when the item's status is updated.
    ItemStatusChanged(ItemStatusChangedEvent),
    /// The event tracks when a new role is granted to an address.
    GrantRole(GrantRoleEvent),
    /// The event tracks when a role is revoked from an address.
    RevokeRole(RevokeRoleEvent),
}

/// The ItemCreatedEvent is logged when an item is created.
#[derive(Serialize, SchemaType, Debug, PartialEq, Eq)]
pub struct ItemCreatedEvent {
    /// The item's id.
    pub item_id:      ItemID,
    /// The item's metadata_url.
    pub metadata_url: Option<MetadataUrl>,
}

/// The ItemStatusChangedEvent is logged when the status of an item is updated.
#[derive(Serialize, SchemaType, Debug, PartialEq, Eq)]
pub struct ItemStatusChangedEvent {
    /// The item's id.
    pub item_id:         ItemID,
    /// The item's new status.
    pub new_status:      Status,
    /// Any additional data encoded as generic bytes. Usecase-specific data can
    /// be included here such as temperature, longitude, latitude, ... .
    pub additional_data: AdditionalData,
}

/// The GrantRoleEvent is logged when a new role is granted to an address.
#[derive(Serialize, SchemaType, Debug, PartialEq, Eq)]
pub struct GrantRoleEvent {
    /// The address that has been its role granted.
    pub address: Address,
    /// The role that was granted to the above address.
    pub role:    Roles,
}

/// The RevokeRoleEvent is logged when a role is revoked from an address.
#[derive(Serialize, SchemaType, Debug, PartialEq, Eq)]
pub struct RevokeRoleEvent {
    /// Address that has been its role revoked.
    pub address: Address,
    /// The role that was revoked from the above address.
    pub role:    Roles,
}

/// A struct containing a set of roles granted to an address.
#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
struct AddressRoleState<S> {
    /// Set of roles.
    roles: StateSet<Roles, S>,
}

/// Enum of available roles in this contract. Several addresses can have the
/// same role and an address can have several roles.
#[derive(Serialize, PartialEq, Eq, Reject, SchemaType, Clone, Copy, Debug)]
pub enum Roles {
    /// Admin role.
    ADMIN,
    /// Producer role.
    PRODUCER,
    /// Transporter role.
    TRANSPORTER,
    /// Seller role.
    SELLER,
}

/// Enum of the statuses that an item can have.
#[derive(Serialize, PartialEq, Eq, Reject, SchemaType, Clone, Copy, Debug)]
pub enum Status {
    /// Item is produced.
    Produced,
    /// Item is in transit.
    InTransit,
    /// Item is in store.
    InStore,
    /// Item is sold.
    Sold,
}

impl Status {
    fn new() -> Self { Status::Produced }
}

// Implementing a custom schemaType for the `Event` struct containing all
// events. This custom implementation flattens the fields to avoid one
// level of nesting. Deriving the schemaType would result in e.g.: {"Nonce":
// [{...fields}] }. In contrast, this custom schemaType implementation results
// in e.g.: {"Nonce": {...fields} }
impl schema::SchemaType for Event {
    fn get_type() -> schema::Type {
        let mut event_map = BTreeMap::new();
        event_map.insert(
            ITEM_CREATED_EVENT_TAG,
            (
                "ItemCreated".to_string(),
                schema::Fields::Named(vec![
                    (String::from("itemId"), ItemID::get_type()),
                    (String::from("metadataURL"), Option::<MetadataUrl>::get_type()),
                ]),
            ),
        );
        event_map.insert(
            ITEM_STATUS_CHANGED_EVENT_TAG,
            (
                "ItemStatusChanged".to_string(),
                schema::Fields::Named(vec![
                    (String::from("itemId"), ItemID::get_type()),
                    (String::from("newStatus"), Status::get_type()),
                    (String::from("additionalData"), AdditionalData::get_type()),
                ]),
            ),
        );
        event_map.insert(
            GRANT_ROLE_EVENT_TAG,
            (
                "GrantRole".to_string(),
                schema::Fields::Named(vec![
                    (String::from("address"), Address::get_type()),
                    (String::from("role"), Roles::get_type()),
                ]),
            ),
        );
        event_map.insert(
            REVOKE_ROLE_EVENT_TAG,
            (
                "RevokeRole".to_string(),
                schema::Fields::Named(vec![
                    (String::from("address"), Address::get_type()),
                    (String::from("role"), Roles::get_type()),
                ]),
            ),
        );
        schema::Type::TaggedEnum(event_map)
    }
}

/// A struct containing a state of one item.
#[derive(Debug, Serialize, SchemaType, Clone, PartialEq, Eq)]
pub struct ItemState {
    /// The status of the item.
    pub status:       Status,
    /// The metadata_url of the item.
    pub metadata_url: Option<MetadataUrl>,
}

/// The state of the smart contract.
/// This state can be viewed by querying the node with the command
/// `concordium-client contract invoke` using the `view` function as entrypoint.
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S = StateApi> {
    /// The next item id that will be assigned to an item when the admin creates
    /// it. This value is sequentially increased by 1.
    next_item_id: ItemID,
    /// A map containing all roles granted to addresses.
    roles:        StateMap<Address, AddressRoleState<S>, S>,
    /// A map containing all items with their states.
    items:        StateMap<ItemID, ItemState, S>,
}

/// The different errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
pub enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams, // -1
    /// Failed logging because the log is full.
    LogFull, // -2
    /// Failed logging because the log is malformed.
    LogMalformed, // -3
    /// Failed because the actor is not authorized to invoke the entry point.
    Unauthorized, // -4
    /// Failed to revoke role because it was not granted in the first place.
    RoleWasNotGranted, // -5
    /// Failed to grant role because it was granted already in the first place.
    RoleWasAlreadyGranted, // -6
    /// Item with given item id already exists in the state.
    ItemAlreadyExists, // -7
    /// Item with given item id does not exist in the state.
    ItemDoesNotExist, // -8
    /// The item is already in the final state and cannot be updated based on
    /// the state machine rules.
    FinalState, // -9
}

/// Mapping the logging errors to CustomContractError.
impl From<LogError> for CustomContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

/// Custom type for the contract result.
pub type ContractResult<A> = Result<A, CustomContractError>;

impl State {
    /// Grant role to an address.
    fn grant_role(&mut self, account: &Address, role: Roles, state_builder: &mut StateBuilder) {
        self.roles.entry(*account).or_insert_with(|| AddressRoleState {
            roles: state_builder.new_set(),
        });

        self.roles.entry(*account).and_modify(|entry| {
            entry.roles.insert(role);
        });
    }

    /// Revoke role from an address.
    fn revoke_role(&mut self, account: &Address, role: Roles) {
        self.roles.entry(*account).and_modify(|entry| {
            entry.roles.remove(&role);
        });
    }

    /// Check if an address has a role.
    fn has_role(&self, account: &Address, role: Roles) -> bool {
        return match self.roles.get(account) {
            None => false,
            Some(roles) => roles.roles.contains(&role),
        };
    }

    /// Change the item status to the given new status. The function reverts if
    /// the item does not exist.
    fn change_item_status(
        &mut self,
        item_index: ItemID,
        new_state: Status,
    ) -> Result<(), CustomContractError> {
        let mut previous_state =
            self.items.entry(item_index).occupied_or(CustomContractError::ItemDoesNotExist)?;

        previous_state.status = new_state;

        Ok(())
    }
}

/// Init function that creates a new contract.
#[init(contract = "track_and_trace", event = "Event", enable_logger)]
fn init(
    ctx: &InitContext,
    state_builder: &mut StateBuilder,
    logger: &mut impl HasLogger,
) -> InitResult<State> {
    // Get the instantiater of this contract instance.
    let invoker = Address::Account(ctx.init_origin());

    // Creating `State`
    let mut state = State {
        next_item_id: 0u64,
        roles:        state_builder.new_map(),
        items:        state_builder.new_map(),
    };

    // Grant ADMIN role.
    state.grant_role(&invoker, Roles::ADMIN, state_builder);
    logger.log(&Event::GrantRole(GrantRoleEvent {
        address: invoker,
        role:    Roles::ADMIN,
    }))?;

    Ok(state)
}

/// Return_value of the `view` function contains the content of the state.
#[derive(Serialize, SchemaType, PartialEq, Eq, Debug)]
pub struct ViewState {
    /// The next item id that will be assigned to an item when the admin creates
    /// it.
    pub next_item_id: ItemID,
    /// A vector containing all roles granted to addresses.
    pub roles:        Vec<(Address, Vec<Roles>)>,
    /// A vector containing all items with their states.
    pub items:        Vec<(ItemID, ItemState)>,
}

/// View function for testing. This function reports on the entire state of the
/// contract for testing purposes.
#[receive(contract = "track_and_trace", name = "view", return_value = "ViewState")]
fn contract_view(_ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<ViewState> {
    let state = host.state();

    let roles: Vec<(Address, Vec<Roles>)> = state
        .roles
        .iter()
        .map(|(key, value)| {
            let mut roles_vec = Vec::new();
            for role in value.roles.iter() {
                roles_vec.push(*role);
            }
            (*key, roles_vec)
        })
        .collect();

    let items: Vec<(ItemID, ItemState)> =
        state.items.iter().map(|(key, value)| (*key, (*value).clone())).collect();

    Ok(ViewState {
        roles,
        items,
        next_item_id: state.next_item_id,
    })
}

/// Receive function for the ADMIN to create a new item.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The sender is not the ADMIN of the contract instance.
/// - The item already exists in the state which should technically not happen.
/// - It fails to log the `ItemCreatedEvent`.
#[receive(
    contract = "track_and_trace",
    name = "createItem",
    parameter = "Option<MetadataUrl>",
    error = "CustomContractError",
    mutable,
    enable_logger
)]
fn create_item(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> Result<(), CustomContractError> {
    // Parse the parameter.
    let metadata_url: Option<MetadataUrl> = ctx.parameter_cursor().get()?;

    // Check that only the ADMIN is authorized to create a new item.
    ensure!(host.state().has_role(&ctx.sender(), Roles::ADMIN), CustomContractError::Unauthorized);

    // Get the next available item id.
    let next_item_id = host.state().next_item_id;
    // Increase the item id tracker in the state.
    host.state_mut().next_item_id += 1;

    // Create the item in state.
    let previous_item = host.state_mut().items.insert(next_item_id, ItemState {
        metadata_url: metadata_url.clone(),
        status:       Status::new(),
    });

    ensure_eq!(previous_item, None, CustomContractError::ItemAlreadyExists);

    // Log an ItemCreatedEvent.
    logger.log(&Event::ItemCreated(ItemCreatedEvent {
        item_id: next_item_id,
        metadata_url,
    }))?;

    Ok(())
}

/// Partial parameter type for the contract function
/// `changeItemStatus/changeItemStatusByAdmin`.
#[derive(Serialize, SchemaType, Debug, PartialEq, Eq)]
pub struct AdditionalData {
    /// Any additional data encoded as generic bytes. Usecase-specific data can
    /// be included here such as temperature, longitude, latitude, ... .
    pub bytes: Vec<u8>,
}

/// The parameter type for the contract function `changeItemStatusByAdmin` which
/// updates the status of an item.
#[derive(Serialize, SchemaType)]
pub struct ChangeItemStatusParamsByAdmin {
    /// The item's id.
    pub item_id:         ItemID,
    /// The item's new status.
    pub new_status:      Status,
    /// Any additional data encoded as generic bytes. Usecase-specific data can
    /// be included here such as temperature, longitude, latitude, ... .
    pub additional_data: AdditionalData,
}

/// Receive function for the ADMIN to change the
/// status of an item. The ADMIN can set the item's status
/// to any value at any time.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Sender is not an authorized role.
/// - The item does not exist in the state.
/// - It fails to log the `ItemStatusChangedEvent`.
#[receive(
    contract = "track_and_trace",
    name = "changeItemStatusByAdmin",
    parameter = "ChangeItemStatusParamsByAdmin",
    error = "CustomContractError",
    mutable,
    enable_logger
)]
fn change_item_status_by_admin(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> Result<(), CustomContractError> {
    // Parse the parameter.
    let param: ChangeItemStatusParamsByAdmin = ctx.parameter_cursor().get()?;

    // Check that only the ADMIN is authorized.
    ensure!(host.state().has_role(&ctx.sender(), Roles::ADMIN), CustomContractError::Unauthorized);

    // The admin can set the item's status to any value at any time.
    host.state_mut().change_item_status(param.item_id, param.new_status)?;

    // Log an ItemStatusChangedEvent.
    logger.log(&Event::ItemStatusChanged(ItemStatusChangedEvent {
        item_id:         param.item_id,
        new_status:      param.new_status,
        additional_data: param.additional_data,
    }))?;

    Ok(())
}

/// The parameter type for the contract function `changeItemStatus` which
/// updates the status of an item.
#[derive(Serialize, SchemaType)]
pub struct ChangeItemStatusParams {
    /// The item's id.
    pub item_id:         ItemID,
    /// Any additional data encoded as generic bytes. Usecase-specific data can
    /// be included here such as temperature, longitude, latitude, ... .
    pub additional_data: AdditionalData,
}

/// Function to update the item's status based on the rules of the state
/// machine.
fn update_state_machine(
    host: &mut Host<State>,
    sender: Address,
    item_id: ItemID,
) -> Result<Status, CustomContractError> {
    // Get the item from the state.
    let mut item =
        host.state_mut().items.entry(item_id).occupied_or(CustomContractError::ItemDoesNotExist)?;

    // Model the state transition based on the rules of the state machine.
    match item.status {
        Status::Produced => {
            item.status = Status::InTransit;
            drop(item);

            // Check that only the correct role is authorized.
            ensure!(
                host.state().has_role(&sender, Roles::PRODUCER),
                CustomContractError::Unauthorized
            );
            Ok(Status::InTransit)
        }
        Status::InTransit => {
            item.status = Status::InStore;
            drop(item);

            // Check that only the correct role is authorized.
            ensure!(
                host.state().has_role(&sender, Roles::TRANSPORTER),
                CustomContractError::Unauthorized
            );
            Ok(Status::InStore)
        }
        Status::InStore => {
            item.status = Status::Sold;
            drop(item);

            // Check that only the correct role is authorized.
            ensure!(
                host.state().has_role(&sender, Roles::SELLER),
                CustomContractError::Unauthorized
            );
            Ok(Status::Sold)
        }
        Status::Sold => bail!(CustomContractError::FinalState),
    }
}

/// Receive function for the other ROLES (all roles except for the ADMIN role)
/// to change the status of an item. The other ROLES can update the item's
/// status based on the rules of the state machine.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Sender is not an authorized role to update the item to the next state.
/// - The item does not exist in the state.
/// - The item is already in the `Sold` state (final state).
/// - It fails to log the `ItemStatusChangedEvent`.
#[receive(
    contract = "track_and_trace",
    name = "changeItemStatus",
    parameter = "ChangeItemStatusParams",
    error = "CustomContractError",
    mutable,
    enable_logger
)]
fn change_item_status(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> Result<(), CustomContractError> {
    // Parse the parameter.
    let param: ChangeItemStatusParams = ctx.parameter_cursor().get()?;

    let new_status = update_state_machine(host, ctx.sender(), param.item_id)?;

    // Log an ItemStatusChangedEvent.
    logger.log(&Event::ItemStatusChanged(ItemStatusChangedEvent {
        item_id: param.item_id,
        new_status,
        additional_data: param.additional_data,
    }))?;

    Ok(())
}

/// The parameter for the contract function `grantRole` which grants a role to
/// an address.
#[derive(Serialize, SchemaType)]
pub struct GrantRoleParams {
    /// The address that has been its role granted.
    pub address: Address,
    /// The role that has been granted to the above address.
    pub role:    Roles,
}

/// Add role to an address.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The sender is not the ADMIN of the contract instance.
/// - The `address` is already holding the specified role to be granted.
#[receive(
    contract = "track_and_trace",
    name = "grantRole",
    parameter = "GrantRoleParams",
    error = "CustomContractError",
    enable_logger,
    mutable
)]
fn contract_grant_role(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let params: GrantRoleParams = ctx.parameter_cursor().get()?;

    let (state, state_builder) = host.state_and_builder();

    // Get the sender who invoked this contract function.
    let sender = ctx.sender();
    // Check that only the ADMIN is authorized to grant roles.
    ensure!(state.has_role(&sender, Roles::ADMIN), CustomContractError::Unauthorized);

    // Check that the `address` had previously not held the specified role.
    ensure!(
        !state.has_role(&params.address, params.role),
        CustomContractError::RoleWasAlreadyGranted
    );

    // Grant role.
    state.grant_role(&params.address, params.role, state_builder);
    // Log a GrantRoleEvent.
    logger.log(&Event::GrantRole(GrantRoleEvent {
        address: params.address,
        role:    params.role,
    }))?;
    Ok(())
}

/// The parameter for the contract function `revokeRole` which revokes a role
/// from an address.
#[derive(Serialize, SchemaType)]
pub struct RevokeRoleParams {
    /// The address that has been its role revoked.
    pub address: Address,
    /// The role that has been revoked from the above address.
    pub role:    Roles,
}

/// Revoke role from an address.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The sender is not the ADMIN of the contract instance.
/// - The `address` does not hold the specified role to be revoked.
#[receive(
    contract = "track_and_trace",
    name = "revokeRole",
    parameter = "RevokeRoleParams",
    error = "CustomContractError",
    enable_logger,
    mutable
)]
fn contract_revoke_role(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let params: RevokeRoleParams = ctx.parameter_cursor().get()?;

    let (state, _) = host.state_and_builder();

    // Get the sender who invoked this contract function.
    let sender = ctx.sender();
    // Check that only the ADMIN is authorized to revoke roles.
    ensure!(state.has_role(&sender, Roles::ADMIN), CustomContractError::Unauthorized);

    // Check that the `address` had previously held the specified role.
    ensure!(state.has_role(&params.address, params.role), CustomContractError::RoleWasNotGranted);

    // Revoke role.
    state.revoke_role(&params.address, params.role);
    // Log a RevokeRoleEvent.
    logger.log(&Event::RevokeRole(RevokeRoleEvent {
        address: params.address,
        role:    params.role,
    }))?;
    Ok(())
}
