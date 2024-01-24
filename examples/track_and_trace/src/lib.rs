//! # Implementation of an auction smart contract
//!
//! Accounts can invoke the bid function to participate in the auction.
//! An account has to send some CCD when invoking the bid function.
//! This CCD amount has to exceed the current highest bid by a minimum raise
//! to be accepted by the smart contract.
//!
//! The minimum raise is set when initializing and is defined in Euro cent.
//! The contract uses the current exchange rate used by the chain by the time of
//! the bid, to convert the bid into EUR.
//!
//! The smart contract keeps track of the current highest bidder as well as
//! the CCD amount of the highest bid. The CCD balance of the smart contract
//! represents the highest bid. When a new highest bid is accepted by the smart
//! contract, the smart contract refunds the old highest bidder.
//!
//! Bids have to be placed before the auction ends. The participant with the
//! highest bid (the last bidder) wins the auction.
//!
//! After the auction ends, any account can finalize the auction. The owner of
//! the smart contract instance receives the highest bid (the balance of this
//! contract) when the auction is finalized. This can be done only once.
//!
//! Terminology: `Accounts` are derived from a public/private key pair.
//! `Contract` instances are created by deploying a smart contract
//! module and initializing it.

#![cfg_attr(not(feature = "std"), no_std)]

use concordium_cis2::*;
use concordium_std::{collections::BTreeMap, *};

/// Event tags.
pub const ITEM_CREATED_EVENT_TAG: u8 = 0;
pub const ITEM_STATUS_CHANGED_EVENT_TAG: u8 = 1;
pub const GRANT_ROLE_EVENT_TAG: u8 = 2;
pub const REVOKE_ROLE_EVENT_TAG: u8 = 3;

//Tagged events to be serialized for the event log.
#[derive(Debug, Serial, Deserial, PartialEq, Eq)]
pub enum Event {
    /// The event tracks when a role is revoked from an address.
    ItemCreated(ItemCreatedEvent),
    /// The event tracks when a role is revoked from an address.
    ItemStatusChanged(ItemStatusChangedEvent),
    /// The event tracks when a new role is granted to an address.
    GrantRole(GrantRoleEvent),
    /// The event tracks when a role is revoked from an address.
    RevokeRole(RevokeRoleEvent),
}

/// The ItemCreatedEvent is logged when a new role is granted to an address.
#[derive(Serialize, SchemaType, Debug, PartialEq, Eq)]
pub struct ItemCreatedEvent {
    /// The address that has been its role granted.
    pub item_id:      u64,
    /// The role that was granted to the above address.
    pub metadata_url: Option<MetadataUrl>,
}

/// The ItemStatusChangedEvent is logged when a new role is granted to an
/// address.
#[derive(Serialize, SchemaType, Debug, PartialEq, Eq)]
pub struct AdditionalData {
    /// The address that has been its role granted.
    pub bytes: Vec<u8>,
}

/// The ItemStatusChangedEvent is logged when a new role is granted to an
/// address.
#[derive(Serialize, SchemaType, Debug, PartialEq, Eq)]
pub struct ItemStatusChangedEvent {
    /// The address that has been its role granted.
    pub item_id:         u64,
    // The role that was granted to the above address.
    pub new_status:      Status,
    ///
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

/// The parameter for the contract function `grantRole` which grants a role to
/// an address.
#[derive(Serialize, SchemaType)]
pub struct GrantRoleParams {
    /// The address that has been its role granted.
    pub address: Address,
    /// The role that has been granted to the above address.
    pub role:    Roles,
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

/// A struct containing a set of roles granted to an address.
#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
struct AddressRoleState<S> {
    /// Set of roles.
    roles: StateSet<Roles, S>,
}

/// Enum of available roles in this contract.
#[derive(Serialize, PartialEq, Eq, Reject, SchemaType, Clone, Copy, Debug)]
pub enum Roles {
    /// Admin role.
    ADMIN,
    /// Upgrader role.
    PRODUCER,
    /// Blacklister role.
    TRANSPORTER,
    /// Pauser role.
    SELLER,
}

/// Enum of available roles in this contract.
#[derive(Serialize, PartialEq, Eq, Reject, SchemaType, Clone, Copy, Debug)]
pub enum Status {
    Produced,
    InTransit,
    InStore,
    Sold,
}

// Implementing a custom schemaType for the `Event` struct containing all
// CIS2/CIS3 events. This custom implementation flattens the fields to avoid one
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
                    (String::from("itemId"), u64::get_type()),
                    (String::from("metadataURL"), Option::<MetadataUrl>::get_type()),
                ]),
            ),
        );
        event_map.insert(
            ITEM_STATUS_CHANGED_EVENT_TAG,
            (
                "ItemStatusChanged".to_string(),
                schema::Fields::Named(vec![
                    (String::from("itemId"), u64::get_type()),
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

/// A struct containing a set of roles granted to an address.
#[derive(Debug, Serialize, SchemaType, Clone, PartialEq, Eq)]
pub struct ItemState {
    /// Set of roles.
    pub status:       Status,
    pub metadata_url: Option<MetadataUrl>,
}

/// The state of the smart contract.
/// This state can be viewed by querying the node with the command
/// `concordium-client contract invoke` using the `view` function as entrypoint.
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S = StateApi> {
    /// The minimum accepted raise to over bid the current bidder in Euro cent.
    next_item_id: u64,
    /// A map containing all roles granted to addresses.
    roles:        StateMap<Address, AddressRoleState<S>, S>,
    /// A map containing all roles granted to addresses.
    items:        StateMap<u64, ItemState, S>,
}

/// The different errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
pub enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams, // -1
    /// Failed logging: Log is full.
    LogFull, // -2
    /// Failed logging: Log is malformed.
    LogMalformed, // -3
    ///
    Unauthorized, // -4
    RoleWasAlreadyGranted,
    RoleWasNotGranted,
    ItemAlreadyExists,
    ItemNotExists,
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

    /// Check if an address has an role.
    fn has_role(&self, account: &Address, role: Roles) -> bool {
        return match self.roles.get(account) {
            None => false,
            Some(roles) => roles.roles.contains(&role),
        };
    }

    /// Check if an address has an role.
    fn to_state_produced(&mut self, item_index: u64) {
        self.items.entry(item_index).and_modify(|x| x.status = Status::Sold);
    }

    /// Check if an address has an role.
    fn to_state_in_transit(&mut self, item_index: u64) {
        self.items.entry(item_index).and_modify(|x| x.status = Status::InTransit);
    }

    /// Check if an address has an role.
    fn to_state_in_store(&mut self, item_index: u64) {
        self.items.entry(item_index).and_modify(|x| x.status = Status::InStore);
    }

    /// Check if an address has an role.
    fn to_state_sold(&mut self, item_index: u64) {
        self.items.entry(item_index).and_modify(|x| x.status = Status::Sold);
    }
}
/// Init function that creates a new auction
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

#[derive(Serialize, SchemaType, PartialEq, Eq, Debug)]
pub struct ViewState {
    pub next_item_id: u64,
    pub items:        Vec<(u64, ItemState)>,
    pub roles:        Vec<(Address, Vec<Roles>)>,
}

/// View function for testing. This reports on the entire state of the contract
/// for testing purposes.
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

    let items: Vec<(u64, ItemState)> =
        state.items.iter().map(|(key, value)| (*key, (*value).clone())).collect();

    Ok(ViewState {
        roles,
        items,
        next_item_id: host.state().next_item_id,
    })
}

/// Receive function for accounts to place a bid in the auction
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
    let metadata_url: Option<MetadataUrl> = ctx.parameter_cursor().get()?;

    // Check that only the ADMIN is authorized to create new item.
    ensure!(host.state().has_role(&ctx.sender(), Roles::ADMIN), CustomContractError::Unauthorized);

    let next_item_id = host.state().next_item_id;

    host.state_mut().next_item_id += 1;
    let previous_item = host.state_mut().items.insert(next_item_id, ItemState {
        metadata_url: metadata_url.clone(),
        status:       Status::Produced,
    });

    ensure_eq!(previous_item, None, CustomContractError::ItemAlreadyExists);

    logger.log(&Event::ItemCreated(ItemCreatedEvent {
        item_id: next_item_id,
        metadata_url,
    }))?;

    Ok(())
}

/// The parameter for the contract function `revokeRole` which revokes a role
/// from an address.
#[derive(Serialize, SchemaType)]
pub struct ChangeItemStatusParams {
    /// The address that has been its role revoked.
    pub item_id:         u64,
    pub new_status:      Status,
    pub additional_data: AdditionalData,
}

/// Receive function for accounts to place a bid in the auction
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
    let param: ChangeItemStatusParams = ctx.parameter_cursor().get()?;

    // TODO other roles can also update
    // Check that only the ADMIN is authorized to create new item.
    ensure!(host.state().has_role(&ctx.sender(), Roles::ADMIN), CustomContractError::Unauthorized);

    match param.new_status {
        Status::Produced => host.state_mut().to_state_produced(param.item_id),
        Status::InTransit => host.state_mut().to_state_in_transit(param.item_id),
        Status::InStore => host.state_mut().to_state_in_store(param.item_id),
        Status::Sold => host.state_mut().to_state_sold(param.item_id),
    };

    logger.log(&Event::ItemStatusChanged(ItemStatusChangedEvent {
        item_id:         param.item_id,
        new_status:      param.new_status,
        additional_data: param.additional_data,
    }))?;

    Ok(())
}

/// Add role to an address.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Sender is not the ADMIN of the contract instance.
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

    // Check that the `address` had previously not hold the specified role.
    ensure!(
        !state.has_role(&params.address, params.role),
        CustomContractError::RoleWasAlreadyGranted
    );

    // Grant role.
    state.grant_role(&params.address, params.role, state_builder);
    logger.log(&Event::GrantRole(GrantRoleEvent {
        address: params.address,
        role:    params.role,
    }))?;
    Ok(())
}

/// Revoke role from an address.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Sender is not the ADMIN of the contract instance.
/// - The `address` is not holding the specified role to be revoked.
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

    // Check that the `address` had previously hold the specified role.
    ensure!(state.has_role(&params.address, params.role), CustomContractError::RoleWasNotGranted);

    // Revoke role.
    state.revoke_role(&params.address, params.role);
    logger.log(&Event::RevokeRole(RevokeRoleEvent {
        address: params.address,
        role:    params.role,
    }))?;
    Ok(())
}
