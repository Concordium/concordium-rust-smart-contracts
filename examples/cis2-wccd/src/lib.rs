//! Upgradable wCCD smart contract (Concordium's canonical wCCD
//! implementation following the CIS-2 standard)
//!
//! # Description
//! The token in this contract is a wrapped CCD (wCCD), meaning it holds a one
//! to one correspondence with the CCD. This smart contract can be
//! paused/unpaused and upgraded by an admin address.
//! Note: The word 'address' refers to either an account address or a
//! contract address.
//!
//! As follows from the CIS-2 specification, the contract has a `transfer`
//! function for transferring an amount of a specific token type from one
//! address to another address. An address can enable and disable one or more
//! addresses as operators with the `updateOperator` function. An operator of
//! some token owner address is allowed to transfer or unwrap any tokens of the
//! owner.
//!
//! Besides the contract functions required by the CIS-2 standard, this contract
//! implements a function `wrap` for converting CCD into wCCD tokens. It accepts
//! an amount of CCD and mints this amount of wCCD tokens. The function requires
//! a receiving address as an input parameter that receives the minted wCCD
//! tokens.
//!
//! The contract also implements a contract function `unwrap` for converting
//! wCCD back into CCD. The function takes the amount of tokens to unwrap, the
//! address owning these wCCD and a receiver for the CCD. If the sender is the
//! owner or an operator of the owner, the wCCD tokens are burned and the amount
//! of CCD is sent to the receiver.
//!
//! There is a corresponding tutorial for this smart contract available here:
//! https://developer.concordium.software/en/mainnet/smart-contracts/tutorials/wCCD/index.html
//!
//! The admin address can pause/unpause the protocol, set implementors, transfer
//! the admin address to a new address, and update the metadata URL.
#![cfg_attr(not(feature = "std"), no_std)]
use concordium_cis2::{Cis2Event, *};
use concordium_std::*;

/// The id of the wCCD token in this contract.
pub const TOKEN_ID_WCCD: ContractTokenId = TokenIdUnit();

/// Tag for the NewAdmin event.
pub const NEW_ADMIN_EVENT_TAG: u8 = 0;

/// List of supported standards by this contract address.
pub const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 2] =
    [CIS0_STANDARD_IDENTIFIER, CIS2_STANDARD_IDENTIFIER];

/// Sha256 digest
pub type Sha256 = [u8; 32];

// Types

/// Contract token ID type.
/// Since this contract will only ever contain this one token type, we use the
/// smallest possible token ID.
pub type ContractTokenId = TokenIdUnit;

/// Contract token amount type.
/// Since this contract is wrapping the CCD and the CCD can be represented as a
/// u64, we can specialize the token amount to u64 reducing module size and cost
/// of arithmetics.
pub type ContractTokenAmount = TokenAmountU64;

/// The state tracked for each address.
#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
pub struct AddressState<S = StateApi> {
    /// The number of tokens owned by this address.
    pub balance:   ContractTokenAmount,
    /// The address which are currently enabled as operators for this token and
    /// this address.
    pub operators: StateSet<Address, S>,
}

/// The contract state,
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S: HasStateApi = StateApi> {
    /// The admin address can upgrade the contract, pause and unpause the
    /// contract, transfer the admin address to a new address, set
    /// implementors, and update the metadata URL in the contract.
    admin:        Address,
    /// Contract is paused if `paused = true` and unpaused if `paused = false`.
    paused:       bool,
    /// Map specifying the `AddressState` (balance and operators) for every
    /// address.
    token:        StateMap<Address, AddressState<S>, S>,
    /// Map with contract addresses providing implementations of additional
    /// standards.
    implementors: StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
    /// The MetadataUrl of the token.
    /// `StateBox` allows for lazy loading data. This is helpful
    /// in the situations when one wants to do a partial update not touching
    /// this field, which can be large.
    metadata_url: StateBox<MetadataUrl, S>,
}

/// The parameter type for the contract function `unwrap`.
/// Takes an amount of tokens and unwraps the CCD and sends it to a receiver.
#[derive(Serialize, SchemaType)]
pub struct UnwrapParams {
    /// The amount of tokens to unwrap.
    pub amount:   ContractTokenAmount,
    /// The owner of the tokens.
    pub owner:    Address,
    /// The address to receive these unwrapped CCD.
    pub receiver: Receiver,
    /// If the `Receiver` is a contract the unwrapped CCD together with these
    /// additional data bytes are sent to the function entrypoint specified in
    /// the `Receiver`.
    pub data:     AdditionalData,
}

/// The parameter type for the contract function `wrap`.
/// It includes a receiver for receiving the wrapped CCD tokens.
#[derive(Serialize, SchemaType, Debug)]
pub struct WrapParams {
    /// The address to receive these tokens.
    /// If the receiver is the sender of the message wrapping the tokens, it
    /// will not log a transfer event.
    pub to:   Receiver,
    /// Some additional data bytes are used in the `OnReceivingCis2` hook. Only
    /// if the `Receiver` is a contract and the `Receiver` is not
    /// the invoker of the wrap function the receive hook function is
    /// executed. The `OnReceivingCis2` hook invokes the function entrypoint
    /// specified in the `Receiver` with these additional data bytes as
    /// part of the input parameters. This action allows the receiving smart
    /// contract to react to the credited wCCD amount.
    pub data: AdditionalData,
}

/// The parameter type for the contract function `setImplementors`.
/// Takes a standard identifier and list of contract addresses providing
/// implementations of this standard.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct SetImplementorsParams {
    /// The identifier for the standard.
    pub id:           StandardIdentifierOwned,
    /// The addresses of the implementors of the standard.
    pub implementors: Vec<ContractAddress>,
}

/// The parameter type for the contract function `upgrade`.
/// Takes the new module and optionally an entrypoint to call in the new module
/// after triggering the upgrade. The upgrade is reverted if the entrypoint
/// fails. This is useful for doing migration in the same transaction triggering
/// the upgrade.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct UpgradeParams {
    /// The new module reference.
    pub module:  ModuleReference,
    /// Optional entrypoint to call in the new module after upgrade.
    pub migrate: Option<(OwnedEntrypointName, OwnedParameter)>,
}

/// The return type for the contract function `view`.
#[derive(Serialize, SchemaType, PartialEq, Eq, Debug)]
pub struct ReturnBasicState {
    /// The admin address can upgrade the contract, pause and unpause the
    /// contract, transfer the admin address to a new address, set
    /// implementors, and update the metadata URL in the contract.
    pub admin:        Address,
    /// Contract is paused if `paused = true` and unpaused if `paused = false`.
    pub paused:       bool,
    /// The metadata URL of the token.
    pub metadata_url: MetadataUrl,
}

/// The parameter type for the contract function `setMetadataUrl`.
#[derive(Serialize, SchemaType, Clone, PartialEq, Eq, Debug)]
pub struct SetMetadataUrlParams {
    /// The URL following the specification RFC1738.
    pub url:  String,
    /// The hash of the document stored at the above URL.
    pub hash: Option<Sha256>,
}

/// The parameter type for the contract function `setPaused`.
#[derive(Serialize, SchemaType, PartialEq, Eq, Debug)]
#[repr(transparent)]
pub struct SetPausedParams {
    /// Contract is paused if `paused = true` and unpaused if `paused = false`.
    pub paused: bool,
}

/// A NewAdminEvent introduced by this smart contract.
#[derive(Serialize, SchemaType, PartialEq, Eq, Debug)]
#[repr(transparent)]
#[concordium(transparent)]
pub struct NewAdminEvent {
    /// New admin address.
    pub new_admin: Address,
}

/// Tagged events to be serialized for the event log.
#[derive(SchemaType, Serialize, PartialEq, Eq, Debug)]
#[concordium(repr(u8))]
pub enum WccdEvent {
    NewAdmin {
        new_admin: NewAdminEvent,
    },
    #[concordium(forward = cis2_events)]
    Cis2Event(Cis2Event<ContractTokenId, ContractTokenAmount>),
}

/// The different errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
pub enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Failed logging: Log is full.
    LogFull,
    /// Failed logging: Log is malformed.
    LogMalformed,
    /// Contract is paused.
    ContractPaused,
    /// Failed to invoke a contract.
    InvokeContractError,
    /// Failed to invoke a transfer.
    InvokeTransferError,
    /// Upgrade failed because the new module does not exist.
    FailedUpgradeMissingModule,
    /// Upgrade failed because the new module does not contain a contract with a
    /// matching name.
    FailedUpgradeMissingContract,
    /// Upgrade failed because the smart contract version of the module is not
    /// supported.
    FailedUpgradeUnsupportedModuleVersion,
    /// Failed to verify
    FailedToVerifyProof,
}

pub type ContractError = Cis2Error<CustomContractError>;

pub type ContractResult<A> = Result<A, ContractError>;

/// Mapping the logging errors to ContractError.
impl From<LogError> for CustomContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

/// Mapping errors related to contract invocations to CustomContractError.
impl<T> From<CallContractError<T>> for CustomContractError {
    fn from(_cce: CallContractError<T>) -> Self { Self::InvokeContractError }
}

/// Mapping errors related to contract invocations to CustomContractError.
impl From<TransferError> for CustomContractError {
    fn from(_te: TransferError) -> Self { Self::InvokeTransferError }
}

/// Mapping errors related to contract upgrades to CustomContractError.
impl From<UpgradeError> for CustomContractError {
    #[inline(always)]
    fn from(ue: UpgradeError) -> Self {
        match ue {
            UpgradeError::MissingModule => Self::FailedUpgradeMissingModule,
            UpgradeError::MissingContract => Self::FailedUpgradeMissingContract,
            UpgradeError::UnsupportedModuleVersion => Self::FailedUpgradeUnsupportedModuleVersion,
        }
    }
}

/// Mapping CustomContractError to ContractError
impl From<CustomContractError> for ContractError {
    fn from(c: CustomContractError) -> Self { Cis2Error::Custom(c) }
}

impl State {
    /// Creates a new state with no one owning any tokens by default.
    fn new(state_builder: &mut StateBuilder, admin: Address, metadata_url: MetadataUrl) -> Self {
        State {
            admin,
            paused: false,
            token: state_builder.new_map(),
            implementors: state_builder.new_map(),
            metadata_url: state_builder.new_box(metadata_url),
        }
    }

    /// Get the current balance of a given token id for a given address.
    /// Results in an error if the token id does not exist in the state.
    fn balance(
        &self,
        token_id: &ContractTokenId,
        address: &Address,
    ) -> ContractResult<ContractTokenAmount> {
        ensure_eq!(token_id, &TOKEN_ID_WCCD, ContractError::InvalidTokenId);
        Ok(self.token.get(address).map(|s| s.balance).unwrap_or_else(|| 0u64.into()))
    }

    /// Check if an address is an operator of a specific owner address.
    fn is_operator(&self, address: &Address, owner: &Address) -> bool {
        self.token
            .get(owner)
            .map(|address_state| address_state.operators.contains(address))
            .unwrap_or(false)
    }

    /// Update the state with a transfer.
    /// Results in an error if the token id does not exist in the state or if
    /// the from address has insufficient tokens to do the transfer.
    fn transfer(
        &mut self,
        token_id: &ContractTokenId,
        amount: ContractTokenAmount,
        from: &Address,
        to: &Address,
        state_builder: &mut StateBuilder,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID_WCCD, ContractError::InvalidTokenId);
        if amount == 0u64.into() {
            return Ok(());
        }
        {
            let mut from_state =
                self.token.get_mut(from).ok_or(ContractError::InsufficientFunds)?;
            ensure!(from_state.balance >= amount, ContractError::InsufficientFunds);
            from_state.balance -= amount;
        }
        let mut to_state = self.token.entry(*to).or_insert_with(|| AddressState {
            balance:   0u64.into(),
            operators: state_builder.new_set(),
        });
        to_state.balance += amount;

        Ok(())
    }

    /// Update the state adding a new operator for a given token id and address.
    /// Succeeds even if the `operator` is already an operator for this
    /// `token_id` and `address`.
    fn add_operator(
        &mut self,
        owner: &Address,
        operator: &Address,
        state_builder: &mut StateBuilder,
    ) {
        let mut owner_state = self.token.entry(*owner).or_insert_with(|| AddressState {
            balance:   0u64.into(),
            operators: state_builder.new_set(),
        });
        owner_state.operators.insert(*operator);
    }

    /// Update the state removing an operator for a given token id and address.
    /// Succeeds even if the `operator` is not an operator for this `token_id`
    /// and `address`.
    fn remove_operator(&mut self, owner: &Address, operator: &Address) {
        self.token.entry(*owner).and_modify(|address_state| {
            address_state.operators.remove(operator);
        });
    }

    /// Mint an amount of wCCD tokens.
    /// Results in an error if the token id does not exist in the state.
    fn mint(
        &mut self,
        token_id: &ContractTokenId,
        amount: ContractTokenAmount,
        owner: &Address,
        state_builder: &mut StateBuilder,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID_WCCD, ContractError::InvalidTokenId);
        let mut owner_state = self.token.entry(*owner).or_insert_with(|| AddressState {
            balance:   0u64.into(),
            operators: state_builder.new_set(),
        });

        owner_state.balance += amount;
        Ok(())
    }

    /// Burn an amount of wCCD tokens.
    /// Results in an error if the token id does not exist in the state or if
    /// the owner address has insufficient tokens to do the burn.
    fn burn(
        &mut self,
        token_id: &ContractTokenId,
        amount: ContractTokenAmount,
        owner: &Address,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID_WCCD, ContractError::InvalidTokenId);
        if amount == 0u64.into() {
            return Ok(());
        }

        let mut from_state = self.token.get_mut(owner).ok_or(ContractError::InsufficientFunds)?;
        ensure!(from_state.balance >= amount, ContractError::InsufficientFunds);
        from_state.balance -= amount;

        Ok(())
    }

    /// Check if state contains any implementors for a given standard.
    fn have_implementors(&self, std_id: &StandardIdentifierOwned) -> SupportResult {
        if let Some(addresses) = self.implementors.get(std_id) {
            SupportResult::SupportBy(addresses.to_vec())
        } else {
            SupportResult::NoSupport
        }
    }

    /// Set implementors for a given standard.
    fn set_implementors(
        &mut self,
        std_id: StandardIdentifierOwned,
        implementors: Vec<ContractAddress>,
    ) {
        let _ = self.implementors.insert(std_id, implementors);
    }
}

// Contract functions

/// Initialize contract instance with no initial tokens.
/// Logs a `Mint` event for the single token id with no amounts.
/// Logs a `TokenMetadata` event with the metadata url and hash.
/// Logs a `NewAdmin` event with the invoker as admin.
#[init(
    contract = "cis2_wCCD",
    enable_logger,
    parameter = "SetMetadataUrlParams",
    event = "WccdEvent"
)]
fn contract_init(
    ctx: &InitContext,
    state_builder: &mut StateBuilder,
    logger: &mut impl HasLogger,
) -> InitResult<State> {
    // Parse the parameter.
    let params: SetMetadataUrlParams = ctx.parameter_cursor().get()?;
    // Get the instantiator of this contract instance to be used as the initial
    // admin.
    let invoker = Address::Account(ctx.init_origin());

    // Create the metadata_url
    let metadata_url = MetadataUrl {
        url:  params.url.clone(),
        hash: params.hash,
    };

    // Construct the initial contract state.
    let state = State::new(state_builder, invoker, metadata_url.clone());
    // Log event for the newly minted token.
    logger.log(&WccdEvent::Cis2Event(Cis2Event::Mint(MintEvent {
        token_id: TOKEN_ID_WCCD,
        amount:   ContractTokenAmount::from(0u64),
        owner:    invoker,
    })))?;

    // Log event for where to find metadata for the token
    logger.log(&WccdEvent::Cis2Event(Cis2Event::TokenMetadata::<_, ContractTokenAmount>(
        TokenMetadataEvent {
            token_id: TOKEN_ID_WCCD,
            metadata_url,
        },
    )))?;

    // Log event for the new admin.
    logger.log(&WccdEvent::NewAdmin {
        new_admin: NewAdminEvent {
            new_admin: invoker,
        },
    })?;

    Ok(state)
}

/// Wrap an amount of CCD into wCCD tokens and transfer the tokens if the sender
/// is not the receiver.
#[receive(
    contract = "cis2_wCCD",
    name = "wrap",
    parameter = "WrapParams",
    error = "ContractError",
    enable_logger,
    mutable,
    payable
)]
fn contract_wrap(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    amount: Amount,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Check that contract is not paused.
    ensure!(!host.state().paused, ContractError::Custom(CustomContractError::ContractPaused));

    // Parse the parameter.
    let params: WrapParams = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    let receive_address = params.to.address();

    let (state, state_builder) = host.state_and_builder();
    // Update the state.
    state.mint(&TOKEN_ID_WCCD, amount.micro_ccd.into(), &receive_address, state_builder)?;

    // Log the newly minted tokens.
    logger.log(&WccdEvent::Cis2Event(Cis2Event::Mint(MintEvent {
        token_id: TOKEN_ID_WCCD,
        amount:   ContractTokenAmount::from(amount.micro_ccd),
        owner:    sender,
    })))?;

    // Only logs a transfer event if the receiver is not the sender.
    // Only executes the `OnReceivingCis2` hook if the receiver is not the sender
    // and the receiver is a contract.
    if sender != receive_address {
        logger.log(&WccdEvent::Cis2Event(Cis2Event::Transfer(TransferEvent {
            token_id: TOKEN_ID_WCCD,
            amount:   ContractTokenAmount::from(amount.micro_ccd),
            from:     sender,
            to:       receive_address,
        })))?;

        // If the receiver is a contract: invoke the receive hook function.
        if let Receiver::Contract(address, function) = params.to {
            let parameter = OnReceivingCis2Params {
                token_id: TOKEN_ID_WCCD,
                amount:   ContractTokenAmount::from(amount.micro_ccd),
                from:     sender,
                data:     params.data,
            };
            host.invoke_contract(
                &address,
                &parameter,
                function.as_entrypoint_name(),
                Amount::zero(),
            )?;
        }
    }
    Ok(())
}

/// Unwrap an amount of wCCD tokens into CCD
#[receive(
    contract = "cis2_wCCD",
    name = "unwrap",
    parameter = "UnwrapParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_unwrap(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Check that contract is not paused.
    ensure!(!host.state().paused, ContractError::Custom(CustomContractError::ContractPaused));

    // Parse the parameter.
    let params: UnwrapParams = ctx.parameter_cursor().get()?;

    // Get the sender who invoked this contract function.
    let sender = ctx.sender();
    let state = host.state_mut();

    // Authenticate the sender
    ensure!(
        sender == params.owner || state.is_operator(&sender, &params.owner),
        ContractError::Unauthorized
    );

    // Update the state.
    state.burn(&TOKEN_ID_WCCD, params.amount, &params.owner)?;

    // Log the burning of tokens.
    logger.log(&WccdEvent::Cis2Event(Cis2Event::Burn(BurnEvent {
        token_id: TOKEN_ID_WCCD,
        amount:   params.amount,
        owner:    params.owner,
    })))?;

    let unwrapped_amount = Amount::from_micro_ccd(params.amount.into());

    // Transfer the CCD to the receiver
    match params.receiver {
        Receiver::Account(address) => {
            // verify presentation.
            let Some(request) = host.verify_presentation(params.data.as_ref()) else {
                return Err(CustomContractError::FailedToVerifyProof.into())
            };
            let allowed = request.statements.into_iter().any(|s| {
                if s.address != address {
                    return false;
                }
                s.atomics.into_iter().any(|atomic| match atomic {
                    AtomicStatement::InRange {
                        ..
                    } => false,
                    AtomicStatement::InSet {
                        tag,
                        set,
                    } => {
                        tag == attributes::NATIONALITY.0
                            && set.into_iter().all(|s| s != "NO")
                    }
                })
            });
            if allowed {
                host.invoke_transfer(&address, unwrapped_amount)?
            } else {
                return Err(CustomContractError::FailedToVerifyProof.into());
            }
        }
        Receiver::Contract(address, function) => {
            host.invoke_contract(
                &address,
                &params.data,
                function.as_entrypoint_name(),
                unwrapped_amount,
            )?;
        }
    }

    Ok(())
}

/// Transfer the admin address to a new admin address.
///
/// It rejects if:
/// - Sender is not the current admin of the contract instance.
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_wCCD",
    name = "updateAdmin",
    parameter = "Address",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_update_admin(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Check that only the current admin is authorized to update the admin address.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    // Parse the parameter.
    let new_admin = ctx.parameter_cursor().get()?;

    // Update the admin variable.
    host.state_mut().admin = new_admin;

    // Log a new admin event.
    logger.log(&WccdEvent::NewAdmin {
        new_admin: NewAdminEvent {
            new_admin,
        },
    })?;

    Ok(())
}

/// Pause/Unpause this smart contract instance by the admin. All non-admin
/// state-mutative functions (wrap, unwrap, transfer, updateOperator) cannot be
/// executed when the contract is paused.
///
/// It rejects if:
/// - Sender is not the admin of the contract instance.
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_wCCD",
    name = "setPaused",
    parameter = "SetPausedParams",
    error = "ContractError",
    mutable
)]
fn contract_set_paused(ctx: &ReceiveContext, host: &mut Host<State>) -> ContractResult<()> {
    // Check that only the admin is authorized to pause/unpause the contract.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    // Parse the parameter.
    let params: SetPausedParams = ctx.parameter_cursor().get()?;

    // Update the paused variable.
    host.state_mut().paused = params.paused;

    Ok(())
}

/// Update the metadata URL in this smart contract instance.
///
/// It rejects if:
/// - Sender is not the admin of the contract instance.
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_wCCD",
    name = "setMetadataUrl",
    parameter = "SetMetadataUrlParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_state_set_metadata_url(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Check that only the admin is authorized to update the URL.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    // Parse the parameter.
    let params: SetMetadataUrlParams = ctx.parameter_cursor().get()?;

    // Create the metadata_url
    let metadata_url = MetadataUrl {
        url:  params.url.clone(),
        hash: params.hash,
    };

    // Update the hash variable.
    *host.state_mut().metadata_url = metadata_url.clone();

    // Log an event including the new metadata for this token.
    logger.log(&WccdEvent::Cis2Event(Cis2Event::TokenMetadata::<_, ContractTokenAmount>(
        TokenMetadataEvent {
            token_id: TOKEN_ID_WCCD,
            metadata_url,
        },
    )))?;

    Ok(())
}

// Contract functions required by the CIS-2 standard

type TransferParameter = TransferParams<ContractTokenId, ContractTokenAmount>;

/// Execute a list of token transfers, in the order of the list.
///
/// Logs a `Transfer` event and invokes a receive hook function for every
/// transfer in the list.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the transfers fail to be executed, which could be if:
///     - The `token_id` does not exist.
///     - The sender is not the owner of the token, or an operator for this
///       specific `token_id` and `from` address.
///     - The token is not owned by the `from`.
/// - Fails to log event.
/// - Any of the receive hook function calls rejects.
#[receive(
    contract = "cis2_wCCD",
    name = "transfer",
    parameter = "TransferParameter",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_transfer(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Check that contract is not paused.
    ensure!(!host.state().paused, ContractError::Custom(CustomContractError::ContractPaused));

    // Parse the parameter.
    let TransferParams(transfers): TransferParameter = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    for Transfer {
        token_id,
        amount,
        from,
        to,
        data,
    } in transfers
    {
        let (state, builder) = host.state_and_builder();
        // Authenticate the sender for this transfer
        ensure!(from == sender || state.is_operator(&sender, &from), ContractError::Unauthorized);
        let to_address = to.address();
        // Update the contract state
        state.transfer(&token_id, amount, &from, &to_address, builder)?;

        // Log transfer event
        logger.log(&WccdEvent::Cis2Event(Cis2Event::Transfer(TransferEvent {
            token_id,
            amount,
            from,
            to: to_address,
        })))?;

        // If the receiver is a contract: invoke the receive hook function.
        if let Receiver::Contract(address, function) = to {
            let parameter = OnReceivingCis2Params {
                token_id,
                amount,
                from,
                data,
            };
            host.invoke_contract(
                &address,
                &parameter,
                function.as_entrypoint_name(),
                Amount::zero(),
            )?;
        }
    }
    Ok(())
}

/// Enable or disable addresses as operators of the sender address.
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Fails to log event.
#[receive(
    contract = "cis2_wCCD",
    name = "updateOperator",
    parameter = "UpdateOperatorParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_update_operator(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Check that contract is not paused.
    ensure!(!host.state().paused, ContractError::Custom(CustomContractError::ContractPaused));

    // Parse the parameter.
    let UpdateOperatorParams(params) = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    let (state, state_builder) = host.state_and_builder();
    for param in params {
        // Update the operator in the state.
        match param.update {
            OperatorUpdate::Add => state.add_operator(&sender, &param.operator, state_builder),
            OperatorUpdate::Remove => state.remove_operator(&sender, &param.operator),
        }

        // Log the appropriate event
        logger.log(&WccdEvent::Cis2Event(
            Cis2Event::<ContractTokenId, ContractTokenAmount>::UpdateOperator(
                UpdateOperatorEvent {
                    owner:    sender,
                    operator: param.operator,
                    update:   param.update,
                },
            ),
        ))?;
    }

    Ok(())
}

/// Parameter type for the CIS-2 function `balanceOf` specialized to the subset
/// of TokenIDs used by this contract.
pub type ContractBalanceOfQueryParams = BalanceOfQueryParams<ContractTokenId>;

pub type ContractBalanceOfQueryResponse = BalanceOfQueryResponse<ContractTokenAmount>;

/// Get the balance of given token IDs and addresses.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "cis2_wCCD",
    name = "balanceOf",
    parameter = "ContractBalanceOfQueryParams",
    return_value = "ContractBalanceOfQueryResponse",
    error = "ContractError"
)]
fn contract_balance_of(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<ContractBalanceOfQueryResponse> {
    // Parse the parameter.
    let params: ContractBalanceOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for balance.
        let amount = host.state().balance(&query.token_id, &query.address)?;
        response.push(amount);
    }
    let result = ContractBalanceOfQueryResponse::from(response);
    Ok(result)
}

/// Takes a list of queries. Each query contains an owner address and some
/// address that will be checked if it is an operator to the owner address.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_wCCD",
    name = "operatorOf",
    parameter = "OperatorOfQueryParams",
    return_value = "OperatorOfQueryResponse",
    error = "ContractError"
)]
fn contract_operator_of(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<OperatorOfQueryResponse> {
    // Parse the parameter.
    let params: OperatorOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state if the `address` being an `operator` of `owner`.
        let is_operator = host.state().is_operator(&query.address, &query.owner);
        response.push(is_operator);
    }
    let result = OperatorOfQueryResponse::from(response);
    Ok(result)
}

/// Parameter type for the CIS-2 function `tokenMetadata` specialized to the
/// subset of TokenIDs used by this contract.
// This type is pub to silence the dead_code warning, as this type is only used
// for when generating the schema.
pub type ContractTokenMetadataQueryParams = TokenMetadataQueryParams<ContractTokenId>;

/// Get the token metadata URLs and checksums given a list of token IDs.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "cis2_wCCD",
    name = "tokenMetadata",
    parameter = "ContractTokenMetadataQueryParams",
    return_value = "TokenMetadataQueryResponse",
    error = "ContractError"
)]
fn contract_token_metadata(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<TokenMetadataQueryResponse> {
    // Parse the parameter.
    let params: ContractTokenMetadataQueryParams = ctx.parameter_cursor().get()?;

    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for token_id in params.queries {
        // Check the token exists.
        ensure_eq!(token_id, TOKEN_ID_WCCD, ContractError::InvalidTokenId);

        response.push(host.state().metadata_url.clone());
    }
    let result = TokenMetadataQueryResponse::from(response);
    Ok(result)
}

/// Function to view the basic state of the contract.
#[receive(
    contract = "cis2_wCCD",
    name = "view",
    return_value = "ReturnBasicState",
    error = "ContractError"
)]
fn contract_view(_ctx: &ReceiveContext, host: &Host<State>) -> ContractResult<ReturnBasicState> {
    let state = ReturnBasicState {
        admin:        host.state().admin,
        paused:       host.state().paused,
        metadata_url: host.state().metadata_url.clone(),
    };
    Ok(state)
}

/// Get the supported standards or addresses for a implementation given list of
/// standard identifiers.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_wCCD",
    name = "supports",
    parameter = "SupportsQueryParams",
    return_value = "SupportsQueryResponse",
    error = "ContractError"
)]
fn contract_supports(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<SupportsQueryResponse> {
    // Parse the parameter.
    let params: SupportsQueryParams = ctx.parameter_cursor().get()?;

    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for std_id in params.queries {
        if SUPPORTS_STANDARDS.contains(&std_id.as_standard_identifier()) {
            response.push(SupportResult::Support);
        } else {
            response.push(host.state().have_implementors(&std_id));
        }
    }
    let result = SupportsQueryResponse::from(response);
    Ok(result)
}

/// Set the addresses for an implementation given a standard identifier and a
/// list of contract addresses.
///
/// It rejects if:
/// - Sender is not the admin of the contract instance.
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_wCCD",
    name = "setImplementors",
    parameter = "SetImplementorsParams",
    error = "ContractError",
    mutable
)]
fn contract_set_implementor(ctx: &ReceiveContext, host: &mut Host<State>) -> ContractResult<()> {
    // Check that only the admin is authorized to set implementors.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);
    // Parse the parameter.
    let params: SetImplementorsParams = ctx.parameter_cursor().get()?;
    // Update the implementors in the state
    host.state_mut().set_implementors(params.id, params.implementors);
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
    contract = "cis2_wCCD",
    name = "upgrade",
    parameter = "UpgradeParams",
    error = "ContractError",
    low_level
)]
fn contract_upgrade<S: HasStateApi>(
    ctx: &ReceiveContext,
    host: &mut impl HasHost<S>,
) -> ContractResult<()> {
    // Read the top-level contract state.
    let state: State<S> = host.state().read_root()?;

    // Check that only the admin is authorized to upgrade the smart contract.
    ensure_eq!(ctx.sender(), state.admin, ContractError::Unauthorized);
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
