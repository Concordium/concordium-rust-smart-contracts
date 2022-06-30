//! upgradable wCCD token

#![cfg_attr(not(feature = "std"), no_std)]
use crate::CustomContractError::{
    AlreadyInitialized, ContractPaused, OnlyImplementation, OnlyState, OutOfBound, StateInvokeError,
};
use concordium_cis2::*;
use concordium_std::*;
use core::fmt::Debug;

/// The id of the wCCD token in this contract.
const TOKEN_ID_WCCD: ContractTokenId = TokenIdUnit();

/// The metadata url for the wCCD token.
const TOKEN_METADATA_URL: &str = "https://some.example/token/wccd";

// Types

/// Contract token ID type.
/// Since this contract will only ever contain this one token type, we use the
/// smallest possible token ID.
type ContractTokenId = TokenIdUnit;

/// Contract token amount type.
/// Since this contract is wrapping the CCD and the CCD can be represented as a
/// u64, we can specialize the token amount to u64 reducing module size and cost
/// of arithmetics.
type ContractTokenAmount = TokenAmountU64;

/// The state tracked for each address.
#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
struct AddressState<S> {
    /// The number of tokens owned by this address.
    balance:   ContractTokenAmount,
    /// The address which are currently enabled as operators for this token and
    /// this address.
    operators: StateSet<Address, S>,
}

/// The contract state.
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S> {
    /// Address of the w_ccd proxy contract.
    proxy_address:          Option<ContractAddress>,
    /// Address of the w_ccd implementation contract.
    implementation_address: Option<ContractAddress>,
    /// FALSE if proxy and implementation addresses have not been set yet.
    /// TRUE if proxy and implementation addresses have been set.
    initialized:            bool,
    /// The state of the one token.
    token:                  StateMap<Address, AddressState<S>, S>,
    /// Timestamp when contract is unpaused.
    unpause_time:           Timestamp,
}

/// The implementation contract state.
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct StateImplementation<S> {
    /// The admin address can pause/unpause the contract.
    admin:         Address,
    /// Address of the w_ccd proxy contract.
    proxy_address: Option<ContractAddress>,
    /// Address of the w_ccd state contract.
    state_address: Option<ContractAddress>,
    /// FALSE if proxy and state addresses have not been set yet.
    /// TRUE if proxy and state addresses have been set.
    initialized:   bool,

    /// TODO: These state variables will be removed out of this
    /// `StateImplementation` struct once the getter/setter functions are
    /// set up between the State contract and the Implementation contract.
    /// The state of the one token.
    token:        StateMap<Address, AddressState<S>, S>,
    /// Timestamp when contract is unpaused.
    unpause_time: Timestamp,
}

/// The parameter type for the contract function `unwrap`.
/// Takes an amount of tokens and unwrap the CCD and send it to a receiver.
#[derive(Serialize, SchemaType)]
struct UnwrapParams {
    /// The amount of tokens to unwrap.
    amount:   ContractTokenAmount,
    /// The owner of the tokens.
    owner:    Address,
    /// The address to receive these unwrapped CCD.
    receiver: Receiver,
    /// Some additional bytes to include in the transfer.
    data:     AdditionalData,
}

/// The parameter type for the contract function `wrap`.
///
/// The receiver for the wrapped CCD tokens.
#[derive(Serialize, SchemaType)]
struct WrapParams {
    /// The address to receive these tokens.
    /// If the receiver is the sender of the message wrapping the tokens, it
    /// will not log a transfer.
    to:   Receiver,
    /// Some additional bytes to include in a transfer.
    data: AdditionalData,
}

/// The parameter type for the state contract function `initialize`.
#[derive(Serialize, SchemaType)]
struct InitializeStateParams {
    /// Address of the w_ccd proxy contract.
    proxy_address:          Option<ContractAddress>,
    /// Address of the w_ccd implementation contract.
    implementation_address: Option<ContractAddress>,
}

/// The parameter type for the implementation contract function `initialize`.
#[derive(Serialize, SchemaType)]
struct InitializeImplementationParams {
    /// Address of the w_ccd proxy contract.
    proxy_address: Option<ContractAddress>,
    /// Address of the w_ccd state contract.
    state_address: Option<ContractAddress>,
}

/// The different errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject)]
enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Failed logging: Log is full.
    LogFull,
    /// Failed logging: Log is malformed.
    LogMalformed,
    /// Failed to invoke a contract.
    InvokeContractError,
    /// Failed to invoke a transfer.
    InvokeTransferError,
    /// Value out of bound.
    OutOfBound,
    /// Contract is paused.
    ContractPaused,
    // Contract already initialized.
    AlreadyInitialized,
    // Only implementation contract.
    OnlyImplementation,
    // Only proxy contract.
    OnlyProxy,
    // Only state contract.
    OnlyState,
    // Raised when implementation can not invoke state contract.
    StateInvokeError,
}

type ContractError = Cis2Error<CustomContractError>;

type ContractResult<A> = Result<A, ContractError>;

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

/// Mapping CustomContractError to ContractError
impl From<CustomContractError> for ContractError {
    fn from(c: CustomContractError) -> Self { Cis2Error::Custom(c) }
}

impl<S: HasStateApi> State<S> {
    /// Creates a new state with no one owning any tokens by default.
    fn new(state_builder: &mut StateBuilder<S>) -> Self {
        // Setup state.
        State {
            proxy_address:          None,
            implementation_address: None,
            initialized:            false,
            token:                  state_builder.new_map(),
            unpause_time:           Timestamp::from_timestamp_millis(0),
        }
    }

    /// TODO: This function should be removed in the end. It is still here
    /// because the tests are not re-written to work without this mint function
    /// when setting up the state.
    fn mint(
        &mut self,
        token_id: &ContractTokenId,
        amount: ContractTokenAmount,
        owner: &Address,
        state_builder: &mut StateBuilder<S>,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID_WCCD, ContractError::InvalidTokenId);
        let mut owner_state = self.token.entry(*owner).or_insert_with(|| AddressState {
            balance:   0u64.into(),
            operators: state_builder.new_set(),
        });

        owner_state.balance += amount;
        Ok(())
    }
}

impl<S: HasStateApi> StateImplementation<S> {
    /// Creates a new state with no one owning any tokens by default.
    fn new(admin: Address, state_builder: &mut StateBuilder<S>) -> Self {
        // Setup state.
        StateImplementation {
            admin,
            proxy_address: None,
            state_address: None,
            initialized: false,
            token: state_builder.new_map(), // TODO: This variable will be moved 'state' contract.
            unpause_time: Timestamp::from_timestamp_millis(0), /* TODO: This variable will be
                                                                * moved 'state' contract. */
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

    /// Check is an address is an operator of a specific owner address.
    /// Results in an error if the token id does not exist in the state.
    fn is_operator(&self, address: &Address, owner: &Address) -> bool {
        self.token
            .get(owner)
            .map(|address_state| address_state.operators.contains(address))
            .unwrap_or(false)
    }

    /// Update the state with a transfer.
    /// Results in an error if the token id does not exist in the state or if
    /// the from address have insufficient tokens to do the transfer.
    fn transfer(
        &mut self,
        token_id: &ContractTokenId,
        amount: ContractTokenAmount,
        from: &Address,
        to: &Address,
        state_builder: &mut StateBuilder<S>,
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
    /// Results in an error if the token id does not exist in the state.
    /// Succeeds even if the `operator` is already an operator for this
    /// `token_id` and `address`.
    fn add_operator(
        &mut self,
        owner: &Address,
        operator: &Address,
        state_builder: &mut StateBuilder<S>,
    ) -> ContractResult<()> {
        let mut owner_state = self.token.entry(*owner).or_insert_with(|| AddressState {
            balance:   0u64.into(),
            operators: state_builder.new_set(),
        });
        owner_state.operators.insert(*operator);
        Ok(())
    }

    /// Update the state removing an operator for a given token id and address.
    /// Results in an error if the token id does not exist in the state.
    /// Succeeds even if the `operator` is not an operator for this `token_id`
    /// and `address`.
    fn remove_operator(&mut self, owner: &Address, operator: &Address) -> ContractResult<()> {
        self.token.entry(*owner).and_modify(|address_state| {
            address_state.operators.remove(operator);
        });
        Ok(())
    }

    fn mint(
        &mut self,
        token_id: &ContractTokenId,
        amount: ContractTokenAmount,
        owner: &Address,
        state_builder: &mut StateBuilder<S>,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID_WCCD, ContractError::InvalidTokenId);
        let mut owner_state = self.token.entry(*owner).or_insert_with(|| AddressState {
            balance:   0u64.into(),
            operators: state_builder.new_set(),
        });

        owner_state.balance += amount;
        Ok(())
    }

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
}

// Contract functions

/// Initialize the state contract instance with no initial tokens.
/// Logs a `Mint` event for the single token id with no amounts.
/// TODO: move event logs to proxy
#[init(contract = "CIS2-wCCD-State", enable_logger)]
fn contract_state_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
    logger: &mut impl HasLogger,
) -> InitResult<State<S>> {
    // Construct the initial contract state.
    let state = State::new(state_builder);
    // Get the instantiater of this contract instance.
    let invoker = Address::Account(ctx.init_origin());
    // Log event for the newly minted token.
    logger.log(&Cis2Event::Mint(MintEvent {
        token_id: TOKEN_ID_WCCD,
        amount:   ContractTokenAmount::from(0u64),
        owner:    invoker,
    }))?;

    // Log event for where to find metadata for the token
    logger.log(&Cis2Event::TokenMetadata::<_, ContractTokenAmount>(TokenMetadataEvent {
        token_id:     TOKEN_ID_WCCD,
        metadata_url: MetadataUrl {
            url:  String::from(TOKEN_METADATA_URL),
            hash: None,
        },
    }))?;

    Ok(state)
}

/// Initialzes the state of the w_ccd contract with the proxy and the
/// implementation addresses.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "initialize",
    parameter = "InitializeStateParams",
    mutable
)]
fn contract_state_initialize<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    ensure!(!host.state().initialized, concordium_cis2::Cis2Error::Custom(AlreadyInitialized));
    // Set proxy and implementation addresses.
    let params: InitializeStateParams = ctx.parameter_cursor().get()?;
    host.state_mut().proxy_address = params.proxy_address;
    host.state_mut().implementation_address = params.implementation_address;
    // Set the w_ccd_state contract as initialized.
    host.state_mut().initialized = true;
    Ok(())
}

// Getter and setter functions of state contract.

fn only_implementation(
    implementation: Option<ContractAddress>,
    sender: Address,
) -> ContractResult<()> {
    match implementation {
        Some(implementation_address) => {
            ensure_eq!(
                sender,
                Address::Contract(implementation_address),
                concordium_cis2::Cis2Error::Custom(OnlyImplementation)
            );
        }
        None => bail!(concordium_cis2::Cis2Error::Custom(OnlyImplementation)),
    };
    Ok(())
}

/// Set unpause_time.
#[receive(contract = "CIS2-wCCD-State", name = "set_unpause_time", mutable)]
fn contract_state_set_unpause_time<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    // Only implementation can set state.
    only_implementation(host.state().implementation_address, ctx.sender())?;

    // Set unpause_time.
    let unpause_time = ctx.parameter_cursor().get()?;
    host.state_mut().unpause_time = unpause_time;
    Ok(())
}

#[receive(contract = "CIS2-wCCD-State", name = "get_unpause_time", return_value = "UnpauseTime")]
fn contract_state_get_unpause_time<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<Timestamp> {
    Ok(host.state().unpause_time)
}

/// Initialize contract instance with no initial tokens.
/// Logs a `Mint` event for the single token id with no amounts.
/// TODO: Move event logs to proxy
#[init(contract = "CIS2-wCCD", enable_logger)]
fn contract_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
    logger: &mut impl HasLogger,
) -> InitResult<StateImplementation<S>> {
    // Get the instantiater of this contract instance.
    let invoker = Address::Account(ctx.init_origin());
    // Construct the initial contract state.
    let state = StateImplementation::new(invoker, state_builder);
    // Log event for the newly minted token.
    logger.log(&Cis2Event::Mint(MintEvent {
        token_id: TOKEN_ID_WCCD,
        amount:   ContractTokenAmount::from(0u64),
        owner:    invoker,
    }))?;

    // Log event for where to find metadata for the token
    logger.log(&Cis2Event::TokenMetadata::<_, ContractTokenAmount>(TokenMetadataEvent {
        token_id:     TOKEN_ID_WCCD,
        metadata_url: MetadataUrl {
            url:  String::from(TOKEN_METADATA_URL),
            hash: None,
        },
    }))?;

    Ok(state)
}

/// Initialzes the implementation of the w_ccd contract with the proxy and the
/// state addresses.
#[receive(
    contract = "CIS2-wCCD",
    name = "initialize",
    parameter = "InitializeImplementationParams",
    mutable
)]
fn contract_initialize<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation<S>, StateApiType = S>,
) -> ContractResult<()> {
    ensure!(!host.state().initialized, concordium_cis2::Cis2Error::Custom(AlreadyInitialized));
    // Set proxy and storage addresses.
    let params: InitializeImplementationParams = ctx.parameter_cursor().get()?;
    host.state_mut().proxy_address = params.proxy_address;
    host.state_mut().state_address = params.state_address;
    // Set the w_ccd_implementation contract as initialized.
    host.state_mut().initialized = true;
    Ok(())
}

/// Wrap an amount of CCD into wCCD tokens and transfer the tokens if the sender
/// is not the receiver.
#[receive(
    contract = "CIS2-wCCD",
    name = "wrap",
    parameter = "WrapParams",
    enable_logger,
    mutable,
    payable
)]
fn contract_wrap<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation<S>, StateApiType = S>,
    amount: Amount,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    let slot_time = ctx.metadata().slot_time();

    match host.state().state_address {
        None => bail!(concordium_cis2::Cis2Error::Custom(OnlyState)),

        Some(state_address) => {
            let unpause_time = host
                .invoke_contract_raw(
                    &state_address,
                    Parameter(&[]),
                    EntrypointName::new_unchecked("get_unpause_time"),
                    Amount::zero(),
                )?
                .1;

            let unpause_time = if let Some(mut unpause_time) = unpause_time {
                unpause_time.get()?
            } else {
                return Err(concordium_cis2::Cis2Error::Custom(StateInvokeError));
            };

            ensure!(slot_time >= unpause_time, concordium_cis2::Cis2Error::Custom(ContractPaused));

            let params: WrapParams = ctx.parameter_cursor().get()?;
            // Get the sender who invoked this contract function.
            let sender = ctx.sender();

            let receive_address = params.to.address();

            let (state, state_builder) = host.state_and_builder();

            // Update the state.
            state.mint(&TOKEN_ID_WCCD, amount.micro_ccd.into(), &receive_address, state_builder)?;

            // Log the newly minted tokens.
            logger.log(&Cis2Event::Mint(MintEvent {
                token_id: TOKEN_ID_WCCD,
                amount:   ContractTokenAmount::from(amount.micro_ccd),
                owner:    sender,
            }))?;

            // Only log a transfer event if receiver is not the one who payed for this.
            if sender != receive_address {
                logger.log(&Cis2Event::Transfer(TransferEvent {
                    token_id: TOKEN_ID_WCCD,
                    amount:   ContractTokenAmount::from(amount.micro_ccd),
                    from:     sender,
                    to:       receive_address,
                }))?;
            }

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
                )
                .unwrap_abort();
                Ok(())
            } else {
                Ok(())
            }
        }
    }
}

/// Unwrap an amount of wCCD tokens into CCD
#[receive(
    contract = "CIS2-wCCD",
    name = "unwrap",
    parameter = "UnwrapParams",
    enable_logger,
    mutable
)]
fn contract_unwrap<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    let slot_time = ctx.metadata().slot_time();

    match host.state().state_address {
        None => bail!(concordium_cis2::Cis2Error::Custom(OnlyState)),

        Some(state_address) => {
            let unpause_time = host
                .invoke_contract_raw(
                    &state_address,
                    Parameter(&[]),
                    EntrypointName::new_unchecked("get_unpause_time"),
                    Amount::zero(),
                )?
                .1;

            let unpause_time = if let Some(mut unpause_time) = unpause_time {
                unpause_time.get()?
            } else {
                return Err(concordium_cis2::Cis2Error::Custom(StateInvokeError));
            };

            ensure!(slot_time >= unpause_time, concordium_cis2::Cis2Error::Custom(ContractPaused));
            let params: UnwrapParams = ctx.parameter_cursor().get()?;
            // Get the sender who invoked this contract function.
            let sender = ctx.sender();
            let state = host.state_mut();
            ensure!(
                sender == params.owner || state.is_operator(&sender, &params.owner),
                ContractError::Unauthorized
            );

            // Update the state.
            state.burn(&TOKEN_ID_WCCD, params.amount, &params.owner)?;

            // Log the burning of tokens.
            logger.log(&Cis2Event::Burn(BurnEvent {
                token_id: TOKEN_ID_WCCD,
                amount:   params.amount,
                owner:    params.owner,
            }))?;

            let unwrapped_amount = Amount::from_micro_ccd(params.amount.into());

            match params.receiver {
                Receiver::Account(address) => host.invoke_transfer(&address, unwrapped_amount)?,
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
    }
}

// Contract functions required by CIS2

#[allow(dead_code)]
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
    contract = "CIS2-wCCD",
    name = "transfer",
    parameter = "TransferParameter",
    enable_logger,
    mutable
)]
fn contract_transfer<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    let slot_time = ctx.metadata().slot_time();

    match host.state().state_address {
        None => bail!(concordium_cis2::Cis2Error::Custom(OnlyState)),

        Some(state_address) => {
            let unpause_time = host
                .invoke_contract_raw(
                    &state_address,
                    Parameter(&[]),
                    EntrypointName::new_unchecked("get_unpause_time"),
                    Amount::zero(),
                )?
                .1;

            let unpause_time = if let Some(mut unpause_time) = unpause_time {
                unpause_time.get()?
            } else {
                return Err(concordium_cis2::Cis2Error::Custom(StateInvokeError));
            };

            ensure!(slot_time >= unpause_time, concordium_cis2::Cis2Error::Custom(ContractPaused));
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
                ensure!(
                    from == sender || state.is_operator(&sender, &from),
                    ContractError::Unauthorized
                );
                let to_address = to.address();
                // Update the contract state
                state.transfer(&token_id, amount, &from, &to_address, builder)?;

                // Log transfer event
                logger.log(&Cis2Event::Transfer(TransferEvent {
                    token_id,
                    amount,
                    from,
                    to: to_address,
                }))?;

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
    }
}

/// Enable or disable addresses as operators of the sender address.
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Fails to log event.
#[receive(
    contract = "CIS2-wCCD",
    name = "updateOperator",
    parameter = "UpdateOperatorParams",
    enable_logger,
    mutable
)]
fn contract_update_operator<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    let slot_time = ctx.metadata().slot_time();

    match host.state().state_address {
        None => bail!(concordium_cis2::Cis2Error::Custom(OnlyState)),

        Some(state_address) => {
            let unpause_time = host
                .invoke_contract_raw(
                    &state_address,
                    Parameter(&[]),
                    EntrypointName::new_unchecked("get_unpause_time"),
                    Amount::zero(),
                )?
                .1;

            let unpause_time = if let Some(mut unpause_time) = unpause_time {
                unpause_time.get()?
            } else {
                return Err(concordium_cis2::Cis2Error::Custom(StateInvokeError));
            };

            ensure!(slot_time >= unpause_time, concordium_cis2::Cis2Error::Custom(ContractPaused));
            // Parse the parameter.
            let UpdateOperatorParams(params) = ctx.parameter_cursor().get()?;
            // Get the sender who invoked this contract function.
            let sender = ctx.sender();

            let (state, state_builder) = host.state_and_builder();
            for param in params {
                // Update the operator in the state.

                match param.update {
                    OperatorUpdate::Add => {
                        state.add_operator(&sender, &param.operator, state_builder)?
                    }
                    OperatorUpdate::Remove => state.remove_operator(&sender, &param.operator)?,
                };

                // Log the appropriate event
                logger.log(&Cis2Event::<ContractTokenId, ContractTokenAmount>::UpdateOperator(
                    UpdateOperatorEvent {
                        owner:    sender,
                        operator: param.operator,
                        update:   param.update,
                    },
                ))?;
            }

            Ok(())
        }
    }
}

#[receive(contract = "CIS2-wCCD", name = "update_admin", parameter = "NewAdmin", mutable)]
fn contract_update_admin<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation<S>, StateApiType = S>,
) -> ContractResult<()> {
    // Check that only the old admin is authorized to update the admin address.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);
    // Parse the parameter.
    let new_admin = ctx.parameter_cursor().get()?;
    // Update admin.
    host.state_mut().admin = new_admin;
    Ok(())
}

#[receive(contract = "CIS2-wCCD", name = "pause", parameter = "UnpauseTime", mutable)]
fn contract_pause<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation<S>, StateApiType = S>,
) -> ContractResult<()> {
    // Check that only the current admin can pause.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);
    // Parse the parameter.
    let unpause_time = ctx.parameter_cursor().get()?;
    let slot_time = ctx.metadata().slot_time();
    // Update unpause_time.
    match slot_time.checked_add(unpause_time) {
        Some(new_unpause_time) => {
            host.state_mut().unpause_time = new_unpause_time;
        }
        None => {
            bail!(concordium_cis2::Cis2Error::Custom(OutOfBound))
        }
    }
    Ok(())
}

#[receive(contract = "CIS2-wCCD", name = "un_pause", mutable)]
fn contract_un_pause<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation<S>, StateApiType = S>,
) -> ContractResult<()> {
    // Check that only the current admin can un_pause.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    let slot_time = ctx.metadata().slot_time();
    // Update unpause_time to current slot time.
    host.state_mut().unpause_time = slot_time;
    Ok(())
}

/// Parameter type for the CIS-2 function `balanceOf` specialized to the subset
/// of TokenIDs used by this contract.
type ContractBalanceOfQueryParams = BalanceOfQueryParams<ContractTokenId>;

type ContractBalanceOfQueryResponse = BalanceOfQueryResponse<ContractTokenAmount>;

/// Get the balance of given token IDs and addresses.
///
/// It rejects if:
/// - Sender is not a contract.
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "CIS2-wCCD",
    name = "balanceOf",
    parameter = "ContractBalanceOfQueryParams",
    return_value = "ContractBalanceOfQueryResponse"
)]
fn contract_balance_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<StateImplementation<S>, StateApiType = S>,
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

/// Takes a list of queries. Each query is an owner address and some address to
/// check as an operator of the owner address.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "CIS2-wCCD",
    name = "operatorOf",
    parameter = "OperatorOfQueryParams",
    return_value = "OperatorOfQueryResponse"
)]
fn contract_operator_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<StateImplementation<S>, StateApiType = S>,
) -> ContractResult<OperatorOfQueryResponse> {
    // Parse the parameter.
    let params: OperatorOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for address being an operator of owner.
        let is_operator = host.state().is_operator(&query.owner, &query.address);
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
    contract = "CIS2-wCCD",
    name = "tokenMetadata",
    parameter = "ContractTokenMetadataQueryParams",
    return_value = "TokenMetadataQueryResponse"
)]
fn contract_token_metadata<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    _host: &impl HasHost<StateImplementation<S>, StateApiType = S>,
) -> ContractResult<TokenMetadataQueryResponse> {
    // Parse the parameter.
    let params: ContractTokenMetadataQueryParams = ctx.parameter_cursor().get()?;

    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for token_id in params.queries {
        // Check the token exists.
        ensure_eq!(token_id, TOKEN_ID_WCCD, ContractError::InvalidTokenId);

        let metadata_url = MetadataUrl {
            url:  TOKEN_METADATA_URL.to_string(),
            hash: None,
        };
        response.push(metadata_url);
    }
    let result = TokenMetadataQueryResponse::from(response);
    Ok(result)
}

// Tests

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    const ACCOUNT_0: AccountAddress = AccountAddress([0u8; 32]);
    const ADDRESS_0: Address = Address::Account(ACCOUNT_0);
    const ACCOUNT_1: AccountAddress = AccountAddress([1u8; 32]);
    const ADDRESS_1: Address = Address::Account(ACCOUNT_1);
    const ADMIN_ACCOUNT: AccountAddress = AccountAddress([2u8; 32]);
    const ADMIN_ADDRESS: Address = Address::Account(ADMIN_ACCOUNT);
    const NEW_ADMIN_ACCOUNT: AccountAddress = AccountAddress([3u8; 32]);
    const NEW_ADMIN_ADDRESS: Address = Address::Account(NEW_ADMIN_ACCOUNT);

    const IMPLEMENTATION: ContractAddress = ContractAddress {
        index:    1,
        subindex: 0,
    };
    const PROXY: ContractAddress = ContractAddress {
        index:    2,
        subindex: 0,
    };
    const STATE: ContractAddress = ContractAddress {
        index:    3,
        subindex: 0,
    };

    fn expect_error<E, T>(expr: Result<T, E>, err: E, msg: &str)
    where
        E: Eq + Debug,
        T: Debug, {
        let actual = expr.expect_err_report(msg);
        claim_eq!(actual, err);
    }

    /// Test helper function which creates a w_ccd_implementation contract state
    /// where ADDRESS_0 owns 400 tokens.
    fn initial_state_implementation<S: HasStateApi>(
        state_builder: &mut StateBuilder<S>,
    ) -> StateImplementation<S> {
        let mut state = StateImplementation::new(ADMIN_ADDRESS, state_builder);
        state
            .mint(&TOKEN_ID_WCCD, 400u64.into(), &ADDRESS_0, state_builder)
            .expect_report("Failed to setup state");
        state
    }

    /// Test helper function which creates a w_ccd_state contract state where
    /// ADDRESS_0 owns 400 tokens.
    fn initial_state_state<S: HasStateApi>(state_builder: &mut StateBuilder<S>) -> State<S> {
        let mut state = State::new(state_builder);
        state
            .mint(&TOKEN_ID_WCCD, 400u64.into(), &ADDRESS_0, state_builder)
            .expect_report("Failed to setup state");
        state
    }

    /// Test w_ccd state initialization works.
    #[concordium_test]
    fn test_state_init() {
        // Setup the context
        let mut ctx = TestInitContext::empty();
        ctx.set_init_origin(ACCOUNT_0);

        let mut logger = TestLogger::init();
        let mut builder = TestStateBuilder::new();

        // Call the contract function.
        let result = contract_state_init(&ctx, &mut builder, &mut logger);

        // Check the result
        let state = result.expect_report("Contract w_ccd state initialization failed");

        // Check the state
        claim_eq!(state.proxy_address, None, "Proxy address should not be initialized");
        claim_eq!(
            state.implementation_address,
            None,
            "Implementation address should not be initialized"
        );
        claim_eq!(state.initialized, false, "State contract should NOT be initialized");

        let mut host = TestHost::new(state, builder);

        // Setup parameter.
        let initialize_state_params = InitializeStateParams {
            proxy_address:          Some(PROXY),
            implementation_address: Some(IMPLEMENTATION),
        };

        let parameter = InitializeStateParams::from(initialize_state_params);

        let parameter_bytes = to_bytes(&parameter);

        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the state contract.

        let result: ContractResult<()> = contract_state_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        claim_eq!(host.state().proxy_address, Some(PROXY), "Proxy address should now be set");
        claim_eq!(
            host.state().implementation_address,
            Some(IMPLEMENTATION),
            "Implementation address should now be set"
        );
        claim_eq!(host.state().initialized, true, "State contract should be initialized");

        // Can not initialize again.
        let result: ContractResult<()> = contract_state_initialize(&ctx, &mut host);
        // Check that invoke failed.
        expect_error(
            result,
            concordium_cis2::Cis2Error::Custom(AlreadyInitialized),
            "Can not initialize again",
        );
    }

    /// Test set unpause time in state contract.
    #[concordium_test]
    fn test_set_unpause_time() {
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Setup the context.
        let mut ctx = TestReceiveContext::empty();

        // Setup parameter.
        let initialize_state_params = InitializeStateParams {
            proxy_address:          Some(PROXY),
            implementation_address: Some(IMPLEMENTATION),
        };
        let parameter = InitializeStateParams::from(initialize_state_params);
        let parameter_bytes = to_bytes(&parameter);

        ctx.set_parameter(&parameter_bytes);
        ctx.set_sender(concordium_std::Address::Contract(IMPLEMENTATION));

        // Initialize the state contract.
        let result: ContractResult<()> = contract_state_initialize(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[Timestamp::from_timestamp_millis(100)]);
        ctx.set_parameter(&parameter_bytes);

        // Check unpause_time.
        claim_eq!(
            host.state().unpause_time,
            Timestamp::from_timestamp_millis(0),
            "Unpause time should be 0"
        );

        // Check return value of the get_unpause_time function
        let timestamp: ContractResult<Timestamp> = contract_state_get_unpause_time(&ctx, &mut host);
        claim_eq!(
            timestamp,
            Ok(Timestamp::from_timestamp_millis(0)),
            "Getter function should return 0 as unpause_time"
        );

        // Call the contract function.
        let result: ContractResult<()> = contract_state_set_unpause_time(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check unpause_time.
        claim_eq!(
            host.state().unpause_time,
            Timestamp::from_timestamp_millis(100),
            "Unpause time should be updated to 100"
        );

        // Check return value of the get_unpause_time function
        let timestamp: ContractResult<Timestamp> = contract_state_get_unpause_time(&ctx, &mut host);
        claim_eq!(
            timestamp,
            Ok(Timestamp::from_timestamp_millis(100)),
            "Getter function should return 100 as unpause_time"
        );

        // Can NOT set_unpause_time from an address other than the implementation
        ctx.set_sender(ADDRESS_0);
        let result: ContractResult<()> = contract_state_set_unpause_time(&ctx, &mut host);
        // Check that invoke failed.
        expect_error(
            result,
            concordium_cis2::Cis2Error::Custom(OnlyImplementation),
            "Only implemnentation can call setter functions",
        );
    }

    /// Test initialization succeeds and the tokens are owned by the contract
    /// instantiater and the appropriate events are logged.
    #[concordium_test]
    fn test_init() {
        // Setup the context
        let mut ctx = TestInitContext::empty();
        ctx.set_init_origin(ACCOUNT_0);

        let mut logger = TestLogger::init();
        let mut builder = TestStateBuilder::new();

        // Call the contract function.
        let result = contract_init(&ctx, &mut builder, &mut logger);

        // Check the result
        let state = result.expect_report("Contract initialization failed");

        // Check the state
        claim_eq!(state.token.iter().count(), 0, "Only one token is initialized");
        let balance0 =
            state.balance(&TOKEN_ID_WCCD, &ADDRESS_0).expect_report("Token is expected to exist");
        claim_eq!(
            balance0,
            0u64.into(),
            "No initial tokens are owned by the contract instantiater"
        );

        // Check the logs
        claim_eq!(logger.logs.len(), 2, "Exactly one event should be logged");
        claim!(
            logger.logs.contains(&to_bytes(&Cis2Event::Mint(MintEvent {
                owner:    ADDRESS_0,
                token_id: TOKEN_ID_WCCD,
                amount:   ContractTokenAmount::from(0),
            }))),
            "Missing event for minting the token"
        );
        claim!(
            logger.logs.contains(&to_bytes(&Cis2Event::TokenMetadata::<_, ContractTokenAmount>(
                TokenMetadataEvent {
                    token_id:     TOKEN_ID_WCCD,
                    metadata_url: MetadataUrl {
                        url:  String::from(TOKEN_METADATA_URL),
                        hash: None,
                    },
                }
            ))),
            "Missing event with metadata for the token"
        );
    }

    /// Test transfer succeeds, when `from` is the sender.
    #[concordium_test]
    fn test_transfer_account() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(0));

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let mut state = StateImplementation::new(ADMIN_ADDRESS, &mut state_builder);
        state
            .mint(&TOKEN_ID_WCCD, 400.into(), &ADDRESS_0, &mut state_builder)
            .expect_report("Failed to setup state");
        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: Some(PROXY),
            state_address: Some(STATE),
        };
        let parameter = InitializeImplementationParams::from(initialize_implementation_params);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("get_unpause_time".into()),
            MockFn::returning_ok(Timestamp::from_timestamp_millis(0)),
        );

        // Setup parameter.
        let transfer = Transfer {
            token_id: TOKEN_ID_WCCD,
            amount:   ContractTokenAmount::from(100),
            from:     ADDRESS_0,
            to:       Receiver::from_account(ACCOUNT_1),
            data:     AdditionalData::empty(),
        };
        let parameter = TransferParams::from(vec![transfer]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Call the contract function.
        let result: ContractResult<()> = contract_transfer(&ctx, &mut host, &mut logger);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        let balance0 = host
            .state()
            .balance(&TOKEN_ID_WCCD, &ADDRESS_0)
            .expect_report("Token is expected to exist");
        let balance1 = host
            .state()
            .balance(&TOKEN_ID_WCCD, &ADDRESS_1)
            .expect_report("Token is expected to exist");
        claim_eq!(
            balance0,
            300.into(),
            "Token owner balance should be decreased by the transferred amount"
        );
        claim_eq!(
            balance1,
            100.into(),
            "Token receiver balance should be increased by the transferred amount"
        );

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "Only one event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Cis2Event::Transfer(TransferEvent {
                from:     ADDRESS_0,
                to:       ADDRESS_1,
                token_id: TOKEN_ID_WCCD,
                amount:   ContractTokenAmount::from(100),
            })),
            "Incorrect event emitted"
        )
    }

    /// Test transfer token fails, when sender is neither the owner or an
    /// operator of the owner.
    #[concordium_test]
    fn test_transfer_not_authorized() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_1);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(0));

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state_implementation(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: Some(PROXY),
            state_address: Some(STATE),
        };
        let parameter = InitializeImplementationParams::from(initialize_implementation_params);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("get_unpause_time".into()),
            MockFn::returning_ok(Timestamp::from_timestamp_millis(0)),
        );

        // Setup parameter.
        let transfer = Transfer {
            from:     ADDRESS_0,
            to:       Receiver::from_account(ACCOUNT_1),
            token_id: TOKEN_ID_WCCD,
            amount:   ContractTokenAmount::from(100),
            data:     AdditionalData::empty(),
        };
        let parameter = TransferParams::from(vec![transfer]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Call the contract function.
        let result: ContractResult<()> = contract_transfer(&ctx, &mut host, &mut logger);
        // Check the result.
        let err = result.expect_err_report("Expected to fail");
        claim_eq!(err, ContractError::Unauthorized, "Error is expected to be Unauthorized")
    }

    /// Test transfer succeeds when sender is not the owner, but is an operator
    /// of the owner.
    #[concordium_test]
    fn test_operator_transfer() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_1);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(0));

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let mut state = initial_state_implementation(&mut state_builder);

        let result: ContractResult<()> =
            state.add_operator(&ADDRESS_0, &ADDRESS_1, &mut state_builder);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: Some(PROXY),
            state_address: Some(STATE),
        };
        let parameter = InitializeImplementationParams::from(initialize_implementation_params);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("get_unpause_time".into()),
            MockFn::returning_ok(Timestamp::from_timestamp_millis(0)),
        );

        // Setup the parameter.
        let transfer = Transfer {
            from:     ADDRESS_0,
            to:       Receiver::from_account(ACCOUNT_1),
            token_id: TOKEN_ID_WCCD,
            amount:   ContractTokenAmount::from(100),
            data:     AdditionalData::empty(),
        };
        let parameter = TransferParams::from(vec![transfer]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Call the contract function.
        let result: ContractResult<()> = contract_transfer(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        let balance0 = host
            .state()
            .balance(&TOKEN_ID_WCCD, &ADDRESS_0)
            .expect_report("Token is expected to exist");
        let balance1 = host
            .state()
            .balance(&TOKEN_ID_WCCD, &ADDRESS_1)
            .expect_report("Token is expected to exist");
        claim_eq!(balance0, 300.into()); //, "Token owner balance should be decreased by the transferred amount");
        claim_eq!(
            balance1,
            100.into(),
            "Token receiver balance should be increased by the transferred amount"
        );

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "Only one event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Cis2Event::Transfer(TransferEvent {
                from:     ADDRESS_0,
                to:       ADDRESS_1,
                token_id: TOKEN_ID_WCCD,
                amount:   ContractTokenAmount::from(100),
            })),
            "Incorrect event emitted"
        )
    }

    /// Test adding an operator succeeds and the appropriate event is logged.
    #[concordium_test]
    fn test_add_operator() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(0));

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state_implementation(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: Some(PROXY),
            state_address: Some(STATE),
        };
        let parameter = InitializeImplementationParams::from(initialize_implementation_params);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("get_unpause_time".into()),
            MockFn::returning_ok(Timestamp::from_timestamp_millis(0)),
        );

        // Setup parameter.
        let update = UpdateOperator {
            operator: ADDRESS_1,
            update:   OperatorUpdate::Add,
        };
        let parameter = UpdateOperatorParams(vec![update]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Call the contract function.
        let result: ContractResult<()> = contract_update_operator(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        claim!(host.state().is_operator(&ADDRESS_1, &ADDRESS_0), "Account should be an operator");

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Cis2Event::<ContractTokenId, ContractTokenAmount>::UpdateOperator(
                UpdateOperatorEvent {
                    owner:    ADDRESS_0,
                    operator: ADDRESS_1,
                    update:   OperatorUpdate::Add,
                }
            )),
            "Incorrect event emitted"
        )
    }

    /// Test pause contract.
    #[concordium_test]
    fn test_pause() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(100));

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[Timestamp::from_timestamp_millis(100)]);
        ctx.set_parameter(&parameter_bytes);

        let mut state_builder = TestStateBuilder::new();
        let state = initial_state_implementation(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Check unpause_time.
        claim_eq!(
            host.state().unpause_time,
            Timestamp::from_timestamp_millis(0),
            "Unpause time should be 0"
        );

        // Call the contract function.
        let result: ContractResult<()> = contract_pause(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check unpause_time.
        claim_eq!(
            host.state().unpause_time,
            Timestamp::from_timestamp_millis(200),
            "Unpause time should be updated to 200"
        );
    }

    /// Test that only the current admin can update the unpause time.
    #[concordium_test]
    fn test_pause_not_authorized() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        // NEW_ADMIN is not the current admin but tries to update the unpause time.
        ctx.set_sender(NEW_ADMIN_ADDRESS);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(100));

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[Timestamp::from_timestamp_millis(100)]);
        ctx.set_parameter(&parameter_bytes);

        let mut state_builder = TestStateBuilder::new();
        let state = initial_state_implementation(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Check unpause_time.
        claim_eq!(
            host.state().unpause_time,
            Timestamp::from_timestamp_millis(0),
            "Unpause time should be 0"
        );

        // Call the contract function.
        let result: ContractResult<()> = contract_pause(&ctx, &mut host);
        // Check that invoke failed.
        expect_error(
            result,
            ContractError::Unauthorized,
            "Pause should fail because not the current admin tries to invoke it",
        );

        // Check unpause_time is still the same.
        claim_eq!(
            host.state().unpause_time,
            Timestamp::from_timestamp_millis(0),
            "Unpause time should be still the same"
        );
    }

    /// Test un_pause contract.
    #[concordium_test]
    fn test_un_pause() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(100));

        let mut state_builder = TestStateBuilder::new();
        let state = initial_state_implementation(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // UnPausing contract
        let result: ContractResult<()> = contract_un_pause(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check unpause_time.
        claim_eq!(
            host.state().unpause_time,
            Timestamp::from_timestamp_millis(100),
            "Unpause time should be updated to 100"
        );
    }

    /// Test that only the current admin can un_pause.
    #[concordium_test]
    fn test_un_pause_not_authorized() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        // NEW_ADMIN is not the current admin but tries to un_pause the contract.
        ctx.set_sender(NEW_ADMIN_ADDRESS);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(100));

        let mut state_builder = TestStateBuilder::new();
        let state = initial_state_implementation(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // UnPausing contract.
        let result: ContractResult<()> = contract_un_pause(&ctx, &mut host);
        // Check that invoke failed.
        expect_error(
            result,
            ContractError::Unauthorized,
            "Un_pause should fail because not the current admin tries to invoke it",
        );

        // Check unpause_time was not updated.
        claim_eq!(
            host.state().unpause_time,
            Timestamp::from_timestamp_millis(0),
            "Unpause time should still be 0"
        );
    }

    /// Test can NOT wrap when contract is paused.
    #[concordium_test]
    fn test_no_wrap_when_paused() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(100));

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[Timestamp::from_timestamp_millis(100)]);
        ctx.set_parameter(&parameter_bytes);

        let mut state_builder = TestStateBuilder::new();
        let state = initial_state_implementation(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: Some(PROXY),
            state_address: Some(STATE),
        };
        let parameter = InitializeImplementationParams::from(initialize_implementation_params);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("get_unpause_time".into()),
            MockFn::returning_ok(Timestamp::from_timestamp_millis(200)),
        );

        // Setup parameter.
        let wrap_params = WrapParams {
            to:   Receiver::from_account(ACCOUNT_1),
            data: AdditionalData::empty(),
        };

        let parameter = WrapParams::from(wrap_params);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let amount = Amount::from_micro_ccd(100);

        // Trying to invoke the wrap entrypoint. It will revert because the function is
        // paused.
        let result: ContractResult<()> = contract_wrap(&ctx, &mut host, amount, &mut logger);
        // Check that contract is paused.
        expect_error(
            result,
            concordium_cis2::Cis2Error::Custom(ContractPaused),
            "Wrap should fail because contract is paused",
        );
    }

    /// Test can NOT un_wrap when contract is paused.
    #[concordium_test]
    fn test_no_un_wrap_when_paused() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(100));
        ctx.set_sender(ADDRESS_1);

        let mut state_builder = TestStateBuilder::new();
        let state = initial_state_implementation(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: Some(PROXY),
            state_address: Some(STATE),
        };
        let parameter = InitializeImplementationParams::from(initialize_implementation_params);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("get_unpause_time".into()),
            MockFn::returning_ok(Timestamp::from_timestamp_millis(0)),
        );

        // Setup parameter.
        let wrap_params = WrapParams {
            to:   Receiver::from_account(ACCOUNT_1),
            data: AdditionalData::empty(),
        };

        let parameter = WrapParams::from(wrap_params);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let amount = Amount::from_micro_ccd(100);

        // Account_1 wraps some CCD.
        let result: ContractResult<()> = contract_wrap(&ctx, &mut host, amount, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[Timestamp::from_timestamp_millis(100)]);
        ctx.set_parameter(&parameter_bytes);

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("get_unpause_time".into()),
            MockFn::returning_ok(Timestamp::from_timestamp_millis(200)),
        );

        // Setup parameter.
        let un_wrap_params = UnwrapParams {
            amount:   ContractTokenAmount::from(100),
            owner:    ADDRESS_1,
            receiver: Receiver::from_account(ACCOUNT_1),
            data:     AdditionalData::empty(),
        };

        let parameter = UnwrapParams::from(un_wrap_params);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        host.set_self_balance(amount);
        let mut logger = TestLogger::init();

        ctx.set_sender(ADDRESS_1);

        // Trying to invoke the un_wrap entrypoint. It will revert because the function
        // is paused.
        let result: ContractResult<()> = contract_unwrap(&ctx, &mut host, &mut logger);
        // Check that contract is paused.
        expect_error(
            result,
            concordium_cis2::Cis2Error::Custom(ContractPaused),
            "Un_wrap should fail because contract is paused",
        );
    }

    /// Test can NOT transfer when contract is paused.
    #[concordium_test]
    fn test_no_transfer_when_paused() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(100));
        ctx.set_sender(ADMIN_ADDRESS);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let mut state = StateImplementation::new(ADMIN_ADDRESS, &mut state_builder);
        state
            .mint(&TOKEN_ID_WCCD, 400.into(), &ADDRESS_0, &mut state_builder)
            .expect_report("Failed to setup state");
        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: Some(PROXY),
            state_address: Some(STATE),
        };
        let parameter = InitializeImplementationParams::from(initialize_implementation_params);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("get_unpause_time".into()),
            MockFn::returning_ok(Timestamp::from_timestamp_millis(200)),
        );

        // Setup the parameter.
        let transfer = Transfer {
            token_id: TOKEN_ID_WCCD,
            amount:   ContractTokenAmount::from(100),
            from:     ADDRESS_0,
            to:       Receiver::from_account(ACCOUNT_1),
            data:     AdditionalData::empty(),
        };
        let parameter = TransferParams::from(vec![transfer]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        ctx.set_sender(ADDRESS_0);

        // Call the contract function.
        let result: ContractResult<()> = contract_transfer(&ctx, &mut host, &mut logger);

        // Check that contract is paused.
        expect_error(
            result,
            concordium_cis2::Cis2Error::Custom(ContractPaused),
            "Transfer should fail because contract is paused",
        );

        // Check the state.
        let balance0 = host
            .state()
            .balance(&TOKEN_ID_WCCD, &ADDRESS_0)
            .expect_report("Token is expected to exist");
        let balance1 = host
            .state()
            .balance(&TOKEN_ID_WCCD, &ADDRESS_1)
            .expect_report("Token is expected to exist");
        claim_eq!(balance0, 400.into(), "Token owner balance should be still the same");
        claim_eq!(balance1, 0.into(), "Token receiver balance should be still the same");
    }

    /// Test can NOT update operator when contract is paused.
    #[concordium_test]
    fn test_no_add_operator_when_paused() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(100));
        ctx.set_sender(ADMIN_ADDRESS);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state_implementation(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: Some(PROXY),
            state_address: Some(STATE),
        };
        let parameter = InitializeImplementationParams::from(initialize_implementation_params);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("get_unpause_time".into()),
            MockFn::returning_ok(Timestamp::from_timestamp_millis(200)),
        );

        // Setup parameter.
        let update = UpdateOperator {
            operator: ADDRESS_1,
            update:   OperatorUpdate::Add,
        };
        let parameter = UpdateOperatorParams(vec![update]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        ctx.set_sender(ADDRESS_0);

        // Call the contract function.
        let result: ContractResult<()> = contract_update_operator(&ctx, &mut host, &mut logger);

        // Check that contract is paused.
        expect_error(
            result,
            concordium_cis2::Cis2Error::Custom(ContractPaused),
            "Update_operator should fail because contract is paused",
        );

        // Check the state.
        claim_eq!(
            host.state().is_operator(&ADDRESS_1, &ADDRESS_0),
            false,
            "Account should not be an operator"
        );
    }

    /// Test updating to new admin address.
    #[concordium_test]
    fn test_update_admin() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[NEW_ADMIN_ADDRESS]);
        ctx.set_parameter(&parameter_bytes);

        let mut state_builder = TestStateBuilder::new();
        let state = initial_state_implementation(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be the old admin address");

        // Call the contract function.
        let result: ContractResult<()> = contract_update_admin(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the admin state.
        claim_eq!(host.state().admin, NEW_ADMIN_ADDRESS, "Admin should be the new admin address");
    }

    /// Test that only the current admin can update the admin address.
    #[concordium_test]
    fn test_update_admin_not_authorized() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        // NEW_ADMIN is not the current admin but tries to update the admin variable to
        // its own address.
        ctx.set_sender(NEW_ADMIN_ADDRESS);

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[NEW_ADMIN_ADDRESS]);
        ctx.set_parameter(&parameter_bytes);

        let mut state_builder = TestStateBuilder::new();
        let state = initial_state_implementation(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be the old admin address");

        // Call the contract function.
        let result: ContractResult<()> = contract_update_admin(&ctx, &mut host);
        // Check that invoke failed.
        expect_error(
            result,
            ContractError::Unauthorized,
            "Update admin should fail because not the current admin tries to update",
        );

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be still the old admin address");
    }
}
