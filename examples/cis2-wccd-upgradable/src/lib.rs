//! upgradable wCCD: Canonical wCCD implementation following the CIS2 standard.
//! Compared to the other wCCD example in this repo, this smart contract
//! can be paused/unpaused and upgraded by admin addresses.
//!
//! # Description
//! The token in this contract is a wrapped CCD (wCCD), meaning it holds a one
//! to one correspondence with the CCD.
//! Note: The word 'address' refers to either an account address or a
//! contract address.
//!
//! As follows from the CIS2 specification, the contract has a `transfer`
//! function for transferring an amount of a specific token type from one
//! address to another address. An address can enable and disable one or more
//! addresses as operators. An operator of some token owner address is allowed
//! to transfer any tokens of the owner.
//!
//! Besides the contract functions required CIS2, this contract implements a
//! function `wrap` for converting CCD into wCCD tokens. It accepts an amount of
//! CCD and mints this amount of wCCD. The function takes a receiving address as
//! the parameter and transfers the amount of tokens.
//!
//! The contract also implements a contract function `unwrap` for converting
//! wCCD back into CCD. The function takes the amount of tokens to unwrap, the
//! address owning these wCCD and a receiver for the CCD. If the sender is the
//! owner or an operator of the owner, the wCCD are burned and the amount of
//! CCD is sent to the receiver.
//!
//! The protocol consists of three smart contracts (`proxy`, `implementation`,
//! and `state`). All wccd functions (e.g. `wrap`, `unwrap`, `transfer`,
//! `updateOperator`, `balanceOf`, `operatorOf` and `tokenMetadata`) have to be
//! invoked on the `proxy` contract. The `proxy` will append the
//! `current_sender` to the input parameters so that the `implementation` can
//! retrieve this information. Invoking the wccd functions directly on the
//! `implementation` without going through the `proxy` fallback function will
//! revert.

//! The admin address on the `proxy` can upgrade the protocol with
//! a new `implementation` contract. The admin address on the
//! `implementation` can pause/unpause the protocol.
//!
//! Deploy the `state` and the `implementation` contract first by invoking their
//! respective `init` functions. Then, deploy the `proxy` contract and pass
//! the already deployed contract addresses into the proxy `init` function.
//! Then, call the `initialize` function on the `proxy` contract. This function
//! will call the `initialize` functions on the `state` as well as the
//! `implementation` contracts to set the remaining addresses.
#![cfg_attr(not(feature = "std"), no_std)]

use concordium_cis2::*;
use concordium_std::{fmt::Debug, *};

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

/// Needed for the custom serial instance, which doesn't include the `Option`
/// tag and the length of the vector.
#[derive(PartialEq, Eq, Debug)]
struct RawReturnValue(Option<Vec<u8>>);

impl Serial for RawReturnValue {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        match &self.0 {
            Some(rv) => out.write_all(rv),
            None => Ok(()),
        }
    }
}

type WrapParamsWithSender = ParamWithSender<WrapParams>;

type UnwrapParamsWithSender = ParamWithSender<UnwrapParams>;

type UpdateOperatorParamsWithSender = ParamWithSender<UpdateOperatorParams>;

type TransferParameterWithSender = ParamWithSender<TransferParameter>;

#[derive(Debug)]
struct ParamWithSender<T> {
    params: T,
    sender: Address,
}

impl Serial for ParamWithSender<WrapParams> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.params.to.serial(out)?;
        self.params.data.serial(out)?;
        self.sender.serial(out)
    }
}

impl Serial for ParamWithSender<UnwrapParams> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.params.amount.serial(out)?;
        self.params.owner.serial(out)?;
        self.params.receiver.serial(out)?;
        self.params.data.serial(out)?;
        self.sender.serial(out)
    }
}

impl Serial for ParamWithSender<UpdateOperatorParams> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.params.serial(out)?;
        self.sender.serial(out)
    }
}

impl Serial for ParamWithSender<TransferParameter> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.params.serial(out)?;
        self.sender.serial(out)
    }
}

impl Serial for ParamWithSender<Vec<u8>> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        out.write_all(&self.params)?;
        self.sender.serial(out)
    }
}

impl<T: Deserial> Deserial for ParamWithSender<T> {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let params = T::deserial(source)?;
        let sender = Address::deserial(source)?;
        Ok(ParamWithSender {
            params,
            sender,
        })
    }
}

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

/// The `state` contract state.
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S> {
    /// Address of the w_ccd proxy contract.
    proxy_address:          Option<ContractAddress>,
    /// Address of the w_ccd implementation contract.
    implementation_address: Option<ContractAddress>,
    /// The state of the one token.
    token:                  StateMap<Address, AddressState<S>, S>,
    /// Contract is paused/unpaused.
    paused:                 bool,
}

/// The `implementation` contract state.
#[derive(Serial, Deserial, SchemaType)]
struct StateImplementation {
    /// The admin address can pause/unpause the contract.
    admin:         Address,
    /// Address of the w_ccd proxy contract.
    proxy_address: Option<ContractAddress>,
    /// Address of the w_ccd state contract.
    state_address: Option<ContractAddress>,
}

/// The `proxy` contract state.
#[derive(Serial, Deserial, SchemaType)]
struct StateProxy {
    /// The admin address can upgrade the implementation contract.
    admin:                  Address,
    /// Address of the w_ccd implementation contract.
    implementation_address: ContractAddress,
    /// Address of the w_ccd state contract.
    state_address:          ContractAddress,
}

/// The parameter type for the contract function `unwrap`.
/// Takes an amount of tokens and unwraps the CCD and send it to a receiver.
#[derive(Serialize, SchemaType)]
struct UnwrapParams {
    /// The amount of tokens to unwrap.
    amount:   ContractTokenAmount,
    /// The owner of the tokens.
    owner:    Address,
    /// The address to receive these unwrapped CCD.
    receiver: Receiver,
    /// If the `Receiver` is a contract the unwrapped CCD together with these
    /// additional data bytes are sent to the function entrypoint specified in
    /// the `Receiver`.
    data:     AdditionalData,
}

/// The parameter type for the contract function `wrap`.
/// It includes the receiver for the wrapped CCD tokens.
#[derive(Serialize, SchemaType)]
struct WrapParams {
    /// The address to receive these tokens.
    /// If the receiver is the sender of the message wrapping the tokens, it
    /// will not log a transfer.
    to:   Receiver,
    /// Some additional bytes that are used in the `OnReceivingCis2` hook. Only
    /// if the `Receiver` is a contract the receive hook function is
    /// executed.
    data: AdditionalData,
}

/// The parameter type for the state contract function `initialize`.
#[derive(Serialize, SchemaType)]
struct InitializeStateParams {
    /// Address of the w_ccd proxy contract.
    proxy_address:          ContractAddress,
    /// Address of the w_ccd implementation contract.
    implementation_address: ContractAddress,
}

/// The parameter type for the implementation contract function `initialize`.
#[derive(Serialize, SchemaType)]
struct InitializeImplementationParams {
    /// Address of the w_ccd proxy contract.
    proxy_address: ContractAddress,
    /// Address of the w_ccd state contract.
    state_address: ContractAddress,
}

/// The parameter type for the proxy contract function `init`.
#[derive(Serialize, SchemaType)]
struct InitProxyParams {
    /// Address of the w_ccd implementation contract.
    implementation_address: ContractAddress,
    /// Address of the w_ccd state contract.
    state_address:          ContractAddress,
}

/// The parameter type for the state contract function
/// `set_implementation_address`.
#[derive(Serialize, SchemaType)]
struct SetImplementationAddressParams {
    /// Address of the w_ccd implementation contract.
    implementation_address: ContractAddress,
}

/// The parameter type for the proxy and state contract functions `transferCCD`.
#[derive(Serialize, SchemaType)]
struct TransferCCDParams {
    /// Amount of CCD to transfer to implementation.
    amount: ContractTokenAmount,
}

/// The parameter type for the implementation contract function `transferCCD`.
#[derive(Serialize, SchemaType)]
struct TransferCCDImplementationParams {
    /// Amount of CCD to transfer.
    amount:  ContractTokenAmount,
    /// Account that receives CCD tokens.
    account: AccountAddress,
}

/// The parameter type for the state contract function `setPaused`.
#[derive(Serialize, SchemaType)]
struct SetPausedParams {
    /// Contract is paused/unpaused.
    paused: bool,
}

/// The parameter type for the state contract function `setIsOperator`.
#[derive(Serialize, SchemaType)]
struct SetIsOperatorParams {
    /// Owner of the tokens.
    owner:    Address,
    /// Address that will be set/unset to be an operator to the above owner.
    operator: Address,
    /// Add or remove an operator.
    update:   Update,
}

/// The parameter type for the state contract function `setBalance`.
#[derive(Serialize, SchemaType)]
struct SetBalanceParams {
    /// Owner of the tokens.
    owner:  Address,
    /// Amount of tokens that the balance of the owner is updated.
    amount: ContractTokenAmount,
    /// Add or remove the amount from the balance of the owner.
    update: Update,
}

/// The parameter type for the state contract function `getBalance`.
#[derive(Serialize, SchemaType)]
struct GetBalanceParams {
    /// Owner of the tokens.
    owner: Address,
}

/// The parameter type for the state contract function `isOperator`.
#[derive(Serialize, SchemaType)]
struct IsOperatorParams {
    /// Owner of the tokens.
    owner:   Address,
    /// Address that will be checked if it is an operator to the above owner.
    address: Address,
}

/// The return type for the state contract function `view`.
#[derive(Serialize, SchemaType)]
struct ReturnBasicState {
    /// Address of the w_ccd proxy contract.
    proxy_address:          ContractAddress,
    /// Address of the w_ccd implementation contract.
    implementation_address: ContractAddress,
}

/// Update struct.
#[derive(Debug, Serialize, SchemaType)]
pub enum Update {
    /// Remove an amount or operator.
    Remove,
    /// Add an amount or operator.
    Add,
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
    /// Contract is paused.
    ContractPaused,
    /// Contract already initialized.
    AlreadyInitialized,
    /// Contract not initialized.
    NotInitialized,
    /// Only implementation contract.
    OnlyImplementation,
    /// Only proxy contract.
    OnlyProxy,
    /// Only state contract.
    OnlyState,
    /// Raised when implementation can not invoke state contract.
    StateInvokeError,
    /// Raised when implementation can not invoke proxy contract.
    ProxyInvokeError,
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
    /// Creates the new state of the `state` contract with no one owning any
    /// tokens by default. The proxy_address and the implementation_address
    /// are set to None. Both addresses have to be set with the `initialize`
    /// function after the `proxy` contract is deployed.
    fn new(state_builder: &mut StateBuilder<S>) -> Self {
        // Setup state.
        State {
            proxy_address:          None,
            implementation_address: None,
            token:                  state_builder.new_map(),
            paused:                 false,
        }
    }
}

impl StateImplementation {
    /// Creates the new state of the `implementation` contract. The
    /// proxy_address and the state_address are set to None. Both addresses
    /// have to be set with the `initialize` function after the `proxy`
    /// contract is deployed.
    fn new(admin: Address) -> Self {
        // Setup state.
        StateImplementation {
            admin,
            proxy_address: None,
            state_address: None,
        }
    }

    /// Get the current balance of a given token id for a given address.
    /// Results in an error if the token id does not exist in the state.
    fn balance<S>(
        &self,
        token_id: &ContractTokenId,
        owner: &Address,
        host: &impl HasHost<StateImplementation, StateApiType = S>,
    ) -> ContractResult<ContractTokenAmount> {
        ensure_eq!(token_id, &TOKEN_ID_WCCD, ContractError::InvalidTokenId);

        // Setup parameter.
        let parameter_bytes = to_bytes(owner);

        let state_address = host
            .state()
            .state_address
            .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::StateInvokeError))?;

        let balance = host.invoke_contract_raw_read_only(
            &state_address,
            Parameter(&parameter_bytes),
            EntrypointName::new_unchecked("getBalance"),
            Amount::zero(),
        )?;

        // It is expected that this contract is initialized with the w_ccd_state
        // contract (a V1 contract). In that case, the balance variable can be
        // queried from the state contract without error.
        let balance = balance
            .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::StateInvokeError))?
            .get()?;

        Ok(balance)
    }

    /// Check if an address is an operator of a specific owner address.
    /// Results in an error if the token id does not exist in the state.
    fn is_operator<S>(
        &self,
        address: &Address,
        owner: &Address,
        host: &impl HasHost<StateImplementation, StateApiType = S>,
    ) -> ContractResult<bool> {
        // Setup parameter.
        let parameter_bytes = to_bytes(&IsOperatorParams {
            owner:   *owner,
            address: *address,
        });

        let state_address = host
            .state()
            .state_address
            .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::StateInvokeError))?;

        let is_operator = host.invoke_contract_raw_read_only(
            &state_address,
            Parameter(&parameter_bytes),
            EntrypointName::new_unchecked("isOperator"),
            Amount::zero(),
        )?;

        // It is expected that this contract is initialized with the w_ccd_state
        // contract (a V1 contract). In that case, the balance variable can be
        // queried from the state contract without error.
        let is_operator = is_operator
            .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::StateInvokeError))?
            .get()?;

        Ok(is_operator)
    }
}

// Contract functions

/// Initialize the state contract instance with no initial tokens.
/// Logs a `Mint` event for the single token id with no amounts.
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

/// Initialize contract instance with no initial tokens.
/// Logs a `Mint` event for the single token id with no amounts.
#[init(contract = "CIS2-wCCD", enable_logger)]
fn contract_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
    logger: &mut impl HasLogger,
) -> InitResult<StateImplementation> {
    // Get the instantiater of this contract instance.
    let invoker = Address::Account(ctx.init_origin());
    // Construct the initial contract state.
    let state = StateImplementation::new(invoker);
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

/// Initializes the state of the w_ccd proxy contract with the state and the
/// implementation addresses. Both addresses have to be set together by calling
/// this function.
#[init(contract = "CIS2-wCCD-Proxy", parameter = "InitProxyParams", enable_logger)]
fn contract_proxy_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
    _logger: &mut impl HasLogger,
) -> InitResult<StateProxy> {
    // Set state and implementation addresses.
    let params: InitProxyParams = ctx.parameter_cursor().get()?;

    // Get the instantiater of this contract instance.
    let invoker = Address::Account(ctx.init_origin());
    // Construct the initial proxy contract state.
    let state = StateProxy {
        admin:                  invoker,
        state_address:          params.state_address,
        implementation_address: params.implementation_address,
    };

    Ok(state)
}

/// Initializes the state of the w_ccd contract with the proxy and the
/// implementation addresses. Both addresses have to be set together by calling
/// this function. This function can only be called once.
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
    ensure!(
        host.state().proxy_address.is_none() && host.state().implementation_address.is_none(),
        concordium_cis2::Cis2Error::Custom(CustomContractError::AlreadyInitialized)
    );
    // Set proxy and implementation addresses.
    let params: InitializeStateParams = ctx.parameter_cursor().get()?;
    host.state_mut().proxy_address = Some(params.proxy_address);
    host.state_mut().implementation_address = Some(params.implementation_address);
    Ok(())
}

/// Initializes the implementation of the w_ccd contract with the proxy and the
/// state addresses. Both addresses have to be set together by calling this
/// function. This function can only be called once.
#[receive(
    contract = "CIS2-wCCD",
    name = "initialize",
    parameter = "InitializeImplementationParams",
    mutable
)]
fn contract_initialize<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    ensure!(
        host.state().proxy_address.is_none() && host.state().state_address.is_none(),
        concordium_cis2::Cis2Error::Custom(CustomContractError::AlreadyInitialized)
    );
    // Set proxy and storage addresses.
    let params: InitializeImplementationParams = ctx.parameter_cursor().get()?;
    host.state_mut().proxy_address = Some(params.proxy_address);
    host.state_mut().state_address = Some(params.state_address);
    Ok(())
}

/// Initializes the `implementation` and `state` contracts by using the
/// addresses that the `proxy` contract was set up. This function will call the
/// `initialize` functions on the `implementation` as well as the `state`
/// contracts.
#[receive(contract = "CIS2-wCCD-Proxy", name = "initialize", mutable)]
fn contract_proxy_initialize<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateProxy, StateApiType = S>,
) -> ContractResult<()> {
    let state_address = host.state().state_address;

    let parameter_bytes = to_bytes(&InitializeStateParams {
        proxy_address:          ctx.self_address(),
        implementation_address: host.state().implementation_address,
    });

    host.invoke_contract_raw(
        &state_address,
        Parameter(&parameter_bytes),
        EntrypointName::new_unchecked("initialize"),
        Amount::zero(),
    )?;

    let implementation_address = host.state().implementation_address;

    let parameter_bytes = to_bytes(&InitializeImplementationParams {
        proxy_address: ctx.self_address(),
        state_address: host.state().state_address,
    });

    host.invoke_contract_raw(
        &implementation_address,
        Parameter(&parameter_bytes),
        EntrypointName::new_unchecked("initialize"),
        Amount::zero(),
    )?;

    Ok(())
}

/// The fallback method, which redirects the invocations to the implementation.
#[receive(contract = "CIS2-wCCD-Proxy", fallback, mutable, payable, parameter = "WrapParams")]
fn receive_fallback<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateProxy, StateApiType = S>,
    amount: Amount,
) -> ReceiveResult<RawReturnValue> {
    let entrypoint = ctx.named_entrypoint();
    let implementation = host.state().implementation_address;

    let mut parameter_buffer = vec![0; ctx.parameter_cursor().size() as usize];
    ctx.parameter_cursor().read_exact(&mut parameter_buffer)?;

    // Appending the sender to the input parameters
    let paramter_with_sender = ParamWithSender {
        params: parameter_buffer,
        sender: ctx.sender(),
    };

    let parameter_bytes = to_bytes(&paramter_with_sender);

    // Forwarding the invoke unaltered to the implementation contract.
    let return_value = host
        .invoke_contract_raw(
            &implementation,
            Parameter(&parameter_bytes),
            entrypoint.as_entrypoint_name(),
            amount,
        )
        .map_err(|r| {
            if let CallContractError::LogicReject {
                reason,
                ..
            } = r
            {
                Reject::new(reason).unwrap_abort()
            } else {
                r.into()
            }
        })?
        .1;

    match return_value {
        Some(mut rv) => {
            let mut rv_buffer = vec![0; rv.size() as usize];
            rv.read_exact(&mut rv_buffer)?;
            Ok(RawReturnValue(Some(rv_buffer)))
        }
        None => Ok(RawReturnValue(None)),
    }
}

// Simple helper functions to ensure that a call comes from the implementation
// or the proxy.

fn only_implementation(
    implementation: Option<ContractAddress>,
    sender: Address,
) -> ContractResult<()> {
    let implementation_address = implementation
        .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyImplementation))?;
    ensure!(
        sender.matches_contract(&implementation_address),
        concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyImplementation)
    );

    Ok(())
}

fn only_proxy(proxy: Option<ContractAddress>, sender: Address) -> ContractResult<()> {
    let proxy_address =
        proxy.ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyProxy))?;
    ensure!(
        sender.matches_contract(&proxy_address),
        concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyProxy)
    );

    Ok(())
}

// Getter and setter functions

/// Set paused.
#[receive(contract = "CIS2-wCCD-State", name = "setPaused", parameter = "SetPausedParams", mutable)]
fn contract_state_set_paused<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    // Only implementation can set state.
    only_implementation(host.state().implementation_address, ctx.sender())?;

    // Set paused.
    let params: SetPausedParams = ctx.parameter_cursor().get()?;
    host.state_mut().paused = params.paused;
    Ok(())
}

/// Set implementation_address. Only the proxy can invoke this function.
/// The admin on the proxy will initiate the `updateImplementation` function on
/// the proxy which will call this function.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "setImplementationAddress",
    parameter = "SetImplementationAddressParams",
    mutable
)]
fn contract_state_set_implementation_address<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    // Only proxy can update the implementation address.
    only_proxy(host.state().proxy_address, ctx.sender())?;

    // Set implementation address.
    let params: SetImplementationAddressParams = ctx.parameter_cursor().get()?;
    host.state_mut().implementation_address = Some(params.implementation_address);
    Ok(())
}

/// Set balance.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "setBalance",
    parameter = "SetBalanceParams",
    mutable
)]
fn contract_state_set_balance<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    // Only implementation can set state.
    only_implementation(host.state().implementation_address, ctx.sender())?;

    let (state, state_builder) = host.state_and_builder();

    // Set balance.
    let params: SetBalanceParams = ctx.parameter_cursor().get()?;

    let mut owner_state = state.token.entry(params.owner).or_insert_with(|| AddressState {
        balance:   0u64.into(),
        operators: state_builder.new_set(),
    });

    match params.update {
        Update::Add => owner_state.balance += params.amount,
        Update::Remove => owner_state.balance -= params.amount,
    };

    Ok(())
}

/// Set operator.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "setIsOperator",
    parameter = "SetIsOperatorParams",
    mutable
)]
fn contract_state_set_operator<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    // Only implementation can set state.
    only_implementation(host.state().implementation_address, ctx.sender())?;

    // Set balance.
    let params: SetIsOperatorParams = ctx.parameter_cursor().get()?;

    match params.update {
        Update::Add => {
            let (state, state_builder) = host.state_and_builder();

            let mut owner_state = state.token.entry(params.owner).or_insert_with(|| AddressState {
                balance:   0u64.into(),
                operators: state_builder.new_set(),
            });
            owner_state.operators.insert(params.operator);
        }
        Update::Remove => {
            host.state_mut().token.entry(params.owner).and_modify(|address_state| {
                address_state.operators.remove(&params.operator);
            });
        }
    };

    Ok(())
}

/// Get paused.
#[receive(contract = "CIS2-wCCD-State", name = "getPaused", return_value = "bool")]
fn contract_state_get_paused<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<bool> {
    Ok(host.state().paused)
}

/// Get Balance.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "getBalance",
    parameter = "GetBalanceParams",
    return_value = "ContractTokenAmount"
)]
fn contract_state_get_balance<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<ContractTokenAmount> {
    let params: GetBalanceParams = ctx.parameter_cursor().get()?;

    if let Some(s) = host.state().token.get(&params.owner) {
        Ok(s.balance)
    } else {
        Ok(0u64.into())
    }
}

/// Is_operator.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "isOperator",
    parameter = "IsOperatorParams",
    return_value = "bool"
)]
fn contract_state_get_operator<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<bool> {
    let params: IsOperatorParams = ctx.parameter_cursor().get()?;

    Ok(host
        .state()
        .token
        .get(&params.owner)
        .map_or(false, |address_state| address_state.operators.contains(&params.address)))
}

/// Function to receive CCD on the implementation. All CCDs are held by the
/// proxy contract. Nonetheless, during the `unwrap` function the proxy should
/// send some CCD amount back to the implementation which then goes through
/// additional logic to deal with sending the CCD to the receiver address.
#[receive(contract = "CIS2-wCCD", name = "receiveCCD", payable)]
fn contract_implementation_recieve_ccd<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    _host: &impl HasHost<StateImplementation, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {
    Ok(())
}

/// Function to receive CCD on the proxy. All CCDs are held by the
/// proxy contract.
#[receive(contract = "CIS2-wCCD-Proxy", name = "receiveCCD", payable)]
fn contract_proxy_recieve_ccd<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    _host: &impl HasHost<StateProxy, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {
    Ok(())
}

/// Function to access the CCD on the proxy. Only the implementation can access
/// the funds.
#[receive(
    contract = "CIS2-wCCD-Proxy",
    parameter = "TransferCCDParams",
    name = "transferCCD",
    mutable
)]
fn contract_proxy_transfer_ccd<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateProxy, StateApiType = S>,
) -> ContractResult<()> {
    // Only implementation can access ccds on proxy.
    only_implementation(Some(host.state().implementation_address), ctx.sender())?;

    let params: TransferCCDParams = ctx.parameter_cursor().get()?;

    // Funds are sent to the implementation which then further sends them
    // in the `unwrap` function to the receiver.
    let implementation = host.state().implementation_address;
    host.invoke_contract_raw(
        &implementation,
        Parameter(&[]),
        EntrypointName::new_unchecked("receiveCCD"),
        Amount::from_micro_ccd(params.amount.into()),
    )?;

    Ok(())
}

/// This function is meant for recovering CCD tokens in the future. In case some
/// CCD tokens are accidentally sent to the `state` contract we can upgrade the
/// `implementation` contract to access the CCD via this function if necessary.
#[receive(
    contract = "CIS2-wCCD-State",
    parameter = "TransferCCDParams",
    name = "transferCCD",
    mutable
)]
fn contract_state_transfer_ccd<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    // Only implementation can access ccds on the state contract.
    only_implementation(host.state().implementation_address, ctx.sender())?;

    let params: TransferCCDParams = ctx.parameter_cursor().get()?;

    let implementation = host.state().implementation_address.unwrap();
    host.invoke_contract_raw(
        &implementation,
        Parameter(&[]),
        EntrypointName::new_unchecked("receiveCCD"),
        Amount::from_micro_ccd(params.amount.into()),
    )?;

    Ok(())
}

/// This function is meant for recovering CCD tokens in the future by the admin.
/// In case some CCD tokens are accidentally sent to the `implementation`
/// contract the admin can access the CCD via this function if necessary.
#[receive(
    contract = "CIS2-wCCD",
    parameter = "TransferCCDImplementationParams",
    name = "transferCCD",
    mutable
)]
fn contract_implementation_transfer_ccd<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    // Check that only the admin is authorized.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    let params: TransferCCDImplementationParams = ctx.parameter_cursor().get()?;

    host.invoke_transfer(&params.account, Amount::from_micro_ccd(params.amount.into()))?;

    Ok(())
}

/// Function to view contract balance.
#[receive(contract = "CIS2-wCCD-State", name = "viewBalance", return_value = "Amount")]
fn contract_state_view_balance<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<Amount> {
    Ok(host.self_balance())
}

/// Function to view contract balance.
#[receive(contract = "CIS2-wCCD", name = "viewBalance", return_value = "Amount")]
fn contract_view_balance<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<Amount> {
    Ok(host.self_balance())
}

/// Function to view contract balance.
#[receive(contract = "CIS2-wCCD-Proxy", name = "viewBalance", return_value = "Amount")]
fn contract_proxy_view_balance<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<StateProxy, StateApiType = S>,
) -> ContractResult<Amount> {
    Ok(host.self_balance())
}

/// Function to view state of contract.
#[receive(contract = "CIS2-wCCD-State", name = "view", return_value = "ReturnBasicState")]
fn contract_state_view<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<ReturnBasicState> {
    let proxy_address = host
        .state()
        .proxy_address
        .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::NotInitialized))?;

    let implementation_address = host
        .state()
        .implementation_address
        .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::NotInitialized))?;

    let state = ReturnBasicState {
        proxy_address,
        implementation_address,
    };
    Ok(state)
}

/// Function to view state of contract.
#[receive(contract = "CIS2-wCCD", name = "view", return_value = "StateImplementation")]
fn contract_implementation_view<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<StateImplementation> {
    let state_implementation = StateImplementation {
        admin:         host.state().admin,
        proxy_address: host.state().proxy_address,
        state_address: host.state().state_address,
    };
    Ok(state_implementation)
}

/// Function to view state of contract.
#[receive(contract = "CIS2-wCCD-Proxy", name = "view", return_value = "StateProxy")]
fn contract_proxy_view<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<StateProxy, StateApiType = S>,
) -> ContractResult<StateProxy> {
    let state_proxy = StateProxy {
        admin:                  host.state().admin,
        implementation_address: host.state().implementation_address,
        state_address:          host.state().state_address,
    };
    Ok(state_proxy)
}

/// Helper function to ensure contract is not paused.
fn when_not_paused<S>(
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    let state_address = host
        .state()
        .state_address
        .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::StateInvokeError))?;

    let paused = host.invoke_contract_raw_read_only(
        &state_address,
        Parameter(&[]),
        EntrypointName::new_unchecked("getPaused"),
        Amount::zero(),
    )?;

    // It is expected that this contract is initialized with the w_ccd_state
    // contract (a V1 contract). In that case, the paused variable can be
    // queried from the state contract without error.
    let paused: bool = paused
        .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::StateInvokeError))?
        .get()?;
    // Check that contract is not paused.
    ensure!(!paused, concordium_cis2::Cis2Error::Custom(CustomContractError::ContractPaused));
    Ok(())
}

/// Wrap an amount of CCD into wCCD tokens and transfer the tokens if the sender
/// is not the receiver.
#[receive(contract = "CIS2-wCCD", name = "wrap", enable_logger, mutable, payable)]
fn contract_wrap<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
    amount: Amount,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Can be only called through the fallback function on the proxy.
    only_proxy(host.state().proxy_address, ctx.sender())?;

    // Check that contract is not paused.
    when_not_paused(host)?;
    if amount == Amount::zero() {
        return Ok(());
    }

    let input: WrapParamsWithSender = ctx.parameter_cursor().get()?;

    // Get the sender who invoked this contract function.
    let sender = input.sender;

    let receive_address = input.params.to.address();

    let proxy_address = host
        .state()
        .proxy_address
        .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::ProxyInvokeError))?;

    // Proxy holds CCD funds. CCD is sent to proxy.
    host.invoke_contract_raw(
        &proxy_address,
        Parameter(&[]),
        EntrypointName::new_unchecked("receiveCCD"),
        amount,
    )?;

    let owner = receive_address;

    let set_balance_params = SetBalanceParams {
        owner,
        amount: amount.micro_ccd.into(),
        update: Update::Add,
    };

    let parameter_bytes = to_bytes(&set_balance_params);

    let state_address = host
        .state()
        .state_address
        .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyState))?;

    // Update state.
    host.invoke_contract_raw(
        &state_address,
        Parameter(&parameter_bytes),
        EntrypointName::new_unchecked("setBalance"),
        Amount::zero(),
    )?;

    // Log the newly minted tokens.
    logger.log(&Cis2Event::Mint(MintEvent {
        token_id: TOKEN_ID_WCCD,
        amount:   ContractTokenAmount::from(amount.micro_ccd),
        owner:    sender,
    }))?;

    // Only logs a transfer event if the receiver is not the sender.
    // Only executes the `OnReceivingCis2` hook if the receiver is not the sender
    // and the receiver is a contract.
    if sender != receive_address {
        logger.log(&Cis2Event::Transfer(TransferEvent {
            token_id: TOKEN_ID_WCCD,
            amount:   ContractTokenAmount::from(amount.micro_ccd),
            from:     sender,
            to:       receive_address,
        }))?;

        // If the receiver is a contract: invoke the receive hook function.
        if let Receiver::Contract(address, function) = input.params.to {
            let parameter = OnReceivingCis2Params {
                token_id: TOKEN_ID_WCCD,
                amount:   ContractTokenAmount::from(amount.micro_ccd),
                from:     sender,
                data:     input.params.data,
            };
            host.invoke_contract(
                &address,
                &parameter,
                function.as_entrypoint_name(),
                Amount::zero(),
            )
            .unwrap_abort();
        }
    }
    Ok(())
}

/// Unwrap an amount of wCCD tokens into CCD
#[receive(contract = "CIS2-wCCD", name = "unwrap", enable_logger, mutable)]
fn contract_unwrap<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Can be only called through the fallback function on the proxy.
    only_proxy(host.state().proxy_address, ctx.sender())?;

    // Check that contract is not paused.
    when_not_paused(host)?;

    let input: UnwrapParamsWithSender = ctx.parameter_cursor().get()?;

    if input.params.amount == 0u64.into() {
        return Ok(());
    }

    // Get the sender who invoked this contract function.
    let sender = input.sender;
    //  let state = host.state_mut();
    ensure!(
        sender == input.params.owner
            || host
                .state()
                .is_operator(&sender, &input.params.owner, host)
                .map_or(false, |is_operator| is_operator),
        ContractError::Unauthorized
    );

    // Update the state.

    let token_balance = host.state().balance(&TOKEN_ID_WCCD, &input.params.owner, host)?;

    ensure!(token_balance >= input.params.amount, ContractError::InsufficientFunds);

    let set_balance_params = SetBalanceParams {
        owner:  input.params.owner,
        amount: input.params.amount,
        update: Update::Remove,
    };

    let parameter_bytes = to_bytes(&set_balance_params);

    let state_address = host
        .state()
        .state_address
        .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyState))?;

    host.invoke_contract_raw(
        &state_address,
        Parameter(&parameter_bytes),
        EntrypointName::new_unchecked("setBalance"),
        Amount::zero(),
    )?;

    let params2: TransferCCDParams = TransferCCDParams {
        amount: input.params.amount,
    };

    let parameter_bytes = to_bytes(&params2);

    let proxy_address = host
        .state()
        .proxy_address
        .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyProxy))?;

    // Access/Request CCD funds from proxy.
    host.invoke_contract_raw(
        &proxy_address,
        Parameter(&parameter_bytes),
        EntrypointName::new_unchecked("transferCCD"),
        Amount::zero(),
    )?;

    let unwrapped_amount = Amount::from_micro_ccd(input.params.amount.into());

    // Send CCD to receiver.
    match input.params.receiver {
        Receiver::Account(address) => host.invoke_transfer(&address, unwrapped_amount)?,
        Receiver::Contract(address, function) => {
            host.invoke_contract(
                &address,
                &input.params.data,
                function.as_entrypoint_name(),
                unwrapped_amount,
            )?;
        }
    }

    // Log the burning of tokens.
    logger.log(&Cis2Event::Burn(BurnEvent {
        token_id: TOKEN_ID_WCCD,
        amount:   input.params.amount,
        owner:    input.params.owner,
    }))?;

    Ok(())
}

// Contract functions required by CIS2

pub type TransferParameter = TransferParams<ContractTokenId, ContractTokenAmount>;

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
#[receive(contract = "CIS2-wCCD", name = "transfer", enable_logger, mutable)]
fn contract_transfer<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Can be only called through the fallback function on the proxy.
    only_proxy(host.state().proxy_address, ctx.sender())?;

    // Check that contract is not paused.
    when_not_paused(host)?;

    // Parse the parameter.
    let input: TransferParameterWithSender = ctx.parameter_cursor().get()?;

    let TransferParams(transfers) = input.params;

    for Transfer {
        token_id,
        amount,
        from,
        to,
        data,
    } in transfers
    {
        // Get the sender who invoked this contract function.
        let sender = input.sender;

        // Authenticate the sender for this transfer
        ensure!(
            from == sender
                || host
                    .state()
                    .is_operator(&sender, &from, host)
                    .map_or(false, |is_operator| is_operator),
            ContractError::Unauthorized
        );
        let to_address = to.address();
        // Update the contract state

        if amount == 0u64.into() {
            return Ok(());
        }

        // Update the state.

        let token_balance = host.state().balance(&TOKEN_ID_WCCD, &from, host)?;

        ensure!(token_balance >= amount, ContractError::InsufficientFunds);
        {
            let set_balance_params = SetBalanceParams {
                owner: from,
                amount,
                update: Update::Remove,
            };

            let parameter_bytes = to_bytes(&set_balance_params);

            let state_address = host
                .state()
                .state_address
                .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyState))?;

            host.invoke_contract_raw(
                &state_address,
                Parameter(&parameter_bytes),
                EntrypointName::new_unchecked("setBalance"),
                Amount::zero(),
            )?;
        }

        let set_balance_params = SetBalanceParams {
            owner: to_address,
            amount,
            update: Update::Add,
        };

        let parameter_bytes = to_bytes(&set_balance_params);

        let state_address = host
            .state()
            .state_address
            .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyState))?;

        host.invoke_contract_raw(
            &state_address,
            Parameter(&parameter_bytes),
            EntrypointName::new_unchecked("setBalance"),
            Amount::zero(),
        )?;

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

/// Enable or disable addresses as operators of the sender address.
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Fails to log event.
#[receive(contract = "CIS2-wCCD", name = "updateOperator", enable_logger, mutable)]
fn contract_update_operator<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Can be only called through the fallback function on the proxy.
    only_proxy(host.state().proxy_address, ctx.sender())?;

    // Check that contract is not paused.
    when_not_paused(host)?;

    // Parse the parameter.
    let input: UpdateOperatorParamsWithSender = ctx.parameter_cursor().get()?;

    let UpdateOperatorParams(params) = input.params;

    for param in params {
        // Get the sender who invoked this contract function.
        let sender = input.sender;

        // Update the operator in the state.

        match param.update {
            OperatorUpdate::Add => {
                let set_operator_params = SetIsOperatorParams {
                    owner:    sender,
                    operator: param.operator,
                    update:   Update::Add,
                };

                let parameter_bytes = to_bytes(&set_operator_params);

                let state_address = host
                    .state()
                    .state_address
                    .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyState))?;

                host.invoke_contract_raw(
                    &state_address,
                    Parameter(&parameter_bytes),
                    EntrypointName::new_unchecked("setIsOperator"),
                    Amount::zero(),
                )?;
            }

            OperatorUpdate::Remove => {
                let set_operator_params = SetIsOperatorParams {
                    owner:    sender,
                    operator: param.operator,
                    update:   Update::Remove,
                };

                let parameter_bytes = to_bytes(&set_operator_params);

                let state_address = host
                    .state()
                    .state_address
                    .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyState))?;

                host.invoke_contract_raw(
                    &state_address,
                    Parameter(&parameter_bytes),
                    EntrypointName::new_unchecked("setIsOperator"),
                    Amount::zero(),
                )?;
            }
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

/// This functions allows the admin of the implementation to transfer the
/// address to a new admin.
#[receive(contract = "CIS2-wCCD", name = "updateAdmin", mutable)]
fn contract_implementation_update_admin<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    // Check that only the old admin is authorized to update the admin address.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);
    // Parse the parameter.
    let new_admin = ctx.parameter_cursor().get()?;
    // Update admin.
    host.state_mut().admin = new_admin;
    Ok(())
}

/// This functions allows the admin of the proxy to transfer the address to a
/// new admin.
#[receive(contract = "CIS2-wCCD-Proxy", name = "updateAdmin", mutable)]
fn contract_proxy_update_admin<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateProxy, StateApiType = S>,
) -> ContractResult<()> {
    // Check that only the old admin is authorized to update the admin address.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);
    // Parse the parameter.
    let new_admin = ctx.parameter_cursor().get()?;
    // Update admin.
    host.state_mut().admin = new_admin;
    Ok(())
}

/// Function to update the protocol with a new implementation.
/// Only the admin on the proxy can call this function.
#[receive(
    contract = "CIS2-wCCD-Proxy",
    name = "updateImplementation",
    parameter = "SetImplementationAddressParams",
    mutable
)]
fn contract_update_implementation<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateProxy, StateApiType = S>,
) -> ContractResult<()> {
    // Check that only the proxy admin is authorized to update the implementation
    // address.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);
    // Parse the parameter.
    let params: SetImplementationAddressParams = ctx.parameter_cursor().get()?;
    // Update implementation.
    host.state_mut().implementation_address = params.implementation_address;

    let set_implementation_address_params = SetImplementationAddressParams {
        implementation_address: params.implementation_address,
    };

    let parameter_bytes = to_bytes(&set_implementation_address_params);

    let state_address = host.state().state_address;

    // Update implementation in the state contract.
    host.invoke_contract_raw(
        &state_address,
        Parameter(&parameter_bytes),
        EntrypointName::new_unchecked("setImplementationAddress"),
        Amount::zero(),
    )?;

    Ok(())
}

/// This function pauses the contract. Only the
/// admin of the implementation can call this function.
#[receive(contract = "CIS2-wCCD", name = "pause", mutable)]
fn contract_pause<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    // Check that only the current admin can pause.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    let parameter_bytes = to_bytes(&SetPausedParams {
        paused: true,
    });

    let state_address = host
        .state()
        .state_address
        .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyState))?;

    host.invoke_contract_raw(
        &state_address,
        Parameter(&parameter_bytes),
        EntrypointName::new_unchecked("setPaused"),
        Amount::zero(),
    )?;

    Ok(())
}

/// Function to unpause the contract by the admin.
#[receive(contract = "CIS2-wCCD", name = "unPause", mutable)]
fn contract_un_pause<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    // Check that only the current admin can un_pause.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    let parameter_bytes = to_bytes(&SetPausedParams {
        paused: false,
    });

    let state_address = host
        .state()
        .state_address
        .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyState))?;

    host.invoke_contract_raw(
        &state_address,
        Parameter(&parameter_bytes),
        EntrypointName::new_unchecked("setPaused"),
        Amount::zero(),
    )?;

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
    host: &impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<ContractBalanceOfQueryResponse> {
    // Parse the parameter.
    let params: ContractBalanceOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for balance.
        let amount = host.state().balance(&query.token_id, &query.address, host)?;
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
    host: &impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<OperatorOfQueryResponse> {
    // Parse the parameter.
    let params: OperatorOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for address being an operator of owner.
        let is_operator = host
            .state()
            .is_operator(&query.address, &query.owner, host)
            .map_or(false, |is_operator| is_operator);
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
    _host: &impl HasHost<StateImplementation, StateApiType = S>,
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
    const OTHER_ACCOUNT: AccountAddress = AccountAddress([2u8; 32]);
    const OTHER_ADDRESS: Address = Address::Account(OTHER_ACCOUNT);
    const ADMIN_ACCOUNT: AccountAddress = AccountAddress([3u8; 32]);
    const ADMIN_ADDRESS: Address = Address::Account(ADMIN_ACCOUNT);
    const NEW_ADMIN_ACCOUNT: AccountAddress = AccountAddress([4u8; 32]);
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
    const NEW_IMPLEMENTATION: ContractAddress = ContractAddress {
        index:    4,
        subindex: 0,
    };

    fn expect_error<E, T>(expr: Result<T, E>, err: E, msg: &str)
    where
        E: Eq + Debug,
        T: Debug, {
        let actual = expr.expect_err_report(msg);
        claim_eq!(actual, err);
    }

    /// Test helper function which creates a w_ccd_proxy contract state
    fn initial_state_proxy() -> StateProxy {
        StateProxy {
            admin:                  ADMIN_ADDRESS,
            implementation_address: IMPLEMENTATION,
            state_address:          STATE,
        }
    }

    /// Test helper function which creates a w_ccd_implementation contract state
    fn initial_state_implementation() -> StateImplementation {
        StateImplementation::new(ADMIN_ADDRESS)
    }

    /// Test helper function which creates a w_ccd_state contract state
    fn initial_state_state<S: HasStateApi>(state_builder: &mut StateBuilder<S>) -> State<S> {
        State::new(state_builder)
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

        let mut host = TestHost::new(state, builder);

        // Setup parameter.
        let initialize_state_params = InitializeStateParams {
            proxy_address:          PROXY,
            implementation_address: IMPLEMENTATION,
        };
        let parameter_bytes = to_bytes(&initialize_state_params);

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

        // Can not initialize again.
        let result: ContractResult<()> = contract_state_initialize(&ctx, &mut host);
        // Check that invoke failed.
        expect_error(
            result,
            concordium_cis2::Cis2Error::Custom(CustomContractError::AlreadyInitialized),
            "Can not initialize again",
        );
    }

    /// Test set unpause time in state contract.
    #[concordium_test]
    fn test_set_paused() {
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Setup the context.
        let mut ctx = TestReceiveContext::empty();

        // Setup parameter.
        let initialize_state_params = InitializeStateParams {
            proxy_address:          PROXY,
            implementation_address: IMPLEMENTATION,
        };
        let parameter_bytes = to_bytes(&initialize_state_params);

        ctx.set_parameter(&parameter_bytes);
        ctx.set_sender(concordium_std::Address::Contract(IMPLEMENTATION));

        // Initialize the state contract.
        let result: ContractResult<()> = contract_state_initialize(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Setup the parameter.
        let parameter_bytes = to_bytes(&SetPausedParams {
            paused: true,
        });
        ctx.set_parameter(&parameter_bytes);

        // Check return value of the get_paused function
        let paused: ContractResult<bool> = contract_state_get_paused(&ctx, &host);
        claim_eq!(
            paused,
            Ok(false),
            "Getter function should return that the contract is not paused"
        );

        // Call the contract function.
        let result: ContractResult<()> = contract_state_set_paused(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check return value of the get_paused function
        let paused: ContractResult<bool> = contract_state_get_paused(&ctx, &host);
        claim_eq!(paused, Ok(true), "Getter function should return that contract is paused");

        // Can NOT set_paused from an address other than the implementation
        ctx.set_sender(ADDRESS_0);
        let result: ContractResult<()> = contract_state_set_paused(&ctx, &mut host);
        // Check that invoke failed.
        expect_error(
            result,
            concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyImplementation),
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

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

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
        ctx.set_sender(ADMIN_ADDRESS);

        let mut logger = TestLogger::init();
        let state_builder = TestStateBuilder::new();
        let state = StateImplementation::new(ADMIN_ADDRESS);

        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: PROXY,
            state_address: STATE,
        };
        let parameter_bytes = to_bytes(&initialize_implementation_params);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getPaused".into()),
            MockFn::returning_ok(false),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getBalance".into()),
            MockFn::returning_ok(ContractTokenAmount::from(400)),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("setBalance".into()),
            MockFn::returning_ok(()),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getBalance".into()),
            MockFn::returning_ok(ContractTokenAmount::from(400)),
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

        let transfer_params = TransferParameterWithSender {
            params: parameter,
            sender: ADDRESS_0,
        };

        let parameter_bytes = to_bytes(&transfer_params);
        ctx.set_parameter(&parameter_bytes);

        ctx.set_sender(concordium_std::Address::Contract(PROXY));

        // Call the contract function.
        let result: ContractResult<()> = contract_transfer(&ctx, &mut host, &mut logger);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getBalance".into()),
            MockFn::returning_ok(ContractTokenAmount::from(300)),
        );
        let balance0 = host
            .state()
            .balance(&TOKEN_ID_WCCD, &ADDRESS_0, &host)
            .expect_report("Token is expected to exist");
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getBalance".into()),
            MockFn::returning_ok(ContractTokenAmount::from(100)),
        );
        let balance1 = host
            .state()
            .balance(&TOKEN_ID_WCCD, &ADDRESS_1, &host)
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
        ctx.set_sender(ADMIN_ADDRESS);

        let mut logger = TestLogger::init();
        let state_builder = TestStateBuilder::new();
        let state = initial_state_implementation();
        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: PROXY,
            state_address: STATE,
        };
        let parameter_bytes = to_bytes(&initialize_implementation_params);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getPaused".into()),
            MockFn::returning_ok(false),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("isOperator".into()),
            MockFn::returning_ok(false),
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

        let transfer_params = TransferParameterWithSender {
            params: parameter,
            sender: OTHER_ADDRESS,
        };

        let parameter_bytes = to_bytes(&transfer_params);
        ctx.set_parameter(&parameter_bytes);

        ctx.set_parameter(&parameter_bytes);
        ctx.set_sender(concordium_std::Address::Contract(PROXY));

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
        ctx.set_sender(ADMIN_ADDRESS);

        let mut logger = TestLogger::init();
        let state_builder = TestStateBuilder::new();
        let state = initial_state_implementation();

        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: PROXY,
            state_address: STATE,
        };
        let parameter_bytes = to_bytes(&initialize_implementation_params);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getPaused".into()),
            MockFn::returning_ok(false),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("setBalance".into()),
            MockFn::returning_ok(()),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getBalance".into()),
            MockFn::returning_ok(ContractTokenAmount::from(400)),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("setIsOperator".into()),
            MockFn::returning_ok(()),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("isOperator".into()),
            MockFn::returning_ok(true),
        );

        // Setup parameter.
        let update = UpdateOperator {
            operator: concordium_std::Address::Contract(PROXY),
            update:   OperatorUpdate::Add,
        };

        let parameter = UpdateOperatorParams(vec![update]);

        let update_operator_params = UpdateOperatorParamsWithSender {
            params: parameter,
            sender: ADDRESS_0,
        };

        let parameter_bytes = to_bytes(&update_operator_params);
        ctx.set_parameter(&parameter_bytes);

        ctx.set_parameter(&parameter_bytes);
        ctx.set_sender(concordium_std::Address::Contract(PROXY));

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_update_operator(&ctx, &mut host, &mut logger);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Setup the parameter.
        let transfer = Transfer {
            from:     ADDRESS_0,
            to:       Receiver::from_account(ACCOUNT_1),
            token_id: TOKEN_ID_WCCD,
            amount:   ContractTokenAmount::from(100),
            data:     AdditionalData::empty(),
        };

        let parameter = TransferParams::from(vec![transfer]);

        let transfer_params = TransferParameterWithSender {
            params: parameter,
            sender: ADDRESS_0,
        };

        let parameter_bytes = to_bytes(&transfer_params);
        ctx.set_parameter(&parameter_bytes);

        // Call the contract function.
        let result: ContractResult<()> = contract_transfer(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getBalance".into()),
            MockFn::returning_ok(ContractTokenAmount::from(300)),
        );
        // Check the state.
        let balance0 = host
            .state()
            .balance(&TOKEN_ID_WCCD, &ADDRESS_0, &host)
            .expect_report("Token is expected to exist");
        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getBalance".into()),
            MockFn::returning_ok(ContractTokenAmount::from(100)),
        );
        let balance1 = host
            .state()
            .balance(&TOKEN_ID_WCCD, &ADDRESS_1, &host)
            .expect_report("Token is expected to exist");
        claim_eq!(balance0, 300.into()); //, "Token owner balance should be decreased by the transferred amount");
        claim_eq!(
            balance1,
            100.into(),
            "Token receiver balance should be increased by the transferred amount"
        );

        // Check the logs.
        claim_eq!(logger.logs.len(), 2, "Only one event should be logged");
        claim_eq!(
            logger.logs[1],
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
        ctx.set_sender(ADMIN_ADDRESS);

        let mut logger = TestLogger::init();
        let state_builder = TestStateBuilder::new();
        let state = initial_state_implementation();
        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: PROXY,
            state_address: STATE,
        };
        let parameter_bytes = to_bytes(&initialize_implementation_params);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getPaused".into()),
            MockFn::returning_ok(false),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("isOperator".into()),
            MockFn::returning_ok(true),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("setIsOperator".into()),
            MockFn::returning_ok(()),
        );

        // Setup parameter.
        let update = UpdateOperator {
            operator: ADDRESS_1,
            update:   OperatorUpdate::Add,
        };

        let parameter = UpdateOperatorParams(vec![update]);

        let update_operator_params = UpdateOperatorParamsWithSender {
            params: parameter,
            sender: ADDRESS_0,
        };

        let parameter_bytes = to_bytes(&update_operator_params);
        ctx.set_parameter(&parameter_bytes);

        ctx.set_sender(concordium_std::Address::Contract(PROXY));

        // Call the contract function.
        let result: ContractResult<()> = contract_update_operator(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        claim!(
            host.state()
                .is_operator(&ADDRESS_1, &ADDRESS_0, &host)
                .map_or(false, |is_operator| is_operator),
            "Account should be an operator"
        );

        // Checking that `ADDRESS_1` is an operator in the query response of the
        // `contract_operator_of` function as well.
        // Setup parameter.
        let operator_of_query = OperatorOfQuery {
            address: ADDRESS_1,
            owner:   ADDRESS_0,
        };

        let operator_of_query_vector = OperatorOfQueryParams {
            queries: vec![operator_of_query],
        };
        let parameter_bytes = to_bytes(&operator_of_query_vector);

        ctx.set_parameter(&parameter_bytes);

        // Checking the return value of the `contract_operator_of` function
        let result: ContractResult<OperatorOfQueryResponse> = contract_operator_of(&ctx, &host);

        claim_eq!(
            result.expect_report("Failed getting result value").0,
            [true],
            "Account should be an operator in the query response"
        );

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
        );
    }

    /// Test pause contract.
    #[concordium_test]
    fn test_pause() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_implementation();
        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: PROXY,
            state_address: STATE,
        };
        let parameter_bytes = to_bytes(&initialize_implementation_params);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("setPaused".into()),
            MockFn::returning_ok(()),
        );

        // Call the contract function.
        let result: ContractResult<()> = contract_pause(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");
    }

    /// Test that only the current admin can pause the contract.
    #[concordium_test]
    fn test_pause_not_authorized() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        // NEW_ADMIN is not the current admin but tries to pause.
        ctx.set_sender(NEW_ADMIN_ADDRESS);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_implementation();
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> = contract_pause(&ctx, &mut host);
        // Check that invoke failed.
        expect_error(
            result,
            ContractError::Unauthorized,
            "Pause should fail because not the current admin tries to invoke it",
        );
    }

    /// Test un_pause contract.
    #[concordium_test]
    fn test_un_pause() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_implementation();
        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: PROXY,
            state_address: STATE,
        };
        let parameter_bytes = to_bytes(&initialize_implementation_params);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("setPaused".into()),
            MockFn::returning_ok(()),
        );

        // UnPausing contract
        let result: ContractResult<()> = contract_un_pause(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");
    }

    /// Test that only the current admin can un_pause.
    #[concordium_test]
    fn test_un_pause_not_authorized() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        // NEW_ADMIN is not the current admin but tries to un_pause the contract.
        ctx.set_sender(NEW_ADMIN_ADDRESS);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_implementation();
        let mut host = TestHost::new(state, state_builder);

        // UnPausing contract.
        let result: ContractResult<()> = contract_un_pause(&ctx, &mut host);
        // Check that invoke failed.
        expect_error(
            result,
            ContractError::Unauthorized,
            "Un_pause should fail because not the current admin tries to invoke it",
        );
    }

    /// Test that one can NOT wrap when contract is paused.
    #[concordium_test]
    fn test_no_wrap_when_paused() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_implementation();
        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: PROXY,
            state_address: STATE,
        };
        let parameter_bytes = to_bytes(&initialize_implementation_params);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getPaused".into()),
            MockFn::returning_ok(true),
        );

        // Setup parameter.
        let wrap_params = WrapParamsWithSender {
            params: WrapParams {
                to:   Receiver::from_account(ACCOUNT_1),
                data: AdditionalData::empty(),
            },
            sender: ADDRESS_0,
        };

        let parameter_bytes = to_bytes(&wrap_params);
        ctx.set_parameter(&parameter_bytes);
        ctx.set_sender(concordium_std::Address::Contract(PROXY));

        let mut logger = TestLogger::init();
        let amount = Amount::from_micro_ccd(100);

        // Trying to invoke the wrap entrypoint. It will revert because the function is
        // paused.
        let result: ContractResult<()> = contract_wrap(&ctx, &mut host, amount, &mut logger);
        // Check that contract is paused.
        expect_error(
            result,
            concordium_cis2::Cis2Error::Custom(CustomContractError::ContractPaused),
            "Wrap should fail because contract is paused",
        );
    }

    /// Test un_wrap.
    #[concordium_test]
    fn test_un_wrap() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_implementation();
        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: PROXY,
            state_address: STATE,
        };
        let parameter_bytes = to_bytes(&initialize_implementation_params);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getPaused".into()),
            MockFn::returning_ok(false),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            PROXY,
            OwnedEntrypointName::new_unchecked("receiveCCD".into()),
            MockFn::returning_ok(()),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            PROXY,
            OwnedEntrypointName::new_unchecked("transferCCD".into()),
            MockFn::returning_ok(()),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("setBalance".into()),
            MockFn::returning_ok(()),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getBalance".into()),
            MockFn::returning_ok(ContractTokenAmount::from(100)),
        );

        // Setup parameter.
        let wrap_params = WrapParamsWithSender {
            params: WrapParams {
                to:   Receiver::from_account(ACCOUNT_0),
                data: AdditionalData::empty(),
            },
            sender: ADDRESS_0,
        };

        let parameter_bytes = to_bytes(&wrap_params);
        ctx.set_parameter(&parameter_bytes);
        ctx.set_sender(concordium_std::Address::Contract(PROXY));

        let mut logger = TestLogger::init();
        let amount = Amount::from_micro_ccd(100);
        host.set_self_balance(amount);

        // Account_0 wraps some CCD.
        let result: ContractResult<()> = contract_wrap(&ctx, &mut host, amount, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Setup parameter.
        let un_wrap_params = UnwrapParamsWithSender {
            params: UnwrapParams {
                amount:   ContractTokenAmount::from(100),
                owner:    ADDRESS_0,
                receiver: Receiver::from_account(ACCOUNT_0),
                data:     AdditionalData::empty(),
            },
            sender: ADDRESS_0,
        };

        let parameter_bytes = to_bytes(&un_wrap_params);
        ctx.set_parameter(&parameter_bytes);

        host.set_self_balance(amount);
        let mut logger = TestLogger::init();

        // Trying to invoke the un_wrap entrypoint.
        let result: ContractResult<()> = contract_unwrap(&ctx, &mut host, &mut logger);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");
    }

    /// Test that one can NOT un_wrap when contract is paused.
    #[concordium_test]
    fn test_no_un_wrap_when_paused() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_implementation();
        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: PROXY,
            state_address: STATE,
        };
        let parameter_bytes = to_bytes(&initialize_implementation_params);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getPaused".into()),
            MockFn::returning_ok(false),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            PROXY,
            OwnedEntrypointName::new_unchecked("receiveCCD".into()),
            MockFn::returning_ok(()),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("setBalance".into()),
            MockFn::returning_ok(()),
        );

        // Setup parameter.
        let wrap_params = WrapParamsWithSender {
            params: WrapParams {
                to:   Receiver::from_account(ACCOUNT_1),
                data: AdditionalData::empty(),
            },
            sender: ADDRESS_0,
        };

        let parameter_bytes = to_bytes(&wrap_params);
        ctx.set_parameter(&parameter_bytes);
        ctx.set_sender(concordium_std::Address::Contract(PROXY));

        let mut logger = TestLogger::init();
        let amount = Amount::from_micro_ccd(100);
        host.set_self_balance(amount);

        // Account_1 wraps some CCD.
        let result: ContractResult<()> = contract_wrap(&ctx, &mut host, amount, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getPaused".into()),
            MockFn::returning_ok(true),
        );

        // Setup parameter.
        let un_wrap_params = UnwrapParams {
            amount:   ContractTokenAmount::from(100),
            owner:    ADDRESS_1,
            receiver: Receiver::from_account(ACCOUNT_1),
            data:     AdditionalData::empty(),
        };
        let parameter_bytes = to_bytes(&un_wrap_params);
        ctx.set_parameter(&parameter_bytes);

        host.set_self_balance(amount);
        let mut logger = TestLogger::init();

        // Trying to invoke the un_wrap entrypoint. It will revert because the function
        // is paused.
        let result: ContractResult<()> = contract_unwrap(&ctx, &mut host, &mut logger);
        // Check that contract is paused.
        expect_error(
            result,
            concordium_cis2::Cis2Error::Custom(CustomContractError::ContractPaused),
            "Un_wrap should fail because contract is paused",
        );
    }

    /// Test that one can NOT transfer when contract is paused.
    #[concordium_test]
    fn test_no_transfer_when_paused() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

        let mut logger = TestLogger::init();
        let state_builder = TestStateBuilder::new();
        let state = StateImplementation::new(ADMIN_ADDRESS);
        let mut host = TestHost::new(state, state_builder);

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getBalance".into()),
            MockFn::returning_ok(ContractTokenAmount::from(400)),
        );

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: PROXY,
            state_address: STATE,
        };
        let parameter_bytes = to_bytes(&initialize_implementation_params);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getPaused".into()),
            MockFn::returning_ok(true),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getBalance".into()),
            MockFn::returning_ok(ContractTokenAmount::from(400)),
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

        ctx.set_sender(concordium_std::Address::Contract(PROXY));

        // Call the contract function.
        let result: ContractResult<()> = contract_transfer(&ctx, &mut host, &mut logger);

        // Check that contract is paused.
        expect_error(
            result,
            concordium_cis2::Cis2Error::Custom(CustomContractError::ContractPaused),
            "Transfer should fail because contract is paused",
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getBalance".into()),
            MockFn::returning_ok(ContractTokenAmount::from(400)),
        );
        // Check the state.
        let balance0 = host
            .state()
            .balance(&TOKEN_ID_WCCD, &ADDRESS_0, &host)
            .expect_report("Token is expected to exist");
        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getBalance".into()),
            MockFn::returning_ok(ContractTokenAmount::from(0)),
        );
        let balance1 = host
            .state()
            .balance(&TOKEN_ID_WCCD, &ADDRESS_1, &host)
            .expect_report("Token is expected to exist");
        claim_eq!(balance0, 400.into(), "Token owner balance should be still the same");
        claim_eq!(balance1, 0.into(), "Token receiver balance should be still the same");
    }

    /// Test that one can NOT update operator when contract is paused.
    #[concordium_test]
    fn test_no_add_operator_when_paused() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

        let mut logger = TestLogger::init();
        let state_builder = TestStateBuilder::new();
        let state = initial_state_implementation();
        let mut host = TestHost::new(state, state_builder);

        // Setup parameter.
        let initialize_implementation_params = InitializeImplementationParams {
            proxy_address: PROXY,
            state_address: STATE,
        };
        let parameter_bytes = to_bytes(&initialize_implementation_params);
        ctx.set_parameter(&parameter_bytes);

        // Initialize the implementation contract.
        let result: ContractResult<()> = contract_initialize(&ctx, &mut host);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getPaused".into()),
            MockFn::returning_ok(true),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("isOperator".into()),
            MockFn::returning_ok(false),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("isOperator".into()),
            MockFn::returning_ok(false),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("setBalance".into()),
            MockFn::returning_ok(()),
        );

        // Setup parameter.
        let update = UpdateOperator {
            operator: ADDRESS_1,
            update:   OperatorUpdate::Add,
        };
        let parameter = UpdateOperatorParams(vec![update]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);
        ctx.set_sender(concordium_std::Address::Contract(PROXY));

        // Call the contract function.
        let result: ContractResult<()> = contract_update_operator(&ctx, &mut host, &mut logger);

        // Check that contract is paused.
        expect_error(
            result,
            concordium_cis2::Cis2Error::Custom(CustomContractError::ContractPaused),
            "Update_operator should fail because contract is paused",
        );

        // Check the state.
        claim!(
            !host
                .state()
                .is_operator(&ADDRESS_1, &ADDRESS_0, &host)
                .map_or(false, |is_operator| is_operator),
            "Account should not be an operator"
        );
    }

    /// Test updating to new admin address on the implementation contract.
    #[concordium_test]
    fn test_implementation_update_admin() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[NEW_ADMIN_ADDRESS]);
        ctx.set_parameter(&parameter_bytes);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_implementation();
        let mut host = TestHost::new(state, state_builder);

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be the old admin address");

        // Call the contract function.
        let result: ContractResult<()> = contract_implementation_update_admin(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the admin state.
        claim_eq!(host.state().admin, NEW_ADMIN_ADDRESS, "Admin should be the new admin address");
    }

    /// Test updating to new admin address on the proxy contract.
    #[concordium_test]
    fn test_proxy_update_admin() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[NEW_ADMIN_ADDRESS]);
        ctx.set_parameter(&parameter_bytes);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_proxy();
        let mut host = TestHost::new(state, state_builder);

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be the old admin address");

        // Call the contract function.
        let result: ContractResult<()> = contract_proxy_update_admin(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the admin state.
        claim_eq!(host.state().admin, NEW_ADMIN_ADDRESS, "Admin should be the new admin address");
    }

    /// Test that only the current admin can update the admin address on the
    /// implementation contract.
    #[concordium_test]
    fn test_implementation_update_admin_not_authorized() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        // NEW_ADMIN is not the current admin but tries to update the admin variable to
        // its own address.
        ctx.set_sender(NEW_ADMIN_ADDRESS);

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[NEW_ADMIN_ADDRESS]);
        ctx.set_parameter(&parameter_bytes);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_implementation();
        let mut host = TestHost::new(state, state_builder);

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be the old admin address");

        // Call the contract function.
        let result: ContractResult<()> = contract_implementation_update_admin(&ctx, &mut host);
        // Check that invoke failed.
        expect_error(
            result,
            ContractError::Unauthorized,
            "Update admin should fail because not the current admin tries to update",
        );

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be still the old admin address");
    }

    /// Test that only the current admin can update the admin address on the
    /// proxy contract.
    #[concordium_test]
    fn test_proxy_update_admin_not_authorized() {
        // Setup the context.
        let mut ctx = TestReceiveContext::empty();
        // NEW_ADMIN is not the current admin but tries to update the admin variable to
        // its own address.
        ctx.set_sender(NEW_ADMIN_ADDRESS);

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[NEW_ADMIN_ADDRESS]);
        ctx.set_parameter(&parameter_bytes);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_proxy();
        let mut host = TestHost::new(state, state_builder);

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be the old admin address");

        // Call the contract function.
        let result: ContractResult<()> = contract_proxy_update_admin(&ctx, &mut host);
        // Check that invoke failed.
        expect_error(
            result,
            ContractError::Unauthorized,
            "Update admin should fail because not the current admin tries to update",
        );

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be still the old admin address");
    }

    /// Test updating to new admin address on the proxy contract.
    #[concordium_test]
    fn test_contract_update_implementation() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[NEW_IMPLEMENTATION]);
        ctx.set_parameter(&parameter_bytes);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_proxy();
        let mut host = TestHost::new(state, state_builder);

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("setImplementationAddress".into()),
            MockFn::returning_ok(()),
        );

        // Check the admin state.
        claim_eq!(
            host.state().implementation_address,
            IMPLEMENTATION,
            "Implementation should be the old implementation address"
        );

        // Call the contract function.
        let result: ContractResult<()> = contract_update_implementation(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the admin state.
        claim_eq!(
            host.state().implementation_address,
            NEW_IMPLEMENTATION,
            "Implementation should be the new implementation address"
        );
    }

    /// Test fallback function.
    #[concordium_test]
    fn test_contract_fallback() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_proxy();
        let mut host = TestHost::new(state, state_builder);

        let entrypoint_implementation =
            OwnedEntrypointName::new_unchecked("some_entrypoint".into());

        ctx.set_named_entrypoint(entrypoint_implementation.clone());
        ctx.set_parameter(b"hello");

        host.setup_mock_entrypoint(
            IMPLEMENTATION,
            entrypoint_implementation,
            MockFn::new_v1(|parameter, _, &mut _, &mut _| {
                let rv = parameter.0.to_vec();
                let length = rv.len();

                let return_value = [&rv[0..length - 33], b", world!"].concat();

                Ok((false, RawReturnValue(Some(return_value))))
            }),
        );

        // Act
        let result = receive_fallback(&ctx, &mut host, Amount::zero());

        // Assert
        claim_eq!(result, Ok(RawReturnValue(Some(b"hello, world!".to_vec()))))
    }
}
