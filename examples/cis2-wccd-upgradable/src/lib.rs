//! Upgradable wCCD smart contract (Concordium's canonical wCCD
//! implementation following the CIS-2 standard)
//!
//! # Description
//! The token in this contract is a wrapped CCD (wCCD), meaning it holds a
//! one-to-one correspondence with the CCD. Compared to the other wCCD
//! example in this repo, this smart contract can be paused/unpaused
//! and upgraded by admin addresses.
//!
//! Note: The word 'address' refers to either an account address or a
//! contract address.
//!
//! As follows from the CIS-2 specification, the contract has a `transfer`
//! function for transferring an amount of a specific token type from one
//! address to another address. An address can enable and disable one or more
//! addresses as operators. An operator of some token owner address is allowed
//! to transfer or unwrap any tokens of the owner.
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
//! The protocol consists of three smart contracts (`proxy`, `implementation`,
//! and `state`). All state-mutative wCCD functions (e.g. `wrap`, `unwrap`,
//! `transfer`, and `updateOperator`) have to be invoked on the `proxy`
//! contract. The `proxy` will append the `sender` to the input parameters
//! so that the `implementation` can retrieve this information.
//! Invoking the state-mutative wCCD functions directly on the `implementation`
//! without going through the `proxy` fallback function will revert.
//! All non-state-mutative wCCD functions (e.g. `balanceOf`, `operatorOf`,
//! `supports` and `tokenMetadata`) can be queried on the `proxy` or the
//! `implementation`. While for testings it can be convenient to invoke
//! non-state-mutative wCCD functions on the `implementation` contract, you
//! should always invoke them on the `proxy` contract in production. When the
//! protocol is upgraded, the old `implementation` address becomes invalid, you
//! would need to update your production product to the new `implementation`
//! address.
//!
//! There is a corresponding tutorial for this smart contract available here:
//! https://developer.concordium.software/en/mainnet/smart-contracts/tutorials/wCCD/index.html
//! All schemas are available for download here: https://github.com/Concordium/concordium.github.io/
//! tree/main/source/mainnet/smart-contracts/tutorials/wCCD/schemas
//!
//! If you want to create a schema to invoke a state-mutative wCCD function
//! through the fallback function, add the respective `parameters` as attributes
//! to the fallback function. For example, add `WrapParams`, `UnwrapParams`,
//! `TransferParameter`, or `UpdateOperatorParams` as parameter to the
//! fallback function to create a schema for the `wrap`, `unwrap`,
//! `transfer`, and `updateOperator` function, respectively.
//!
//! Example using `WrapParams` to create a schema to invoke the
//! `wrap` function via the fallback function on the proxy:
//!
//! #[receive(contract = "CIS-2-wCCD-Proxy", fallback, parameter = "WrapParams",
//! mutable, payable)] fn receive_fallback<S: HasStateApi>( ... ) { ... }
//!
//! If you want to create a schema to invoke a non-state-mutative wCCD function
//! through the fallback function, add the respective `parameters` and
//! `return_values` as attributes to the fallback function.
//!
//! Example using `OperatorOfQueryParams` and `OperatorOfQueryResponse` to
//! create a schema to invoke the `operatorOf` function via the fallback
//! function:
//!
//! #[receive(contract = "CIS2-wCCD-Proxy", fallback, parameter =
//! "OperatorOfQueryParams", return_value = "OperatorOfQueryResponse", mutable,
//! payable)] fn receive_fallback<S: HasStateApi>( ... ) { ... }
//!
//! State-mutative wCCD functions need to retrieve the `sender` that was
//! appended by the fallback function. These functions use the parameter
//! type `ParamWithSender<T>` on the implementation. This type masks the
//! `sender` to any generic input parameter `T`.
//! Non-state-mutative wCCD function don't need to retrieve the `sender`
//! and nevertheless the sender was appended by the fallback function they can
//! use their usual input parameter. The last few bytes representing the
//! `sender` are just ignored. E.g. the `operatorOf` function uses
//! `OperatorOfQueryParams` and not `ParamWithSender<OperatorOfQueryParams>`
//! on the `implementation`.
//!
//! The admin address on the `proxy` can upgrade the protocol with
//! a new `implementation` contract by invoking the `updateImplementation`
//! function. This invoke will update the `protocol_addresses` to the new
//! `implementation` address in all contracts. The `proxy` and `state` contracts
//! can not be upgraded (change the logic/code). The state of the smart contract
//! is kept in the `state` contract. Only the `implementation` can mutate values
//! in the `state` contract (except for the `protocol_addresses`). All CCD funds
//! are on the `proxy` and all wCCD events are logged on `proxy`. The admin
//! address on the `implementation` can pause/unpause the protocol and set
//! implementors.
//!
//! Deploy the `state` and the `implementation` contract first by invoking their
//! respective `init` functions. Then, deploy the `proxy` contract and pass
//! the already deployed contract addresses into the proxy `init` function.
//! Then, call the `initialize` function on the `proxy` contract. This function
//! will call the `initialize` functions on the `state` as well as the
//! `implementation` contracts to set the remaining `protocol_addresses`.
#![cfg_attr(not(feature = "std"), no_std)]

use concordium_cis2::*;
use concordium_std::{fmt::Debug, *};

/// The id of the wCCD token in this contract.
const TOKEN_ID_WCCD: ContractTokenId = TokenIdUnit();

/// The initial metadata URL for the wCCD token.
/// The URL can be updated with the `setURL` function on the `implementation`.
const INITIAL_TOKEN_METADATA_URL: &str = "https://some.example/token/wccd";

/// List of supported standards by this contract address.
const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 2] =
    [CIS0_STANDARD_IDENTIFIER, CIS2_STANDARD_IDENTIFIER];

/// Tag for the NewAdmin event. The CIS-2 library already uses the
/// event tags from `u8::MAX` to `u8::MAX - 4`.
pub const TOKEN_NEW_ADMIN_EVENT_TAG: u8 = u8::MAX - 5;

/// Tag for the NewImplementation event.
pub const TOKEN_NEW_IMPLEMENTATION_EVENT_TAG: u8 = u8::MAX - 6;

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

/// This parameter is used as the return value of the fallback function.
#[derive(PartialEq, Eq, Debug)]
struct RawReturnValue(Vec<u8>);

impl Serial for RawReturnValue {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> { out.write_all(&self.0) }
}

/// Tagged events to be serialized for the event log.
enum WccdEvent {
    /// A new admin event.
    NewAdmin(NewAdminEvent),
    /// A new implementation event.
    NewImplementation(NewImplementationEvent),
}

impl Serial for WccdEvent {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        match self {
            WccdEvent::NewAdmin(event) => {
                out.write_u8(TOKEN_NEW_ADMIN_EVENT_TAG)?;
                event.serial(out)
            }
            WccdEvent::NewImplementation(event) => {
                out.write_u8(TOKEN_NEW_IMPLEMENTATION_EVENT_TAG)?;
                event.serial(out)
            }
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
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct AddressState<S> {
    /// The number of tokens owned by this address.
    balance:   ContractTokenAmount,
    /// The address which are currently enabled as operators for this token and
    /// this address.
    operators: StateSet<Address, S>,
}

/// The `state` contract state.
#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S> {
    /// Addresses of the protocol
    protocol_addresses: ProtocolAddressesState,
    /// The state of the one token.
    token:              StateMap<Address, AddressState<S>, S>,
    /// Map with contract addresses providing implementations of additional
    /// standards.
    implementors:       StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
    /// Contract is paused/unpaused.
    paused:             bool,
    /// The metadata URL for the wCCD token following the specification RFC1738.
    #[concordium(size_length = 2)]
    url:                String,
}

#[derive(Serialize, PartialEq, Clone)]
enum ProtocolAddressesState {
    UnInitialized,
    Initialized {
        /// Address of the w_ccd proxy contract.
        proxy_address:          ContractAddress,
        /// Address of the w_ccd implementation contract.
        implementation_address: ContractAddress,
    },
}

/// The `implementation` contract state.
#[derive(Serial, Deserial, Clone, SchemaType)]
struct StateImplementation {
    /// The admin address can pause/unpause the contract
    /// and set implementors.
    admin:              Address,
    /// Addresses of the protocol
    protocol_addresses: ProtocolAddressesImplementation,
}

#[derive(SchemaType, Serialize, PartialEq, Clone)]
enum ProtocolAddressesImplementation {
    UnInitialized,
    Initialized {
        /// Address of the w_ccd proxy contract.
        proxy_address: ContractAddress,
        /// Address of the w_ccd state contract.
        state_address: ContractAddress,
    },
}

/// The `proxy` contract state.
#[derive(Serial, Deserial, Clone, SchemaType)]
struct StateProxy {
    /// The admin address can upgrade the implementation contract.
    admin:                  Address,
    /// Address of the w_ccd implementation contract.
    implementation_address: ContractAddress,
    /// Address of the w_ccd state contract.
    state_address:          ContractAddress,
}

/// NewAdminEvent.
#[derive(Serial)]
struct NewAdminEvent {
    /// New admin address.
    new_admin: Address,
}

/// NewImplementationEvent.
#[derive(Serial)]
struct NewImplementationEvent {
    /// New implementation address.
    new_implementation: ContractAddress,
}

/// The parameter type for the contract function `unwrap`.
/// Takes an amount of tokens and unwraps the CCD and sends it to a receiver.
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
    /// will not log a transfer event.
    to:   Receiver,
    /// Some additional data bytes are used in the `OnReceivingCis2` hook. Only
    /// if the `Receiver` is a contract and the `Receiver` is not
    /// the invoker of the wrap function the receive hook function is
    /// executed. The `OnReceivingCis2` hook invokes the function entrypoint
    /// specified in the `Receiver` with these additional data bytes as
    /// part of the input parameters. This action allows the receiving smart
    /// contract to react to the credited wCCD amount.
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

/// The parameter type for the contract functions `transferCCD`.
#[derive(Serialize, SchemaType)]
struct TransferCCDParams {
    /// Amount of CCD to transfer.
    amount:  ContractTokenAmount,
    /// Address that receives the CCD.
    address: Receiver,
    /// If the `Receiver` is a contract the unwrapped CCD together with these
    /// additional data bytes are sent to the function entrypoint specified in
    /// the `Receiver`.
    data:    AdditionalData,
}

/// The parameter type for the contract function `setImplementors`.
/// Takes a standard identifier and list of contract addresses providing
/// implementations of this standard.
#[derive(Debug, Serialize, SchemaType)]
struct SetImplementorsParams {
    /// The identifier for the standard.
    id:           StandardIdentifierOwned,
    /// The addresses of the implementors of the standard.
    implementors: Vec<ContractAddress>,
}

/// The parameter type for the state contract function `setPaused`.
#[derive(Serialize, SchemaType)]
struct SetPausedParams {
    /// Contract is paused/unpaused.
    paused: bool,
}

/// The parameter type for the state contract and implementation contract
/// functions `setURL`.
#[derive(Serialize, SchemaType, Clone)]
struct SetURLParams {
    /// The URL following the specification RFC1738.
    #[concordium(size_length = 2)]
    url: String,
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

/// The parameter type for the state contract function `getImplementors`.
#[derive(Serialize, SchemaType)]
struct GetImplementorsParams {
    /// The identifier for the standard.
    id: StandardIdentifierOwned,
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
    /// Contract is paused/unpaused.
    paused:                 bool,
    /// The URL following the specification RFC1738.
    #[concordium(size_length = 2)]
    url:                    String,
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
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
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
    UnInitialized,
    /// Only implementation contract.
    OnlyImplementation,
    /// Only proxy contract.
    OnlyProxy,
    /// Raised when implementation/proxy can not invoke state contract.
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
    /// Creates the new state of the `state` contract with no one owning any
    /// tokens by default. The ProtocolAddressesState is uninitialized.
    /// The ProtocolAddressesState has to be set with the `initialize`
    /// function after the `proxy` contract is deployed.
    fn new(state_builder: &mut StateBuilder<S>) -> Self {
        // Setup state.
        State {
            protocol_addresses: ProtocolAddressesState::UnInitialized,
            token:              state_builder.new_map(),
            implementors:       state_builder.new_map(),
            paused:             false,
            url:                INITIAL_TOKEN_METADATA_URL.to_string(),
        }
    }
}

impl StateImplementation {
    /// Creates the new state of the `implementation` contract.
    /// The ProtocolAddressesState is uninitialized.
    /// The ProtocolAddressesState has to be set with the `initialize`
    /// function after the `proxy` contract is deployed.
    fn new(admin: Address) -> Self {
        // Setup state.
        StateImplementation {
            admin,
            protocol_addresses: ProtocolAddressesImplementation::UnInitialized,
        }
    }

    /// Get the current balance of a given token id for a given address.
    /// Results in an error if the token id does not exist in the state.
    fn balance<S>(
        &self,
        state_address: &ContractAddress,
        token_id: &ContractTokenId,
        owner: &Address,
        host: &impl HasHost<StateImplementation, StateApiType = S>,
    ) -> ContractResult<ContractTokenAmount> {
        ensure_eq!(token_id, &TOKEN_ID_WCCD, ContractError::InvalidTokenId);

        let balance = host.invoke_contract_read_only(
            state_address,
            owner,
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
    fn is_operator<S>(
        &self,
        state_address: &ContractAddress,
        address: &Address,
        owner: &Address,
        host: &impl HasHost<StateImplementation, StateApiType = S>,
    ) -> ContractResult<bool> {
        let is_operator = host.invoke_contract_read_only(
            state_address,
            &IsOperatorParams {
                owner:   *owner,
                address: *address,
            },
            EntrypointName::new_unchecked("isOperator"),
            Amount::zero(),
        )?;

        // It is expected that this contract is initialized with the w_ccd_state
        // contract (a V1 contract). In that case, the is_operator variable can be
        // queried from the state contract without error.
        let is_operator = is_operator
            .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::StateInvokeError))?
            .get()?;

        Ok(is_operator)
    }

    /// Check if state contains any implementors for a given standard.
    fn have_implementors<S>(
        &self,
        state_address: &ContractAddress,
        std_id: &StandardIdentifierOwned,
        host: &impl HasHost<StateImplementation, StateApiType = S>,
    ) -> ContractResult<SupportResult> {
        let implementors = host.invoke_contract_read_only(
            state_address,
            std_id,
            EntrypointName::new_unchecked("getImplementors"),
            Amount::zero(),
        )?;

        // It is expected that this contract is initialized with the w_ccd_state
        // contract (a V1 contract). In that case, the implementors can be
        // queried from the state contract without error.
        let implementors: Option<Vec<ContractAddress>> = implementors
            .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::StateInvokeError))?
            .get()?;

        if let Some(addresses) = implementors {
            Ok(SupportResult::SupportBy(addresses.to_vec()))
        } else {
            Ok(SupportResult::NoSupport)
        }
    }
}

/// This function logs an event.
#[receive(contract = "CIS2-wCCD-Proxy", name = "logEvent", error = "ContractError", enable_logger)]
fn contract_proxy_log_event<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<StateProxy, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Only implementation can log event.
    only_implementation(host.state().implementation_address, ctx.sender())?;

    let mut parameter_buffer = vec![0; ctx.parameter_cursor().size() as usize];
    ctx.parameter_cursor().read_exact(&mut parameter_buffer)?;

    // Log event.
    logger.log(&RawReturnValue(parameter_buffer))?;

    Ok(())
}

// Contract functions

/// Initialize the state contract instance with no initial tokens.
#[init(contract = "CIS2-wCCD-State")]
fn contract_state_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    // Construct the initial contract state.
    let state = State::new(state_builder);

    Ok(state)
}

/// Initialize the implementation contract. This function logs a new admin
/// event.
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

    // Log a new admin event.
    logger.log(&WccdEvent::NewAdmin(NewAdminEvent {
        new_admin: invoker,
    }))?;

    Ok(state)
}

/// Initializes the state of the w_ccd proxy contract with the state and the
/// implementation addresses. Both addresses have to be set together by calling
/// this function.
#[init(contract = "CIS2-wCCD-Proxy", parameter = "InitProxyParams")]
fn contract_proxy_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
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

/// Initializes the state w-ccd contract with the proxy and the
/// implementation addresses. Both addresses have to be set together
/// by calling this function. This function can only be called once.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "initialize",
    parameter = "InitializeStateParams",
    error = "ContractError",
    mutable
)]
fn contract_state_initialize<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    // Contract can only be initialized once.
    ensure_eq!(
        host.state().protocol_addresses,
        ProtocolAddressesState::UnInitialized,
        concordium_cis2::Cis2Error::Custom(CustomContractError::AlreadyInitialized)
    );

    // Set proxy and implementation addresses.
    let params: InitializeStateParams = ctx.parameter_cursor().get()?;

    host.state_mut().protocol_addresses = ProtocolAddressesState::Initialized {
        proxy_address:          params.proxy_address,
        implementation_address: params.implementation_address,
    };

    Ok(())
}

/// Initializes the implementation w-ccd contract with the proxy and
/// the state addresses. Both addresses have to be set together by
/// calling this function. This function can only be called once.
#[receive(
    contract = "CIS2-wCCD",
    name = "initialize",
    parameter = "InitializeImplementationParams",
    error = "ContractError",
    mutable
)]
fn contract_initialize<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    // Contract can only be initialized once.
    ensure_eq!(
        host.state().protocol_addresses,
        ProtocolAddressesImplementation::UnInitialized,
        concordium_cis2::Cis2Error::Custom(CustomContractError::AlreadyInitialized)
    );

    // Set proxy and storage addresses.
    let params: InitializeImplementationParams = ctx.parameter_cursor().get()?;

    host.state_mut().protocol_addresses = ProtocolAddressesImplementation::Initialized {
        proxy_address: params.proxy_address,
        state_address: params.state_address,
    };

    Ok(())
}

/// Initializes the `implementation` and `state` contracts by using the
/// addresses that the `proxy` contract was set up. This function will call the
/// `initialize` functions on the `implementation` as well as the `state`
/// contracts. This function logs a mint event with amount 0 to signal that a
/// new CIS-2 token was deployed. This function logs an event including the
/// metadata for this token. This function logs a new implementation event.
/// This function logs a new admin event.
#[receive(
    contract = "CIS2-wCCD-Proxy",
    name = "initialize",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_proxy_initialize<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateProxy, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    let state_address = host.state().state_address;

    host.invoke_contract(
        &state_address,
        &InitializeStateParams {
            proxy_address:          ctx.self_address(),
            implementation_address: host.state().implementation_address,
        },
        EntrypointName::new_unchecked("initialize"),
        Amount::zero(),
    )?;

    let implementation_address = host.state().implementation_address;

    host.invoke_contract(
        &implementation_address,
        &InitializeImplementationParams {
            proxy_address: ctx.self_address(),
            state_address: host.state().state_address,
        },
        EntrypointName::new_unchecked("initialize"),
        Amount::zero(),
    )?;

    // Log a `Mint` event for the single token id with 0 amount. Minting an amount
    // of 0 is used to signal that a new token was deployed. Invoking the mint event
    // with 0 amount in the `wrap` function is impossible.
    logger.log(&Cis2Event::Mint(MintEvent {
        token_id: TOKEN_ID_WCCD,
        amount:   ContractTokenAmount::from(0u64),
        owner:    ctx.sender(),
    }))?;

    let url = host.invoke_contract_read_only(
        &state_address,
        &Parameter(&[]),
        EntrypointName::new_unchecked("getURL"),
        Amount::zero(),
    )?;

    let url = url
        .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::StateInvokeError))?
        .get()?;

    // Log an event including the metadata for this token.
    logger.log(&Cis2Event::TokenMetadata::<_, ContractTokenAmount>(TokenMetadataEvent {
        token_id:     TOKEN_ID_WCCD,
        metadata_url: MetadataUrl {
            url,
            hash: None,
        },
    }))?;

    // Log a new implementation event.
    logger.log(&WccdEvent::NewImplementation(NewImplementationEvent {
        new_implementation: implementation_address,
    }))?;

    // Log a new admin event.
    logger.log(&WccdEvent::NewAdmin(NewAdminEvent {
        new_admin: host.state().admin,
    }))?;

    Ok(())
}

/// The fallback method, which redirects the invocations to the implementation.
#[receive(contract = "CIS2-wCCD-Proxy", error = "ContractError", fallback, mutable, payable)]
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

    // Forwarding the invoke unaltered to the implementation contract.
    let mut return_value = host
        .invoke_contract(
            &implementation,
            &paramter_with_sender,
            entrypoint.as_entrypoint_name(),
            amount,
        )
        .map_err(|r| {
            if let CallContractError::LogicReject {
                reason,
                mut return_value,
            } = r
            {
                let mut buffer = vec![0; return_value.size() as usize];
                return_value.read_exact(&mut buffer[..]).unwrap_abort(); // This should always be safe.
                let mut reject = Reject::new(reason).unwrap_abort();
                reject.return_value = Some(buffer);
                reject
            } else {
                r.into()
            }
        })?
        .1
        .unwrap_abort();

    let mut rv_buffer = vec![0; return_value.size() as usize];
    return_value.read_exact(&mut rv_buffer)?;
    Ok(RawReturnValue(rv_buffer))
}

// Simple helper functions to ensure that a call comes from the implementation
// or the proxy.

fn only_implementation(
    implementation_address: ContractAddress,
    sender: Address,
) -> ContractResult<()> {
    ensure!(
        sender.matches_contract(&implementation_address),
        concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyImplementation)
    );

    Ok(())
}

fn only_proxy(proxy_address: ContractAddress, sender: Address) -> ContractResult<()> {
    ensure!(
        sender.matches_contract(&proxy_address),
        concordium_cis2::Cis2Error::Custom(CustomContractError::OnlyProxy)
    );

    Ok(())
}

// Getter and setter functions

/// Set Implementors.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "setImplementors",
    parameter = "SetImplementorsParams",
    error = "ContractError",
    mutable
)]
fn contract_state_set_implementors<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    let (_proxy_address, implementation_address) = get_protocol_addresses_from_state(host)?;

    // Only implementation can set state.
    only_implementation(implementation_address, ctx.sender())?;

    // Set implementors.
    let params: SetImplementorsParams = ctx.parameter_cursor().get()?;

    host.state_mut().implementors.insert(params.id, params.implementors);
    Ok(())
}

/// Set paused.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "setPaused",
    parameter = "SetPausedParams",
    error = "ContractError",
    mutable
)]
fn contract_state_set_paused<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    let (_proxy_address, implementation_address) = get_protocol_addresses_from_state(host)?;

    // Only implementation can set state.
    only_implementation(implementation_address, ctx.sender())?;

    // Set paused.
    let params: SetPausedParams = ctx.parameter_cursor().get()?;
    host.state_mut().paused = params.paused;
    Ok(())
}

/// Set URL.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "setURL",
    parameter = "SetURLParams",
    error = "ContractError",
    mutable
)]
fn contract_state_set_url<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    let (_proxy_address, implementation_address) = get_protocol_addresses_from_state(host)?;

    // Only implementation can set state.
    only_implementation(implementation_address, ctx.sender())?;

    // Set URL.
    let params: SetURLParams = ctx.parameter_cursor().get()?;
    host.state_mut().url = params.url;
    Ok(())
}

/// Set implementation_address. Only the proxy can invoke this function.
/// The admin on the proxy will initiate the `updateImplementation` function on
/// the proxy which will invoke this function.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "setImplementationAddress",
    parameter = "SetImplementationAddressParams",
    error = "ContractError",
    mutable
)]
fn contract_state_set_implementation_address<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    let (proxy_address, _implementation_address) = get_protocol_addresses_from_state(host)?;

    // Only proxy can update the implementation address.
    only_proxy(proxy_address, ctx.sender())?;

    // Set implementation address.
    let params: SetImplementationAddressParams = ctx.parameter_cursor().get()?;

    host.state_mut().protocol_addresses = ProtocolAddressesState::Initialized {
        proxy_address,
        implementation_address: params.implementation_address,
    };

    Ok(())
}

/// Set balance.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "setBalance",
    parameter = "SetBalanceParams",
    error = "ContractError",
    mutable
)]
fn contract_state_set_balance<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    let (_proxy_address, implementation_address) = get_protocol_addresses_from_state(host)?;

    // Only implementation can set state.
    only_implementation(implementation_address, ctx.sender())?;

    // Set balance.
    let params: SetBalanceParams = ctx.parameter_cursor().get()?;

    let (state, state_builder) = host.state_and_builder();

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
    error = "ContractError",
    mutable
)]
fn contract_state_set_operator<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    let (_proxy_address, implementation_address) = get_protocol_addresses_from_state(host)?;

    // Only implementation can set state.
    only_implementation(implementation_address, ctx.sender())?;

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
#[receive(
    contract = "CIS2-wCCD-State",
    name = "getPaused",
    return_value = "bool",
    error = "ContractError"
)]
fn contract_state_get_paused<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<bool> {
    Ok(host.state().paused)
}

/// Get URL.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "getURL",
    return_value = "String",
    error = "ContractError"
)]
fn contract_state_get_url<'a, 'b, S: 'a + HasStateApi>(
    _ctx: &'b impl HasReceiveContext,
    host: &'a impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<&'a String> {
    Ok(&host.state().url)
}

/// Get Balance.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "getBalance",
    parameter = "GetBalanceParams",
    return_value = "ContractTokenAmount",
    error = "ContractError"
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

/// Get Implementors.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "getImplementors",
    parameter = "GetImplementorsParams",
    error = "ContractError"
)]
fn contract_state_get_implementors<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<Option<Vec<ContractAddress>>> {
    let params: GetImplementorsParams = ctx.parameter_cursor().get()?;

    if let Some(addresses) = host.state().implementors.get(&params.id) {
        Ok(Some(addresses.to_vec()))
    } else {
        Ok(None)
    }
}

/// Is_operator.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "isOperator",
    parameter = "IsOperatorParams",
    return_value = "bool",
    error = "ContractError"
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

/// Function to receive CCD on the proxy. All CCDs are held by the
/// proxy contract.
#[receive(contract = "CIS2-wCCD-Proxy", name = "receiveCCD", error = "ContractError", payable)]
fn contract_proxy_recieve_ccd<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<StateProxy, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {
    // Only implementation can send ccds to proxy.
    only_implementation(host.state().implementation_address, ctx.sender())?;

    Ok(())
}

/// Function to access the CCDs on the proxy. Only the implementation can access
/// the funds.
#[receive(
    contract = "CIS2-wCCD-Proxy",
    parameter = "TransferCCDParams",
    name = "transferCCD",
    error = "ContractError",
    mutable
)]
fn contract_proxy_transfer_ccd<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateProxy, StateApiType = S>,
) -> ContractResult<()> {
    // Only implementation can access CCDs on proxy.
    only_implementation(host.state().implementation_address, ctx.sender())?;

    let params: TransferCCDParams = ctx.parameter_cursor().get()?;

    let amount = Amount::from_micro_ccd(params.amount.into());

    // Send CCDs to receiver.
    match params.address {
        Receiver::Account(address) => host.invoke_transfer(&address, amount)?,
        Receiver::Contract(address, function) => {
            host.invoke_contract(&address, &params.data, function.as_entrypoint_name(), amount)?;
        }
    }

    Ok(())
}

/// This function is meant for recovering CCD tokens by the admin
/// in case they accidentally end up on the implementation.
/// Every smart contract instance with a payable function should have
/// some mechanism to recover funds as a good smart contract coding practice.
/// Nonetheless, it is not expected that any CCD tokens can end up
/// on the implementation since the `wrap` function forwards them to the proxy.
#[receive(
    contract = "CIS2-wCCD",
    parameter = "TransferCCDParams",
    error = "ContractError",
    name = "transferCCD",
    mutable
)]
fn contract_implementation_transfer_ccd<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    // Check that only the admin is authorized.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    let params: TransferCCDParams = ctx.parameter_cursor().get()?;

    let amount = Amount::from_micro_ccd(params.amount.into());

    match params.address {
        Receiver::Account(address) => host.invoke_transfer(&address, amount)?,
        Receiver::Contract(address, function) => {
            host.invoke_contract(&address, &params.data, function.as_entrypoint_name(), amount)?;
        }
    }

    Ok(())
}

/// Function to view contract balance of state contract.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "viewBalance",
    return_value = "Amount",
    error = "ContractError"
)]
fn contract_state_view_balance<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<Amount> {
    Ok(host.self_balance())
}

/// Function to view contract balance of implementation contract.
#[receive(
    contract = "CIS2-wCCD",
    name = "viewBalance",
    return_value = "Amount",
    error = "ContractError"
)]
fn contract_view_balance<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<Amount> {
    Ok(host.self_balance())
}

/// Function to view contract balance of proxy contract.
#[receive(
    contract = "CIS2-wCCD-Proxy",
    name = "viewBalance",
    return_value = "Amount",
    error = "ContractError"
)]
fn contract_proxy_view_balance<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<StateProxy, StateApiType = S>,
) -> ContractResult<Amount> {
    Ok(host.self_balance())
}

/// Function to view state of the state contract.
#[receive(
    contract = "CIS2-wCCD-State",
    name = "view",
    return_value = "ReturnBasicState",
    error = "ContractError"
)]
fn contract_state_view<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<ReturnBasicState> {
    let (proxy_address, implementation_address) = get_protocol_addresses_from_state(host)?;

    let state = ReturnBasicState {
        proxy_address,
        implementation_address,
        paused: host.state().paused,
        url: host.state().url.clone(),
    };
    Ok(state)
}

/// Function to view state of the implementation contract.
#[receive(
    contract = "CIS2-wCCD",
    name = "view",
    return_value = "StateImplementation",
    error = "ContractError"
)]
fn contract_implementation_view<'a, 'b, S: HasStateApi>(
    _ctx: &'b impl HasReceiveContext,
    host: &'a impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<&'a StateImplementation> {
    Ok(host.state())
}

/// Function to view state of the proxy contract.
#[receive(
    contract = "CIS2-wCCD-Proxy",
    name = "view",
    return_value = "StateProxy",
    error = "ContractError"
)]
fn contract_proxy_view<'a, 'b, S: HasStateApi>(
    _ctx: &'b impl HasReceiveContext,
    host: &'a impl HasHost<StateProxy, StateApiType = S>,
) -> ContractResult<&'a StateProxy> {
    Ok(host.state())
}

/// Helper function to get protocol addresses from the implementation contract.
fn get_protocol_addresses_from_implementation<S>(
    host: &impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<(ContractAddress, ContractAddress)> {
    if let ProtocolAddressesImplementation::Initialized {
        proxy_address,
        state_address,
    } = host.state().protocol_addresses
    {
        Ok((proxy_address, state_address))
    } else {
        bail!(concordium_cis2::Cis2Error::Custom(CustomContractError::UnInitialized))
    }
}

/// Helper function to get protocol addresses from the state contract.
fn get_protocol_addresses_from_state<S>(
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<(ContractAddress, ContractAddress)> {
    if let ProtocolAddressesState::Initialized {
        proxy_address,
        implementation_address,
    } = host.state().protocol_addresses
    {
        Ok((proxy_address, implementation_address))
    } else {
        bail!(concordium_cis2::Cis2Error::Custom(CustomContractError::UnInitialized));
    }
}

/// Helper function to ensure contract is not paused.
fn when_not_paused<S>(
    state_address: &ContractAddress,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    let paused = host.invoke_contract_read_only(
        state_address,
        &Parameter(&[]),
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
#[receive(contract = "CIS2-wCCD", name = "wrap", error = "ContractError", mutable, payable)]
fn contract_wrap<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
    amount: Amount,
) -> ContractResult<()> {
    let (proxy_address, state_address) = get_protocol_addresses_from_implementation(host)?;

    // Can be only called through the fallback function on the proxy.
    only_proxy(proxy_address, ctx.sender())?;

    // Check that contract is not paused.
    when_not_paused(&state_address, host)?;

    if amount == Amount::zero() {
        return Ok(());
    }

    let input: WrapParamsWithSender = ctx.parameter_cursor().get()?;

    // Get the sender who invoked this contract function.
    let sender = input.sender;

    let receive_address = input.params.to.address();

    // Proxy holds CCD funds. CCD is sent to proxy.
    host.invoke_contract(
        &proxy_address,
        &[8; 0],
        EntrypointName::new_unchecked("receiveCCD"),
        amount,
    )?;

    // Update state.
    host.invoke_contract(
        &state_address,
        &SetBalanceParams {
            owner:  receive_address,
            amount: amount.micro_ccd.into(),
            update: Update::Add,
        },
        EntrypointName::new_unchecked("setBalance"),
        Amount::zero(),
    )?;

    // Log the newly minted tokens.
    host.invoke_contract(
        &proxy_address,
        &Cis2Event::Mint(MintEvent {
            token_id: TOKEN_ID_WCCD,
            amount:   ContractTokenAmount::from(amount.micro_ccd),
            owner:    sender,
        }),
        EntrypointName::new_unchecked("logEvent"),
        Amount::zero(),
    )?;

    // Only logs a transfer event if the receiver is not the sender.
    // Only executes the `OnReceivingCis2` hook if the receiver is not the sender
    // and the receiver is a contract.
    if sender != receive_address {
        // Log the transfer event.
        host.invoke_contract(
            &proxy_address,
            &Cis2Event::Transfer(TransferEvent {
                token_id: TOKEN_ID_WCCD,
                amount:   ContractTokenAmount::from(amount.micro_ccd),
                from:     sender,
                to:       receive_address,
            }),
            EntrypointName::new_unchecked("logEvent"),
            Amount::zero(),
        )?;

        // If the receiver is a contract: invoke the receive hook function.
        if let Receiver::Contract(address, function) = input.params.to {
            host.invoke_contract(
                &address,
                &OnReceivingCis2Params {
                    token_id: TOKEN_ID_WCCD,
                    amount:   ContractTokenAmount::from(amount.micro_ccd),
                    from:     sender,
                    data:     input.params.data,
                },
                function.as_entrypoint_name(),
                Amount::zero(),
            )?;
        }
    }
    Ok(())
}

/// Unwrap an amount of wCCD tokens into CCD
#[receive(contract = "CIS2-wCCD", name = "unwrap", error = "ContractError", mutable)]
fn contract_unwrap<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    let (proxy_address, state_address) = get_protocol_addresses_from_implementation(host)?;

    // Can be only called through the fallback function on the proxy.
    only_proxy(proxy_address, ctx.sender())?;

    // Check that contract is not paused.
    when_not_paused(&state_address, host)?;

    let input: UnwrapParamsWithSender = ctx.parameter_cursor().get()?;

    if input.params.amount == 0u64.into() {
        return Ok(());
    }

    // Get the sender who invoked this contract function.
    let sender = input.sender;

    ensure!(
        sender == input.params.owner
            || host.state().is_operator(&state_address, &sender, &input.params.owner, host)?,
        ContractError::Unauthorized
    );

    // Update the state.

    let token_balance =
        host.state().balance(&state_address, &TOKEN_ID_WCCD, &input.params.owner, host)?;

    ensure!(token_balance >= input.params.amount, ContractError::InsufficientFunds);

    host.invoke_contract(
        &state_address,
        &SetBalanceParams {
            owner:  input.params.owner,
            amount: input.params.amount,
            update: Update::Remove,
        },
        EntrypointName::new_unchecked("setBalance"),
        Amount::zero(),
    )?;

    // Transfer CCD funds from proxy to the receiver address.
    host.invoke_contract(
        &proxy_address,
        &TransferCCDParams {
            amount:  input.params.amount,
            address: input.params.receiver,
            data:    input.params.data,
        },
        EntrypointName::new_unchecked("transferCCD"),
        Amount::zero(),
    )?;

    // Log the burn event.
    host.invoke_contract(
        &proxy_address,
        &Cis2Event::Burn(BurnEvent {
            token_id: TOKEN_ID_WCCD,
            amount:   input.params.amount,
            owner:    input.params.owner,
        }),
        EntrypointName::new_unchecked("logEvent"),
        Amount::zero(),
    )?;

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
#[receive(contract = "CIS2-wCCD", name = "transfer", error = "ContractError", mutable)]
fn contract_transfer<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    let (proxy_address, state_address) = get_protocol_addresses_from_implementation(host)?;

    // Can be only called through the fallback function on the proxy.
    only_proxy(proxy_address, ctx.sender())?;

    // Check that contract is not paused.
    when_not_paused(&state_address, host)?;

    // Parse the parameter.
    let input: TransferParameterWithSender = ctx.parameter_cursor().get()?;

    let TransferParams(transfers) = input.params;

    // Get the sender who invoked this contract function.
    let sender = input.sender;

    for Transfer {
        token_id,
        amount,
        from,
        to,
        data,
    } in transfers
    {
        // Authenticate the sender for this transfer
        ensure!(
            from == sender || host.state().is_operator(&state_address, &sender, &from, host)?,
            ContractError::Unauthorized
        );
        let to_address = to.address();

        if amount != 0u64.into() {
            // Update the state.

            let token_balance = host.state().balance(&state_address, &token_id, &from, host)?;

            ensure!(token_balance >= amount, ContractError::InsufficientFunds);
            {
                host.invoke_contract(
                    &state_address,
                    &SetBalanceParams {
                        owner: from,
                        amount,
                        update: Update::Remove,
                    },
                    EntrypointName::new_unchecked("setBalance"),
                    Amount::zero(),
                )?;
            }

            host.invoke_contract(
                &state_address,
                &SetBalanceParams {
                    owner: to_address,
                    amount,
                    update: Update::Add,
                },
                EntrypointName::new_unchecked("setBalance"),
                Amount::zero(),
            )?;
        }

        // If the receiver is a contract: invoke the receive hook function.
        if let Receiver::Contract(address, function) = to {
            host.invoke_contract(
                &address,
                &OnReceivingCis2Params {
                    token_id,
                    amount,
                    from,
                    data,
                },
                function.as_entrypoint_name(),
                Amount::zero(),
            )?;
        }

        // Log the transfer event.
        host.invoke_contract(
            &proxy_address,
            &Cis2Event::Transfer(TransferEvent {
                token_id: TOKEN_ID_WCCD,
                amount,
                from,
                to: to_address,
            }),
            EntrypointName::new_unchecked("logEvent"),
            Amount::zero(),
        )?;
    }
    Ok(())
}

/// Enable or disable addresses as operators of the sender address.
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Fails to log event.
#[receive(contract = "CIS2-wCCD", name = "updateOperator", error = "ContractError", mutable)]
fn contract_update_operator<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    let (proxy_address, state_address) = get_protocol_addresses_from_implementation(host)?;

    // Can be only called through the fallback function on the proxy.
    only_proxy(proxy_address, ctx.sender())?;

    // Check that contract is not paused.
    when_not_paused(&state_address, host)?;

    // Parse the parameter.
    let input: UpdateOperatorParamsWithSender = ctx.parameter_cursor().get()?;

    let UpdateOperatorParams(params) = input.params;

    // Get the sender who invoked this contract function.
    let sender = input.sender;

    for param in params {
        // Update the operator in the state.
        match param.update {
            OperatorUpdate::Add => {
                host.invoke_contract(
                    &state_address,
                    &SetIsOperatorParams {
                        owner:    sender,
                        operator: param.operator,
                        update:   Update::Add,
                    },
                    EntrypointName::new_unchecked("setIsOperator"),
                    Amount::zero(),
                )?;
            }

            OperatorUpdate::Remove => {
                host.invoke_contract(
                    &state_address,
                    &SetIsOperatorParams {
                        owner:    sender,
                        operator: param.operator,
                        update:   Update::Remove,
                    },
                    EntrypointName::new_unchecked("setIsOperator"),
                    Amount::zero(),
                )?;
            }
        };

        // Log the update operator event.
        host.invoke_contract(
            &proxy_address,
            &Cis2Event::<ContractTokenId, ContractTokenAmount>::UpdateOperator(
                UpdateOperatorEvent {
                    owner:    sender,
                    operator: param.operator,
                    update:   param.update,
                },
            ),
            EntrypointName::new_unchecked("logEvent"),
            Amount::zero(),
        )?;
    }

    Ok(())
}

/// This functions allows the admin of the implementation to transfer the
/// address to a new admin.
#[receive(
    contract = "CIS2-wCCD",
    name = "updateAdmin",
    parameter = "Address",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_implementation_update_admin<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Check that only the old admin is authorized to update the admin address.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);
    // Parse the parameter.
    let new_admin = ctx.parameter_cursor().get()?;
    // Update admin.
    host.state_mut().admin = new_admin;

    // Log a new admin event.
    logger.log(&WccdEvent::NewAdmin(NewAdminEvent {
        new_admin,
    }))?;

    Ok(())
}

/// This functions allows the admin of the proxy to transfer the address to a
/// new admin.
#[receive(
    contract = "CIS2-wCCD-Proxy",
    name = "updateAdmin",
    parameter = "Address",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_proxy_update_admin<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateProxy, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Check that only the old admin is authorized to update the admin address.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);
    // Parse the parameter.
    let new_admin = ctx.parameter_cursor().get()?;
    // Update admin.
    host.state_mut().admin = new_admin;

    // Log a new admin event.
    logger.log(&WccdEvent::NewAdmin(NewAdminEvent {
        new_admin,
    }))?;

    Ok(())
}

/// Set the addresses for an implementation given a standard identifier and a
/// list of contract addresses.
///
/// It rejects if:
/// - Sender is not the admin of the contract instance.
/// - It fails to parse the parameter.
#[receive(
    contract = "CIS2-wCCD",
    name = "setImplementors",
    parameter = "SetImplementorsParams",
    error = "ContractError",
    mutable
)]
fn contract_set_implementor<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    // Authorize the sender.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);
    // Parse the parameter.
    let params: SetImplementorsParams = ctx.parameter_cursor().get()?;

    let (_proxy_address, state_address) = get_protocol_addresses_from_implementation(host)?;

    // Update the implementors in the state
    host.invoke_contract(
        &state_address,
        &params,
        EntrypointName::new_unchecked("setImplementors"),
        Amount::zero(),
    )?;

    Ok(())
}

/// Function to update the protocol with a new implementation.
/// Only the admin on the proxy can call this function.
#[receive(
    contract = "CIS2-wCCD-Proxy",
    name = "updateImplementation",
    parameter = "SetImplementationAddressParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_proxy_update_implementation<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateProxy, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Check that only the proxy admin is authorized to update the implementation
    // address.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);
    // Parse the parameter.
    let params: SetImplementationAddressParams = ctx.parameter_cursor().get()?;
    // Update implementation.
    host.state_mut().implementation_address = params.implementation_address;

    let state_address = host.state().state_address;

    // Update implementation address in the state contract.
    host.invoke_contract(
        &state_address,
        &SetImplementationAddressParams {
            implementation_address: params.implementation_address,
        },
        EntrypointName::new_unchecked("setImplementationAddress"),
        Amount::zero(),
    )?;

    // Log a new implementation event.
    logger.log(&WccdEvent::NewImplementation(NewImplementationEvent {
        new_implementation: params.implementation_address,
    }))?;

    Ok(())
}

/// This function pauses the contract. Only the
/// admin of the implementation can call this function.
#[receive(contract = "CIS2-wCCD", name = "pause", error = "ContractError", mutable)]
fn contract_pause<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    // Check that only the current admin can pause.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    let (_proxy_address, state_address) = get_protocol_addresses_from_implementation(host)?;

    host.invoke_contract(
        &state_address,
        &SetPausedParams {
            paused: true,
        },
        EntrypointName::new_unchecked("setPaused"),
        Amount::zero(),
    )?;

    Ok(())
}

/// This function can be used to set a new URL. Only the
/// admin of the implementation can call this function.
#[receive(
    contract = "CIS2-wCCD",
    name = "setURL",
    parameter = "SetURLParams",
    error = "ContractError",
    mutable
)]
fn contract_set_url<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    // Check that only the current admin can set the url.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    // Parse the parameter.
    let params: SetURLParams = ctx.parameter_cursor().get()?;

    let (proxy_address, state_address) = get_protocol_addresses_from_implementation(host)?;

    host.invoke_contract(
        &state_address,
        &SetURLParams {
            url: params.url.clone(),
        },
        EntrypointName::new_unchecked("setURL"),
        Amount::zero(),
    )?;

    // Log an event including the metadata for this token.
    host.invoke_contract(
        &proxy_address,
        &Cis2Event::TokenMetadata::<_, ContractTokenAmount>(TokenMetadataEvent {
            token_id:     TOKEN_ID_WCCD,
            metadata_url: MetadataUrl {
                url:  params.url,
                hash: None,
            },
        }),
        EntrypointName::new_unchecked("logEvent"),
        Amount::zero(),
    )?;

    Ok(())
}

/// Function to unpause the contract by the admin.
#[receive(contract = "CIS2-wCCD", name = "unpause", error = "ContractError", mutable)]
fn contract_un_pause<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<()> {
    // Check that only the current admin can un_pause.
    ensure_eq!(ctx.sender(), host.state().admin, ContractError::Unauthorized);

    let (_proxy_address, state_address) = get_protocol_addresses_from_implementation(host)?;

    host.invoke_contract(
        &state_address,
        &SetPausedParams {
            paused: false,
        },
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
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "CIS2-wCCD",
    name = "balanceOf",
    parameter = "ContractBalanceOfQueryParams",
    return_value = "ContractBalanceOfQueryResponse",
    error = "ContractError"
)]
fn contract_balance_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<ContractBalanceOfQueryResponse> {
    // Parse the parameter.
    let params: ContractBalanceOfQueryParams = ctx.parameter_cursor().get()?;

    let (_proxy_address, state_address) = get_protocol_addresses_from_implementation(host)?;

    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for balance.
        let amount = host.state().balance(&state_address, &query.token_id, &query.address, host)?;
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
    contract = "CIS2-wCCD",
    name = "operatorOf",
    parameter = "OperatorOfQueryParams",
    return_value = "OperatorOfQueryResponse",
    error = "ContractError"
)]
fn contract_operator_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<OperatorOfQueryResponse> {
    // Parse the parameter.
    let params: OperatorOfQueryParams = ctx.parameter_cursor().get()?;

    let (_proxy_address, state_address) = get_protocol_addresses_from_implementation(host)?;

    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state if the `address` being an `operator` of `owner`.
        let is_operator =
            host.state().is_operator(&state_address, &query.address, &query.owner, host)?;
        response.push(is_operator);
    }
    let result = OperatorOfQueryResponse::from(response);
    Ok(result)
}

/// Get the supported standards or addresses for a implementation given list of
/// standard identifiers.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "CIS2-wCCD",
    name = "supports",
    parameter = "SupportsQueryParams",
    return_value = "SupportsQueryResponse",
    error = "ContractError"
)]
fn contract_supports<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<SupportsQueryResponse> {
    // Parse the parameter.
    let params: SupportsQueryParams = ctx.parameter_cursor().get()?;

    let (_proxy_address, state_address) = get_protocol_addresses_from_implementation(host)?;

    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for std_id in params.queries {
        if SUPPORTS_STANDARDS.contains(&std_id.as_standard_identifier()) {
            response.push(SupportResult::Support);
        } else {
            response.push(host.state().have_implementors(&state_address, &std_id, host)?);
        }
    }
    let result = SupportsQueryResponse::from(response);
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
    return_value = "TokenMetadataQueryResponse",
    error = "ContractError"
)]
fn contract_token_metadata<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<StateImplementation, StateApiType = S>,
) -> ContractResult<TokenMetadataQueryResponse> {
    // Parse the parameter.
    let params: ContractTokenMetadataQueryParams = ctx.parameter_cursor().get()?;

    let (_proxy_address, state_address) = get_protocol_addresses_from_implementation(host)?;

    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for token_id in params.queries {
        // Check the token exists.
        ensure_eq!(token_id, TOKEN_ID_WCCD, ContractError::InvalidTokenId);

        let url = host.invoke_contract_read_only(
            &state_address,
            &Parameter(&[]),
            EntrypointName::new_unchecked("getURL"),
            Amount::zero(),
        )?;

        let url = url
            .ok_or(concordium_cis2::Cis2Error::Custom(CustomContractError::StateInvokeError))?
            .get()?;

        let metadata_url = MetadataUrl {
            url,
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

    /// Test helper function which creates a w_ccd_state contract state
    fn initial_state_state<S: HasStateApi>(state_builder: &mut StateBuilder<S>) -> State<S> {
        State::new(state_builder)
    }

    /// Test helper function which creates a w_ccd_implementation contract state
    fn initial_state_implementation() -> StateImplementation {
        StateImplementation::new(ADMIN_ADDRESS)
    }

    /// Test helper function which creates a w_ccd_proxy contract state
    fn initial_state_proxy() -> StateProxy {
        StateProxy {
            admin:                  ADMIN_ADDRESS,
            implementation_address: IMPLEMENTATION,
            state_address:          STATE,
        }
    }

    /// Test events on proxy when contract is initialized.
    #[concordium_test]
    fn test_proxy_events_during_initialization() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);
        ctx.set_self_address(PROXY);

        let mut logger = TestLogger::init();
        let state_builder = TestStateBuilder::new();
        let state = initial_state_proxy();
        let mut host = TestHost::new(state, state_builder);

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getURL".into()),
            MockFn::returning_ok(INITIAL_TOKEN_METADATA_URL),
        );

        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("initialize".into()),
            MockFn::returning_ok(()),
        );

        // Set up a mock invocation for the implementation contract.
        host.setup_mock_entrypoint(
            IMPLEMENTATION,
            OwnedEntrypointName::new_unchecked("initialize".into()),
            MockFn::returning_ok(()),
        );

        // Initialize the proxy contract.
        let result: ContractResult<()> = contract_proxy_initialize(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the logs
        claim_eq!(logger.logs.len(), 4, "Exactly four events should be logged");
        claim!(
            logger.logs.contains(&to_bytes(&Cis2Event::Mint(MintEvent {
                owner:    ADMIN_ADDRESS,
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
                        url:  String::from(INITIAL_TOKEN_METADATA_URL),
                        hash: None,
                    },
                }
            ))),
            "Missing event with metadata for the token"
        );
        claim!(
            logger.logs.contains(&to_bytes(&WccdEvent::NewImplementation(
                NewImplementationEvent {
                    new_implementation: IMPLEMENTATION,
                }
            ))),
            "Missing event for the new implementation"
        );
        claim!(
            logger.logs.contains(&to_bytes(&WccdEvent::NewAdmin(NewAdminEvent {
                new_admin: ADMIN_ADDRESS,
            }))),
            "Missing event for the new admin"
        );
    }

    /// Test w_ccd state initialization works.
    #[concordium_test]
    fn test_state_init() {
        // Setup the context
        let mut ctx = TestInitContext::empty();
        ctx.set_init_origin(ACCOUNT_0);

        let mut builder = TestStateBuilder::new();

        // Call the contract function.
        let result = contract_state_init(&ctx, &mut builder);

        // Check the result
        let state = result.expect_report("Contract w_ccd state initialization failed");

        if let ProtocolAddressesState::UnInitialized = state.protocol_addresses {
        } else {
            claim!(false, "Implementation address should not be initialized");
        };

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
        if let ProtocolAddressesState::Initialized {
            implementation_address,
            proxy_address,
        } = host.state().protocol_addresses
        {
            claim_eq!(
                implementation_address,
                IMPLEMENTATION,
                "Implementation address should now be set"
            );

            claim_eq!(proxy_address, PROXY, "Proxy address should now be set");
        } else {
            claim!(false, "Implementation address should now be set");
        };

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
    }

    /// Test transfer succeeds, when `from` is the sender.
    #[concordium_test]
    fn test_transfer_account() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);

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

        // Set up a mock invocation for the proxy contract.
        host.setup_mock_entrypoint(
            PROXY,
            OwnedEntrypointName::new_unchecked("logEvent".into()),
            MockFn::returning_ok(()),
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
        let result: ContractResult<()> = contract_transfer(&ctx, &mut host);
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
            .balance(&STATE, &TOKEN_ID_WCCD, &ADDRESS_0, &host)
            .expect_report("Token is expected to exist");
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getBalance".into()),
            MockFn::returning_ok(ContractTokenAmount::from(100)),
        );
        let balance1 = host
            .state()
            .balance(&STATE, &TOKEN_ID_WCCD, &ADDRESS_1, &host)
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
    }

    /// Test transfer token fails, when sender is neither the owner or an
    /// operator of the owner.
    #[concordium_test]
    fn test_transfer_not_authorized() {
        // Setup the context
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
        let result: ContractResult<()> = contract_transfer(&ctx, &mut host);
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

        // Set up a mock invocation for the proxy contract.
        host.setup_mock_entrypoint(
            PROXY,
            OwnedEntrypointName::new_unchecked("logEvent".into()),
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
        let result: ContractResult<()> = contract_update_operator(&ctx, &mut host);
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
        let result: ContractResult<()> = contract_transfer(&ctx, &mut host);

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
            .balance(&STATE, &TOKEN_ID_WCCD, &ADDRESS_0, &host)
            .expect_report("Token is expected to exist");
        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getBalance".into()),
            MockFn::returning_ok(ContractTokenAmount::from(100)),
        );
        let balance1 = host
            .state()
            .balance(&STATE, &TOKEN_ID_WCCD, &ADDRESS_1, &host)
            .expect_report("Token is expected to exist");
        claim_eq!(balance0, 300.into()); //, "Token owner balance should be decreased by the transferred amount");
        claim_eq!(
            balance1,
            100.into(),
            "Token receiver balance should be increased by the transferred amount"
        );
    }

    /// Test adding an operator succeeds and the appropriate event is logged.
    #[concordium_test]
    fn test_add_operator() {
        // Setup the context
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

        // Set up a mock invocation for the proxy contract.
        host.setup_mock_entrypoint(
            PROXY,
            OwnedEntrypointName::new_unchecked("logEvent".into()),
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
        let result: ContractResult<()> = contract_update_operator(&ctx, &mut host);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        claim!(
            host.state()
                .is_operator(&STATE, &ADDRESS_1, &ADDRESS_0, &host)
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

        let amount = Amount::from_micro_ccd(100);

        // Trying to invoke the wrap entrypoint. It will revert because the function is
        // paused.
        let result: ContractResult<()> = contract_wrap(&ctx, &mut host, amount);
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

        // Set up a mock invocation for the proxy contract.
        host.setup_mock_entrypoint(
            PROXY,
            OwnedEntrypointName::new_unchecked("logEvent".into()),
            MockFn::returning_ok(()),
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

        let amount = Amount::from_micro_ccd(100);
        host.set_self_balance(amount);

        // Account_0 wraps some CCD.
        let result: ContractResult<()> = contract_wrap(&ctx, &mut host, amount);

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

        // Trying to invoke the un_wrap entrypoint.
        let result: ContractResult<()> = contract_unwrap(&ctx, &mut host);
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

        // Set up a mock invocation for the proxy contract.
        host.setup_mock_entrypoint(
            PROXY,
            OwnedEntrypointName::new_unchecked("logEvent".into()),
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

        let amount = Amount::from_micro_ccd(100);
        host.set_self_balance(amount);

        // Account_1 wraps some CCD.
        let result: ContractResult<()> = contract_wrap(&ctx, &mut host, amount);

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

        // Trying to invoke the un_wrap entrypoint. It will revert because the function
        // is paused.
        let result: ContractResult<()> = contract_unwrap(&ctx, &mut host);
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
        let result: ContractResult<()> = contract_transfer(&ctx, &mut host);

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
            .balance(&STATE, &TOKEN_ID_WCCD, &ADDRESS_0, &host)
            .expect_report("Token is expected to exist");
        // Set up a mock invocation for the state contract.
        host.setup_mock_entrypoint(
            STATE,
            OwnedEntrypointName::new_unchecked("getBalance".into()),
            MockFn::returning_ok(ContractTokenAmount::from(0)),
        );
        let balance1 = host
            .state()
            .balance(&STATE, &TOKEN_ID_WCCD, &ADDRESS_1, &host)
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
        let result: ContractResult<()> = contract_update_operator(&ctx, &mut host);

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
                .is_operator(&STATE, &ADDRESS_1, &ADDRESS_0, &host)
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
        let mut logger = TestLogger::init();

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[NEW_ADMIN_ADDRESS]);
        ctx.set_parameter(&parameter_bytes);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_implementation();
        let mut host = TestHost::new(state, state_builder);

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be the old admin address");

        // Call the contract function.
        let result: ContractResult<()> =
            contract_implementation_update_admin(&ctx, &mut host, &mut logger);

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
        let mut logger = TestLogger::init();

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[NEW_ADMIN_ADDRESS]);
        ctx.set_parameter(&parameter_bytes);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_proxy();
        let mut host = TestHost::new(state, state_builder);

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be the old admin address");

        // Call the contract function.
        let result: ContractResult<()> = contract_proxy_update_admin(&ctx, &mut host, &mut logger);

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
        let mut logger = TestLogger::init();

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[NEW_ADMIN_ADDRESS]);
        ctx.set_parameter(&parameter_bytes);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_implementation();
        let mut host = TestHost::new(state, state_builder);

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be the old admin address");

        // Call the contract function.
        let result: ContractResult<()> =
            contract_implementation_update_admin(&ctx, &mut host, &mut logger);
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
        let mut logger = TestLogger::init();

        // Setup the parameter.
        let parameter_bytes = to_bytes(&[NEW_ADMIN_ADDRESS]);
        ctx.set_parameter(&parameter_bytes);

        let state_builder = TestStateBuilder::new();
        let state = initial_state_proxy();
        let mut host = TestHost::new(state, state_builder);

        // Check the admin state.
        claim_eq!(host.state().admin, ADMIN_ADDRESS, "Admin should be the old admin address");

        // Call the contract function.
        let result: ContractResult<()> = contract_proxy_update_admin(&ctx, &mut host, &mut logger);
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
    fn test_contract_proxy_update_implementation() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADMIN_ADDRESS);
        let mut logger = TestLogger::init();

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
        let result: ContractResult<()> =
            contract_proxy_update_implementation(&ctx, &mut host, &mut logger);

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

                Ok((false, RawReturnValue(return_value)))
            }),
        );

        // Act
        let result = receive_fallback(&ctx, &mut host, Amount::zero());

        // Assert
        claim_eq!(result, Ok(RawReturnValue(b"hello, world!".to_vec())));
    }
}
