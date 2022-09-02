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
//! There is a front-end example in development here: https://github.com/Concordium/concordium-browser-wallet/pull/62
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

/// The initial metadata URL for the wCCD token.
/// The URL can be updated with the `setURL` function on the `implementation`.
const INITIAL_TOKEN_METADATA_URL: &str = "https://some.example/token/wccd";

// Types

/// Contract token amount type.
/// Since this contract is wrapping the CCD and the CCD can be represented as a
/// u64, we can specialize the token amount to u64 reducing module size and cost
/// of arithmetics.
type ContractTokenAmount = TokenAmountU64;

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

/// The parameter type for the state contract function `initialize`.
#[derive(Serialize, SchemaType)]
struct InitializeStateParams {
    /// Address of the w_ccd proxy contract.
    proxy_address:          ContractAddress,
    /// Address of the w_ccd implementation contract.
    implementation_address: ContractAddress,
}

/// The parameter type for the state contract function
/// `set_implementation_address`.
#[derive(Serialize, SchemaType)]
struct SetImplementationAddressParams {
    /// Address of the w_ccd implementation contract.
    implementation_address: ContractAddress,
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

// Tests

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    const ACCOUNT_0: AccountAddress = AccountAddress([0u8; 32]);
    const ADDRESS_0: Address = Address::Account(ACCOUNT_0);

    const IMPLEMENTATION: ContractAddress = ContractAddress {
        index:    1,
        subindex: 0,
    };
    const PROXY: ContractAddress = ContractAddress {
        index:    2,
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
}
