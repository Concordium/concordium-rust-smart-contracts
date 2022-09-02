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
//! tree/main/source/mainnet/smart-contracts/tutorials/wCCD/schemas.
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

/// The id of the wCCD token in this contract.
const TOKEN_ID_WCCD: ContractTokenId = TokenIdUnit();

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

/// The parameter type for the proxy contract function
/// `onReceivingCis2`.
#[derive(Serialize, SchemaType)]
struct OnReceivingCis2HookParams {
    /// Receiver smart contract.
    receiver:                 Receiver,
    /// Parameters sent to the receiver smart contract.
    on_receiving_cis2_params: OnReceivingCis2Params<ContractTokenId, ContractTokenAmount>,
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

/// This function executes the `OnReceivingCis2` hook
#[receive(contract = "CIS2-wCCD-Proxy", name = "onReceivingCis2", error = "ContractError", mutable)]
fn contract_proxy_on_receiving_cis2<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<StateProxy, StateApiType = S>,
) -> ContractResult<()> {
    // Only implementation can invoke the hook.
    only_implementation(host.state().implementation_address, ctx.sender())?;

    // Get OnReceivingCis2HookParams.
    let params: OnReceivingCis2HookParams = ctx.parameter_cursor().get()?;

    if let Receiver::Contract(address, function) = params.receiver {
        host.invoke_contract(
            &address,
            &params.on_receiving_cis2_params,
            function.as_entrypoint_name(),
            Amount::zero(),
        )?;
    }

    Ok(())
}

// Contract functions

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

// Getter and setter functions

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

// Contract functions required by CIS2

pub type TransferParameter = TransferParams<ContractTokenId, ContractTokenAmount>;

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

// Tests

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

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
            MockFn::returning_ok("https://some.example/token/wccd"),
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
                        url:  "https://some.example/token/wccd".to_string(),
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
