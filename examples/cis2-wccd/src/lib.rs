//! wCCD: An example implementation of CIS2 for a single fungible token.
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

#![cfg_attr(not(feature = "std"), no_std)]
use concordium_cis2::*;
use concordium_std::*;

/// The id of the wCCD token in this contract.
const TOKEN_ID_WCCD: ContractTokenId = TokenIdUnit();

/// List of supported standards by this contract address.
const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 2] =
    [CIS0_STANDARD_IDENTIFIER, CIS2_STANDARD_IDENTIFIER];

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
#[derive(Serial, DeserialWithState, Deletable, StateClone)]
#[concordium(state_parameter = "S")]
struct AddressState<S> {
    /// The number of tokens owned by this address.
    balance:   ContractTokenAmount,
    /// The address which are currently enabled as operators for this token and
    /// this address.
    operators: StateSet<Address, S>,
}

#[derive(Serialize, SchemaType, Clone)]
struct TestParams {
    metadata_url:                  String,
    fail_transfer:                 bool,
    fail_balance_of:               bool,
    fail_token_metadata:           bool,
    always_transfer_to:            Option<AccountAddress>, // fail_transfer takes precedence
    balance_of_returns_string:     bool,                   // fail_balance takes precedence
    token_metadata_returns_number: bool,                   // fail_metadata takes precedence
}

/// The contract state,
#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S> {
    /// The state the one token.
    token:        StateMap<Address, AddressState<S>, S>,
    /// Map with contract addresses providing implementations of additional
    /// standards.
    implementors: StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
    test_params:  TestParams,
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
    fn new(state_builder: &mut StateBuilder<S>, test_params: TestParams) -> Self {
        State {
            token: state_builder.new_map(),
            implementors: state_builder.new_map(),
            test_params,
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
    ) {
        let mut owner_state = self.token.entry(*owner).or_insert_with(|| AddressState {
            balance:   0u64.into(),
            operators: state_builder.new_set(),
        });
        owner_state.operators.insert(*operator);
    }

    /// Update the state removing an operator for a given token id and address.
    /// Results in an error if the token id does not exist in the state.
    /// Succeeds even if the `operator` is not an operator for this `token_id`
    /// and `address`.
    fn remove_operator(&mut self, owner: &Address, operator: &Address) {
        self.token.entry(*owner).and_modify(|address_state| {
            address_state.operators.remove(operator);
        });
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
        self.implementors.insert(std_id, implementors);
    }
}

// Contract functions

/// Initialize contract instance with no initial tokens.
/// Logs a `Mint` event for the single token id with no amounts.
#[init(
    contract = "cis2_wCCD",
    enable_logger,
    event = "Cis2Event<ContractTokenId, ContractTokenAmount>",
    parameter = "TestParams"
)]
fn contract_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
    logger: &mut impl HasLogger,
) -> InitResult<State<S>> {
    let test_params: TestParams = ctx.parameter_cursor().get()?;
    // Construct the initial contract state.
    let url = test_params.metadata_url.clone();
    let state = State::new(state_builder, test_params);
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
            url,
            hash: None,
        },
    }))?;

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
fn contract_wrap<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    amount: Amount,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
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
        host.invoke_contract(&address, &parameter, function.as_entrypoint_name(), Amount::zero())
            .unwrap_abort();
        Ok(())
    } else {
        Ok(())
    }
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
fn contract_unwrap<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
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
    contract = "cis2_wCCD",
    name = "transfer",
    parameter = "TransferParameter",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_transfer<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
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

        let to_address = if let Some(acc) = state.test_params.always_transfer_to {
            Address::Account(acc)
        } else {
            to.address()
        };
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
    if host.state().test_params.fail_transfer {
        return Err(ContractError::Unauthorized);
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
fn contract_update_operator<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
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

/// Parameter type for the CIS-2 function `balanceOf` specialized to the subset
/// of TokenIDs used by this contract.
type ContractBalanceOfQueryParams = BalanceOfQueryParams<ContractTokenId>;

type ContractBalanceOfQueryResponse = BalanceOfQueryResponse<ContractTokenAmount>;

enum BalanceOfRV {
    Normal(ContractBalanceOfQueryResponse),
    AString(String),
}

// Serial without any tags.
impl Serial for BalanceOfRV {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        match self {
            BalanceOfRV::Normal(x) => x.serial(out),
            BalanceOfRV::AString(x) => x.serial(out),
        }
    }
}

/// Get the balance of given token IDs and addresses.
///
/// It rejects if:
/// - Sender is not a contract.
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "cis2_wCCD",
    name = "balanceOf",
    parameter = "ContractBalanceOfQueryParams",
    return_value = "ContractBalanceOfQueryResponse",
    error = "ContractError"
)]
fn contract_balance_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<BalanceOfRV> {
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
    if host.state().test_params.fail_balance_of {
        return Err(ContractError::Unauthorized);
    }

    if host.state().test_params.balance_of_returns_string {
        return Ok(BalanceOfRV::AString("Hello".into()));
    }

    Ok(BalanceOfRV::Normal(result))
}

/// Takes a list of queries. Each query is an owner address and some address to
/// check as an operator of the owner address.
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
fn contract_operator_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<OperatorOfQueryResponse> {
    // Parse the parameter.
    let params: OperatorOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for address being an operator of owner.
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

enum MetadataRV {
    Normal(TokenMetadataQueryResponse),
    Number(u64),
}

// Serialize without a tag
impl Serial for MetadataRV {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        match self {
            MetadataRV::Normal(x) => x.serial(out),
            MetadataRV::Number(x) => x.serial(out),
        }
    }
}

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
fn contract_token_metadata<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<MetadataRV> {
    // Parse the parameter.
    let params: ContractTokenMetadataQueryParams = ctx.parameter_cursor().get()?;

    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for token_id in params.queries {
        // Check the token exists.
        ensure_eq!(token_id, TOKEN_ID_WCCD, ContractError::InvalidTokenId);

        let metadata_url = MetadataUrl {
            url:  host.state().test_params.metadata_url.clone(),
            hash: None,
        };
        response.push(metadata_url);
    }
    let result = TokenMetadataQueryResponse::from(response);
    if host.state().test_params.fail_token_metadata {
        return Err(ContractError::Unauthorized);
    }
    if host.state().test_params.token_metadata_returns_number {
        return Ok(MetadataRV::Number(42));
    }
    Ok(MetadataRV::Normal(result))
}

#[receive(contract = "cis2_wCCD", name = "updateUrl", parameter = "String", mutable)]
fn contract_update_url<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<()> {
    let metadata_url = ctx.parameter_cursor().get()?;
    host.state_mut().test_params.metadata_url = metadata_url;
    Ok(())
}

#[receive(contract = "cis2_wCCD", name = "updateTestParams", parameter = "TestParams", mutable)]
fn contract_update_test_params<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<()> {
    let params: TestParams = ctx.parameter_cursor().get()?;
    host.state_mut().test_params = params;
    Ok(())
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
fn contract_supports<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
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
/// - Sender is not the owner of the contract instance.
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_wCCD",
    name = "setImplementors",
    parameter = "SetImplementorsParams",
    error = "ContractError",
    mutable
)]
fn contract_set_implementor<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    // Authorize the sender.
    ensure!(ctx.sender().matches_account(&ctx.owner()), ContractError::Unauthorized);
    // Parse the parameter.
    let params: SetImplementorsParams = ctx.parameter_cursor().get()?;
    // Update the implementors in the state
    host.state_mut().set_implementors(params.id, params.implementors);
    Ok(())
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

    /// Test helper function which creates a contract state where ADDRESS_0 owns
    /// 400 tokens.
    fn initial_state<S: HasStateApi>(state_builder: &mut StateBuilder<S>) -> State<S> {
        let mut state = State::new(state_builder);
        state
            .mint(&TOKEN_ID_WCCD, 400u64.into(), &ADDRESS_0, state_builder)
            .expect_report("Failed to setup state");
        state
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

        // and parameter.
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

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let mut state = State::new(&mut state_builder);
        state
            .mint(&TOKEN_ID_WCCD, 400.into(), &ADDRESS_0, &mut state_builder)
            .expect_report("Failed to setup state");
        let mut host = TestHost::new(state, state_builder);

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

        // and parameter.
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

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

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

        // and parameter.
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

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let mut state = initial_state(&mut state_builder);
        state.add_operator(&ADDRESS_0, &ADDRESS_1, &mut state_builder);
        let mut host = TestHost::new(state, state_builder);

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

        // and parameter.
        let update = UpdateOperator {
            operator: ADDRESS_1,
            update:   OperatorUpdate::Add,
        };
        let parameter = UpdateOperatorParams(vec![update]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> = contract_update_operator(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        claim!(host.state().is_operator(&ADDRESS_1, &ADDRESS_0), "Account should be an operator");

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
        )
    }

    /// Test unwrapping to a receiver account that doesn't exist.
    ///
    /// This test also showcases the use of [`TestHost::with_rollback`],
    /// which handles rolling back the state if a receive function rejects.
    #[concordium_test]
    fn test_unwrap_to_missing_account() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);

        // and parameter.
        let parameter = UnwrapParams {
            amount:   ContractTokenAmount::from(100),
            owner:    ADDRESS_0,
            receiver: Receiver::from_account(ACCOUNT_1),
            data:     AdditionalData::empty(),
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);
        // Make ACCOUNT_1 missing such that transfers to it will fail.

        host.make_account_missing(ACCOUNT_1);

        // Call the contract function. Note the use of `with_rollback`.
        let result: ContractResult<()> =
            host.with_rollback(|host| contract_unwrap(&ctx, host, &mut logger));

        claim_eq!(result, Err(ContractError::Custom(CustomContractError::InvokeTransferError)));

        // The balance should still be 400 due to the rollback after rejecting.
        claim_eq!(host.state().balance(&TOKEN_ID_WCCD, &ADDRESS_0), Ok(400u64.into()));
        claim!(host.get_transfers().is_empty());
    }
}
