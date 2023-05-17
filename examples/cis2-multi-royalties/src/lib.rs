// Potential Todos:
//  allow royalties to be changed.
//  provide check in transfer function to prevent misuse.


//! A multi token example implementation of the Concordium Token Standard CIS2
//! which allows royalties to be collected.
//!
//! # Description
//! An instance of this smart contract can contain a number of different token
//! types each identified by a token ID. A token type is then globally
//! identified by the contract address together with the token ID.
//!
//! In this example the contract is initialized with no tokens, and tokens can
//! be minted through a `mint` contract function, which will only succeed for
//! the contract owner. No functionality to burn token is defined in this
//! example.
//!
//! Note: The word 'address' refers to either an account address or a
//! contract address.
//!
//! As follows from the CIS2 specification, the contract has a `transfer`
//! function for transferring an amount of a specific token type from one
//! address to another address. An address can enable and disable one or more
//! addresses as operators. An operator of some address is allowed to transfer
//! any tokens owned by this address.
//!
//! This contract also contains an example of a function to be called when
//! receiving tokens. In which case the contract will forward the tokens to
//! the contract owner.
//! 
//! This function is not very useful and is only there to showcase a simple
//! implementation of a token receive hook.
//! 
//! The token can be configured such that it pays royalties.  The settings for
//! whether royalties are paid and how much are configured in the State initialisation.

#![cfg_attr(not(feature = "std"), no_std)]
use concordium_cis2::*;
use concordium_std::*;

/// The baseurl for the token metadata, gets appended with the token ID as hex
/// encoding before emitted in the TokenMetadata event.
const TOKEN_METADATA_BASE_URL: &str = "https://some.example/token/";

/// List of supported standards by this contract address.
const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 2] =
    [CIS0_STANDARD_IDENTIFIER, CIS2_STANDARD_IDENTIFIER];

// Types

/// The parameter for the contract function `mint` which mints a number of
/// token types and/or amounts of tokens to a given address.
#[derive(Serial, Deserial, SchemaType)]
struct InterfaceParams {
    owner:  i32     // this is 4 bytes
}

/// Contract token ID type.
/// To save bytes we use a small token ID type, but is limited to be represented
/// by a `u8`.
type ContractTokenId = TokenIdU8;

/// Contract token amount type.
type ContractTokenAmount = TokenAmountU64;

/// The parameter for the contract function `init` which sets up the contract.
#[derive(Serial, Deserial, SchemaType)]
struct InitParams {
    /// pay royalties on this contract
    pay_royalty:  bool,
}
/// The parameter for the contract function `mint` which mints a number of
/// token types and/or amounts of tokens to a given address.
#[derive(Serial, Deserial, SchemaType)]
struct MintParams {
    /// Owner of the newly minted tokens.
    owner:  Address,
    /// A collection of tokens to mint.
    tokens: collections::BTreeMap<ContractTokenId, ContractTokenAmount>,
}

/// The parameter type for the contract function `setImplementors`.
/// Takes a standard identifier and a list of contract addresses providing
/// implementations of this standard.
#[derive(Debug, Serialize, SchemaType)]
struct SetImplementorsParams {
    /// The identifier for the standard.
    id:           StandardIdentifierOwned,
    /// The addresses of the implementors of the standard.
    implementors: Vec<ContractAddress>,
}


/// The parameter type for the contract function `check_royalty`.
/// Takes a tokenID and a sale price.
#[derive(Debug, Serialize, SchemaType)]
struct CheckRoyaltyParams {
    /// The identifier of the token.
    id:      ContractTokenId,
    /// The sale price.
    sale_price: u64,
}


#[derive(Debug, Serialize, SchemaType)]
struct CheckRoyaltyResult {
    /// The identifier of the payee.
    id:      Address,
    /// The royalties to pay.
    payment: u64,
}

/// The state for each address.
#[derive(Serial, DeserialWithState, Deletable, StateClone)]
#[concordium(state_parameter = "S")]
struct AddressState<S> {
    /// The amount of tokens owned by this address.
    balances:  StateMap<ContractTokenId, ContractTokenAmount, S>,
    /// The address which are currently enabled as operators for this address.
    operators: StateSet<Address, S>,
}


/// The details of each token.
#[derive(Debug, Serialize, SchemaType)]
struct TokenDetails {
    /// Who minted this token.
    minter:  Address,
    /// The percentage royalty.
    royalty: u64,
}

impl<S: HasStateApi> AddressState<S> {
    fn empty(state_builder: &mut StateBuilder<S>) -> Self {
        AddressState {
            balances:  state_builder.new_map(),
            operators: state_builder.new_set(),
        }
    }
}

/// The contract state,
///
/// Note: The specification does not specify how to structure the contract state
/// and this could be structured in a more space efficient way.
#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S> {
    /// The state of addresses.
    state:        StateMap<Address, AddressState<S>, S>,
    /// All of the token IDs
    tokens:       StateSet<ContractTokenId, S>,
    /// Map with contract addresses providing implementations of additional
    /// standards.
    implementors: StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,

    token_details: StateMap<ContractTokenId, TokenDetails, S>,

    pay_royalty: bool,
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
    /// Invalid contract name.
    InvalidContractName,
    /// Only a smart contract can call this function.
    ContractOnly,
    /// Failed to invoke a contract.
    InvokeContractError,
    /// No royalty payable.
    NoRoyaltyPayable,
    /// No royalties not payable in this contract.
    ContractDoesNotPayRoyalties,
}

type ContractError = Cis2Error<CustomContractError>;

type ContractResult<A> = Result<A, ContractError>;

//type RoyaltyResult = Result<CheckRoyaltyResult, CustomContractError>;

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

/// Mapping CustomContractError to ContractError
impl From<CustomContractError> for ContractError {
    fn from(c: CustomContractError) -> Self { Cis2Error::Custom(c) }
}

impl From<NewReceiveNameError> for CustomContractError {
    fn from(_: NewReceiveNameError) -> Self { Self::InvalidContractName }
}

impl From<NewContractNameError> for CustomContractError {
    fn from(_: NewContractNameError) -> Self { Self::InvalidContractName }
}

impl<S: HasStateApi> State<S> {
    /// Construct a state with no tokens
    fn empty(state_builder: &mut StateBuilder<S>) -> Self {
        State {
            state:        state_builder.new_map(),
            tokens:       state_builder.new_set(),
            implementors: state_builder.new_map(),
            token_details: state_builder.new_map(),
            pay_royalty: false,
        }
    }

    /// Mints an amount of tokens with a given address as the owner.
    fn mint(
        &mut self,
        token_id: &ContractTokenId,
        amount: ContractTokenAmount,
        owner: &Address,
        state_builder: &mut StateBuilder<S>,
        royalty: u64
    ) {
        self.tokens.insert(*token_id);        
        self.token_details.insert(*token_id, TokenDetails {minter:*owner, royalty:royalty});
        let mut owner_state =
            self.state.entry(*owner).or_insert_with(|| AddressState::empty(state_builder));
        let mut owner_balance = owner_state.balances.entry(*token_id).or_insert(0.into());
        *owner_balance += amount;
    }

    /// Check that the token ID currently exists in this contract.
    #[inline(always)]
    fn contains_token(&self, token_id: &ContractTokenId) -> bool { self.tokens.contains(token_id) }

    /// Get the current balance of a given token id for a given address.
    /// Results in an error if the token id does not exist in the state.
    fn balance(
        &self,
        token_id: &ContractTokenId,
        address: &Address,
    ) -> ContractResult<ContractTokenAmount> {
        ensure!(self.contains_token(token_id), ContractError::InvalidTokenId);
        let balance = self.state.get(address).map_or(0.into(), |address_state| {
            address_state.balances.get(token_id).map_or(0.into(), |x| *x)
        });
        Ok(balance)
    }

    /// Check if an address is an operator of a given owner address.
    fn is_operator(&self, address: &Address, owner: &Address) -> bool {
        self.state
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
        ensure!(self.contains_token(token_id), ContractError::InvalidTokenId);
        // A zero transfer does not modify the state.
        if amount == 0.into() {
            return Ok(());
        }

        // Get the `from` state and balance, if not present it will fail since the
        // balance is interpreted as 0 and the transfer amount must be more than
        // 0 as this point.;
        {
            let mut from_address_state =
                self.state.entry(*from).occupied_or(ContractError::InsufficientFunds)?;
            let mut from_balance = from_address_state
                .balances
                .entry(*token_id)
                .occupied_or(ContractError::InsufficientFunds)?;
            ensure!(*from_balance >= amount, ContractError::InsufficientFunds);
            *from_balance -= amount;
        }

        let mut to_address_state =
            self.state.entry(*to).or_insert_with(|| AddressState::empty(state_builder));
        let mut to_address_balance = to_address_state.balances.entry(*token_id).or_insert(0.into());
        *to_address_balance += amount;

        Ok(())
    }

    /// Update the state adding a new operator for a given address.
    /// Succeeds even if the `operator` is already an operator for the
    /// `address`.
    fn add_operator(
        &mut self,
        owner: &Address,
        operator: &Address,
        state_builder: &mut StateBuilder<S>,
    ) {
        let mut owner_state =
            self.state.entry(*owner).or_insert_with(|| AddressState::empty(state_builder));
        owner_state.operators.insert(*operator);
    }

    /// Update the state removing an operator for a given address.
    /// Succeeds even if the `operator` is not an operator for the `address`.
    fn remove_operator(&mut self, owner: &Address, operator: &Address) {
        self.state.entry(*owner).and_modify(|address_state| {
            address_state.operators.remove(operator);
        });
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

/// Build a string from TOKEN_METADATA_BASE_URL appended with the token ID
/// encoded as hex.
fn build_token_metadata_url(token_id: &ContractTokenId) -> String {
    let mut token_metadata_url = String::from(TOKEN_METADATA_BASE_URL);
    token_metadata_url.push_str(&token_id.to_string());
    token_metadata_url
}

// Contract functions

/// Initialize contract instance with a no token types.
#[init(contract = "cis2_multi_royalties", 
parameter = "InitParams",
event = "Cis2Event<ContractTokenId, ContractTokenAmount>")]
fn contract_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    // Construct the initial contract state.
    let params: InitParams = ctx.parameter_cursor().get()?;
    let mut state = State::empty(state_builder);
    state.pay_royalty = params.pay_royalty;
    Ok(state)
}

#[derive(Serialize, SchemaType)]
struct ViewAddressState {
    balances:  Vec<(ContractTokenId, ContractTokenAmount)>,
    operators: Vec<Address>,
}

#[derive(Serialize, SchemaType)]
struct ViewState {
    state:  Vec<(Address, ViewAddressState)>,
    tokens: Vec<ContractTokenId>,
}

/// View function for testing. This reports on the entire state of the contract
/// for testing purposes. In a realistic example there `balance_of` and similar
/// functions with a smaller response.
#[receive(contract = "cis2_multi_royalties", name = "view", return_value = "ViewState")]
fn contract_view<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<ViewState> {
    let state = host.state();

    let mut inner_state = Vec::new();
    for (k, a_state) in state.state.iter() {
        let mut balances = Vec::new();
        let mut operators = Vec::new();
        for (token_id, amount) in a_state.balances.iter() {
            balances.push((*token_id, *amount));
        }
        for o in a_state.operators.iter() {
            operators.push(*o);
        }

        inner_state.push((*k, ViewAddressState {
            balances,
            operators,
        }));
    }
    let mut tokens = Vec::new();
    for v in state.tokens.iter() {
        tokens.push(*v);
    }

    Ok(ViewState {
        state: inner_state,
        tokens,
    })
}

/// Mint new tokens with a given address as the owner of these tokens.
/// Can only be called by the contract owner.
/// Logs a `Mint` and a `TokenMetadata` event for each token.
/// The url for the token metadata is the token ID encoded in hex, appended on
/// the `TOKEN_METADATA_BASE_URL`.
///
/// It rejects if:
/// - The sender is not the contract instance owner.
/// - Fails to parse parameter.
/// - Any of the tokens fails to be minted, which could be if:
///     - Fails to log Mint event.
///     - Fails to log TokenMetadata event.
///
/// Note: Can at most mint 32 token types in one call due to the limit on the
/// number of logs a smart contract can produce on each function call.
#[receive(
    contract = "cis2_multi_royalties",
    name = "mint",
    parameter = "MintParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_mint<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Get the contract owner
    let owner = ctx.owner();
    // Get the sender of the transaction
    let sender = ctx.sender();

    ensure!(sender.matches_account(&owner), ContractError::Unauthorized);

    // Parse the parameter.
    let params: MintParams = ctx.parameter_cursor().get()?;

    let (state, builder) = host.state_and_builder();
    for (token_id, token_amount) in params.tokens {
        // Mint the token in the state.
        state.mint(&token_id, token_amount, &params.owner, builder, 0);
        
        // Event for minted token.
        logger.log(&Cis2Event::Mint(MintEvent {
            token_id,
            amount: token_amount,
            owner: params.owner,
        }))?;

        // Metadata URL for the token.
        logger.log(&Cis2Event::TokenMetadata::<_, ContractTokenAmount>(TokenMetadataEvent {
            token_id,
            metadata_url: MetadataUrl {
                url:  build_token_metadata_url(&token_id),
                hash: None,
            },
        }))?;
    }
    Ok(())
}

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
    contract = "cis2_multi_royalties",
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

        // If the receiver is a contract we invoke it.
        if let Receiver::Contract(address, entrypoint_name) = to {
            let parameter = OnReceivingCis2Params {
                token_id,
                amount,
                from,
                data,
            };
            host.invoke_contract(
                &address,
                &parameter,
                entrypoint_name.as_entrypoint_name(),
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
    contract = "cis2_multi_royalties",
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

    let (state, builder) = host.state_and_builder();
    for param in params {
        // Update the operator in the state.
        match param.update {
            OperatorUpdate::Add => state.add_operator(&sender, &param.operator, builder),
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

/// Response type for the CIS-2 function `balanceOf` specialized to the subset
/// of TokenAmounts used by this contract.
type ContractBalanceOfQueryResponse = BalanceOfQueryResponse<ContractTokenAmount>;

/// Get the balance of given token IDs and addresses.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "cis2_multi_royalties",
    name = "balanceOf",
    parameter = "ContractBalanceOfQueryParams",
    return_value = "ContractBalanceOfQueryResponse",
    error = "ContractError"
)]
fn contract_balance_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
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
    contract = "cis2_multi_royalties",
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
type ContractTokenMetadataQueryParams = TokenMetadataQueryParams<ContractTokenId>;

/// Get the token metadata URLs and checksums given a list of token IDs.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "cis2_multi_royalties",
    name = "tokenMetadata",
    parameter = "ContractTokenMetadataQueryParams",
    return_value = "TokenMetadataQueryResponse",
    error = "ContractError"
)]
fn contract_token_metadata<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<TokenMetadataQueryResponse> {
    // Parse the parameter.
    let params: ContractTokenMetadataQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for token_id in params.queries {
        // Check the token exists.
        ensure!(host.state().contains_token(&token_id), ContractError::InvalidTokenId);

        let metadata_url = MetadataUrl {
            url:  build_token_metadata_url(&token_id),
            hash: None,
        };
        response.push(metadata_url);
    }
    let result = TokenMetadataQueryResponse::from(response);
    Ok(result)
}

/// Example of implementing a function for receiving transfers.
/// It is not required to be implemented by the token contract, but is required
/// to implement such a function by any contract which should receive CIS2
/// tokens.
///
/// This contract function is called when a token is transferred to an instance
/// of this contract and should only be called by a contract implementing CIS2.
/// The parameter include a `data` field which can be used to
/// implement some arbitrary functionality. In this example we choose not to use
/// it, and define the function to forward any transfers to the owner of the
/// contract instance.
///
/// Note: The name of this function is not part the CIS2, and a contract can
/// have multiple functions for receiving tokens.
///
/// It rejects if:
/// - Sender is not a contract.
/// - It fails to parse the parameter.
/// - Contract name part of the parameter is invalid.
/// - Calling back `transfer` to sender contract rejects.
#[receive(contract = "cis2_multi_royalties", name = "onReceivingCIS2", error = "ContractError")]
fn contract_on_cis2_received<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    // Ensure the sender is a contract.
    let sender = if let Address::Contract(contract) = ctx.sender() {
        contract
    } else {
        bail!(CustomContractError::ContractOnly.into())
    };

    // Parse the parameter.
    let params: OnReceivingCis2Params<ContractTokenId, ContractTokenAmount> =
        ctx.parameter_cursor().get()?;

    // Build the transfer from this contract to the contract owner.
    let transfer = Transfer {
        token_id: params.token_id,
        amount:   params.amount,
        from:     Address::Contract(ctx.self_address()),
        to:       Receiver::from_account(ctx.owner()),
        data:     AdditionalData::empty(),
    };

    let parameter = TransferParams::from(vec![transfer]);

    // Send back a transfer
    host.invoke_contract_read_only(
        &sender,
        &parameter,
        EntrypointName::new("transfer")?,
        Amount::zero(),
    )?;
    Ok(())
}

/// Get the supported standards or addresses for a implementation given list of
/// standard identifiers.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_multi_royalties",
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
    contract = "cis2_multi_royalties",
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

/// Returns the address of the payee and the amount of royalties to pay them
/// 
/// It rejects if:
/// - The contract does not pay royalties
/// - The return result would be 0
/// - The token is not recognised
#[receive(
    contract = "cis2_multi_royalties",
    name = "check_royalty",
    parameter = "CheckRoyaltyParams",
    error = "ContractError",    
)]
fn contract_check_royalty<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<CheckRoyaltyResult> {
    ensure!(host.state().pay_royalty == true, concordium_cis2::Cis2Error::Custom(CustomContractError::ContractDoesNotPayRoyalties));

    let params: CheckRoyaltyParams = ctx.parameter_cursor().get()?;
    ensure!(params.sale_price > 0, concordium_cis2::Cis2Error::Custom(CustomContractError::NoRoyaltyPayable));
    ensure!(host.state().contains_token(&params.id), ContractError::InvalidTokenId);
    
    let token_details = host.state().token_details.get(&params.id).unwrap(); // safe due to previous checks
    ensure!(token_details.royalty > 0, concordium_cis2::Cis2Error::Custom(CustomContractError::NoRoyaltyPayable));
    let minter = token_details.minter;
    let royalty_to_pay:u64 = params.sale_price / 100 * token_details.royalty;
    let result = CheckRoyaltyResult {
        id: minter,
        payment: royalty_to_pay, 
    };

    Ok(result)
}

/// View function to see whether we support paying royalties
#[receive(contract = "cis2_multi_royalties", name = "supports_interface", return_value = "bool")]
fn supports_interface<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<bool> {
    // At the moment the parameters are not used in this scope
    let state = host.state();

    Ok(state.pay_royalty)
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
    const TOKEN_0: ContractTokenId = TokenIdU8(2);
    const TOKEN_1: ContractTokenId = TokenIdU8(42);

    /// Test helper function which creates a contract state with two tokens with
    /// id `TOKEN_0` and id `TOKEN_1` owned by `ADDRESS_0`
    fn initial_state<S: HasStateApi>(state_builder: &mut StateBuilder<S>) -> State<S> {
        let mut state = State::empty(state_builder);
        state.mint(&TOKEN_0, 400.into(), &ADDRESS_0, state_builder, 0);
        state.mint(&TOKEN_1, 1.into(), &ADDRESS_0, state_builder, 0);
        state
    }

    /// Test helper function which creates a contract state with a token with a royalty
    fn initial_state_with_royalties<S: HasStateApi>(state_builder: &mut StateBuilder<S>) -> State<S> {
        let mut state = State::empty(state_builder);
        state.mint(&TOKEN_0, 400.into(), &ADDRESS_0, state_builder, 50);
        state.pay_royalty = true;
        state
    }

    /// Test initialization succeeds with a state with no tokens.
    #[concordium_test]
    fn test_init() {
        // Setup the context
        let mut ctx = TestInitContext::empty();
        let mut builder = TestStateBuilder::new();
        let royalty = false;
        let init_parameter_bytes = to_bytes(&royalty);
        ctx.set_parameter(&init_parameter_bytes);

        // Call the contract function.
        let result = contract_init(&ctx, &mut builder);

        // Check the result
        let state = result.expect_report("Contract initialization failed");

        // Check the state
        claim_eq!(state.tokens.iter().count(), 0, "Only one token is initialized");
    }

    /// Test minting succeeds and the tokens are owned by the given address and
    /// the appropriate events are logged.
    #[concordium_test]
    fn test_mint() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_owner(ACCOUNT_0);

        // and parameter.
        let mut tokens = collections::BTreeMap::new();
        tokens.insert(TOKEN_0, 400.into());
        tokens.insert(TOKEN_1, 1.into());
        let parameter = MintParams {
            owner: ADDRESS_0,
            tokens,
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::empty(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> = contract_mint(&ctx, &mut host, &mut logger);

        // Check the result
        claim!(result.is_ok(), "Results in rejection");

        // Check the state
        claim_eq!(host.state().tokens.iter().count(), 2, "Only one token is initialized");
        let balance0 =
            host.state().balance(&TOKEN_0, &ADDRESS_0).expect_report("Token is expected to exist");
        claim_eq!(balance0, 400.into(), "Initial tokens are owned by the contract instantiater");

        let balance1 =
            host.state().balance(&TOKEN_1, &ADDRESS_0).expect_report("Token is expected to exist");
        claim_eq!(balance1, 1.into(), "Initial tokens are owned by the contract instantiater");

        // Check the logs
        claim_eq!(logger.logs.len(), 4, "Exactly four events should be logged");
        claim!(
            logger.logs.contains(&to_bytes(&Cis2Event::Mint(MintEvent {
                owner:    ADDRESS_0,
                token_id: TOKEN_0,
                amount:   ContractTokenAmount::from(400),
            }))),
            "Expected an event for minting TOKEN_0"
        );
        claim!(
            logger.logs.contains(&to_bytes(&Cis2Event::Mint(MintEvent {
                owner:    ADDRESS_0,
                token_id: TOKEN_1,
                amount:   ContractTokenAmount::from(1),
            }))),
            "Expected an event for minting TOKEN_1"
        );
        claim!(
            logger.logs.contains(&to_bytes(&Cis2Event::TokenMetadata::<_, ContractTokenAmount>(
                TokenMetadataEvent {
                    token_id:     TOKEN_0,
                    metadata_url: MetadataUrl {
                        url:  "https://some.example/token/02".to_string(),
                        hash: None,
                    },
                }
            ))),
            "Expected an event for token metadata for TOKEN_0"
        );
        claim!(
            logger.logs.contains(&to_bytes(&Cis2Event::TokenMetadata::<_, ContractTokenAmount>(
                TokenMetadataEvent {
                    token_id:     TOKEN_1,
                    metadata_url: MetadataUrl {
                        url:  "https://some.example/token/2A".to_string(),
                        hash: None,
                    },
                }
            ))),
            "Expected an event for token metadata for TOKEN_1"
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
            token_id: TOKEN_0,
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
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> = contract_transfer(&ctx, &mut host, &mut logger);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        let balance0 =
            host.state().balance(&TOKEN_0, &ADDRESS_0).expect_report("Token is expected to exist");
        let balance1 =
            host.state().balance(&TOKEN_0, &ADDRESS_1).expect_report("Token is expected to exist");
        claim_eq!(
            balance0,
            300.into(),
            "Token owner balance should be decreased by the transferred amount."
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
                token_id: TOKEN_0,
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
            token_id: TOKEN_0,
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
            token_id: TOKEN_0,
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
        let balance0 =
            host.state().balance(&TOKEN_0, &ADDRESS_0).expect_report("Token is expected to exist");
        let balance1 =
            host.state().balance(&TOKEN_0, &ADDRESS_1).expect_report("Token is expected to exist");
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
                token_id: TOKEN_0,
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
        let is_operator = host.state().is_operator(&ADDRESS_1, &ADDRESS_0);
        claim!(is_operator, "Account should be an operator");

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

    // test royalties are initialised properly
    #[concordium_test]
    fn test_royalties_setup() {
        // Setup the context
        let ctx = TestReceiveContext::empty();
        let mut builder1 = TestStateBuilder::new();
        let state1 = initial_state(&mut builder1);
        let host = TestHost::new(state1, builder1);
        let royalty_paid = supports_interface(&ctx, &host);
        claim_eq!(royalty_paid.unwrap(), false, "Royalty incorrectly initialised");        

        let mut builder2 = TestStateBuilder::new();
        let mut state2 = initial_state(&mut builder2);
        state2.pay_royalty = true;
        let host = TestHost::new(state2, builder2);
        let royalty_paid = supports_interface(&ctx, &host);
        claim_eq!(royalty_paid.unwrap(), true, "Royalty incorrectly initialised");        
    }

    // test royalties are initialised properly
    #[concordium_test]
    fn test_royalties() {
        let ctx = TestReceiveContext::empty();
        let mut builder = TestStateBuilder::new();
        let state = initial_state(&mut builder);
        let host = TestHost::new(state, builder);
        let royalty_paid = supports_interface(&ctx, &host);
        claim_eq!(royalty_paid.unwrap(), false, "Royalty incorrectly initialised");        
    }

    // test royalties are paid correctly
    #[concordium_test]
    fn test_royalties_paid() {
        // initialise the contract ready for royalties
        let mut init_state_builder = TestStateBuilder::new();
        let mut ctx_init = TestInitContext::empty();
        let royalty = true;
        let init_parameter_bytes = to_bytes(&royalty);
        ctx_init.set_parameter(&init_parameter_bytes);

        let _ = contract_init(&ctx_init, &mut init_state_builder);

        let mut ctx_roy = TestReceiveContext::empty();
        let royalty = CheckRoyaltyParams {
            id: TOKEN_0,
            sale_price:   200,
        };
        
        let mut roy_state_builder = TestStateBuilder::new();
        let mut state = initial_state_with_royalties(&mut roy_state_builder);
        
        state.mint(&TOKEN_0, 400.into(), &ADDRESS_0, & mut roy_state_builder, 50);

        let mut host = TestHost::new(state, roy_state_builder);
        let roy_parameter: CheckRoyaltyParams = CheckRoyaltyParams::from(royalty);
        let roy_parameter_bytes = to_bytes(&roy_parameter);
        ctx_roy.set_parameter(&roy_parameter_bytes);

         let royalties: CheckRoyaltyResult = contract_check_royalty(&ctx_roy, &mut host).unwrap();
        
        claim_eq!(royalties.id, ADDRESS_0, "Incorrect address paid royalities");        
        claim_eq!(royalties.payment, 100, "Incorrect amount of royalities paid");
    }

 // test code sends correct error when price is 0
 #[concordium_test]
 fn test_royalties_with_zero_price() {
     // Setup the context
     let mut ctx = TestReceiveContext::empty();
     ctx.set_owner(ACCOUNT_1);
     let royalty = CheckRoyaltyParams {
         id: TOKEN_0,
         sale_price:   0,
     };
     let parameter: CheckRoyaltyParams = CheckRoyaltyParams::from(royalty);
     let parameter_bytes = to_bytes(&parameter);
     ctx.set_parameter(&parameter_bytes);

     let mut state_builder = TestStateBuilder::new();
     let mut state = initial_state(&mut state_builder);
     state.pay_royalty = true;
     let mut host = TestHost::new(state, state_builder);
     
     let result = contract_check_royalty(&ctx, &mut host);
     // Check the result.
     let err = result.expect_err_report("Expected to fail with 0 price");
     claim_eq!(err, 
        concordium_cis2::Cis2Error::Custom(CustomContractError::NoRoyaltyPayable), 
        "Error should be no royalty payable")

 }

// test code sends correct error when royalty percentage is 0
#[concordium_test]
fn test_royalties_with_zero_royalty_percentage() {
    // Setup the context
    let mut ctx = TestReceiveContext::empty();
    ctx.set_owner(ACCOUNT_1);
    let royalty = CheckRoyaltyParams {
        id: TOKEN_0,
        sale_price:   200,
    };
    let parameter: CheckRoyaltyParams = CheckRoyaltyParams::from(royalty);
    let parameter_bytes = to_bytes(&parameter);
    ctx.set_parameter(&parameter_bytes);

    let mut state_builder = TestStateBuilder::new();
    let mut state = initial_state(&mut state_builder);
    state.pay_royalty = true;
    let mut host = TestHost::new(state, state_builder);
    
    let result = contract_check_royalty(&ctx, &mut host);
    // Check the result.
    let err = result.expect_err_report("Expected to fail with 0 price");
    claim_eq!(err, 
       concordium_cis2::Cis2Error::Custom(CustomContractError::NoRoyaltyPayable), 
       "Error should be no royalty payable")
    }


    // test code sends correct error when token id is invalid
    #[concordium_test]
    fn test_royalties_with_invalid_token() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_owner(ACCOUNT_1);
        let royalty = CheckRoyaltyParams {
            id: TokenIdU8(5),
            sale_price:   200,
        };
        let parameter: CheckRoyaltyParams = CheckRoyaltyParams::from(royalty);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut state_builder = TestStateBuilder::new();
        let mut state = initial_state(&mut state_builder);
        state.pay_royalty = true;
        let mut host = TestHost::new(state, state_builder);
        let result = contract_check_royalty(&ctx, &mut host);
        // Check the result.
        let err = result.expect_err_report("Expected to fail with invalid tokenID");
        claim_eq!(err, 
            ContractError::InvalidTokenId, 
            "Error should be invalid tokenID");
    }
}
