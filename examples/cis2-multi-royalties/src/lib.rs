// Potential Todos:
//  allow royalties to be changed.

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
//! The token can be configured such that it pays royalties. The settings for
//! whether royalties are paid and how much are configured in the State
//! initialisation.

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

/// Contract token ID type.
/// To save bytes we use a small token ID type, but is limited to be represented
/// by a `u8`.
pub type ContractTokenId = TokenIdU8;

/// Contract token amount type.
pub type ContractTokenAmount = TokenAmountU64;

/// The parameter for the contract function `init` which sets up the contract.
#[derive(Serial, Deserial, SchemaType)]
#[repr(transparent)]
pub struct InitParams {
    /// Specifies if this contract enforces the royalty payout whenever a token
    /// is transferred.
    pub pay_royalty: bool,
}

/// The parameter for the contract function `mint` which mints a number of
/// token types and/or amounts of tokens to a given address.
#[derive(Serial, Deserial, SchemaType)]
pub struct MintParams {
    /// Owner of the newly minted tokens.
    pub owner:              Address,
    /// A collection of tokens to mint.
    pub tokens:             collections::BTreeMap<ContractTokenId, ContractTokenAmount>,
    /// Royalty payable to minter (in percentage)
    pub royalty_percentage: u8,
}

/// The parameter type for the contract function `setImplementors`.
/// Takes a standard identifier and a list of contract addresses providing
/// implementations of this standard.
#[derive(Debug, Serialize, SchemaType)]
pub struct SetImplementorsParams {
    /// The identifier for the standard.
    pub id:           StandardIdentifierOwned,
    /// The addresses of the implementors of the standard.
    pub implementors: Vec<ContractAddress>,
}

/// The parameter type for the contract function `check_royalty`.
/// Takes a tokenID and a sale price.
#[derive(Debug, Serialize, SchemaType)]
pub struct CheckRoyaltyParams {
    /// The identifier of the token.
    pub id:         ContractTokenId,
    /// The sale price.
    pub sale_price: u64,
}

#[derive(Debug, Serialize, SchemaType)]
pub struct CheckRoyaltyResult {
    /// The Address of the payee.
    pub royalty_receiver: Address,
    /// The royalties to pay.
    pub payment:          u64,
}

/// The state for each address.
#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
struct AddressState<S = StateApi> {
    /// The amount of tokens owned by this address.
    balances:  StateMap<ContractTokenId, ContractTokenAmount, S>,
    /// The address which are currently enabled as operators for this address.
    operators: StateSet<Address, S>,
}

/// The details of each token.
#[derive(Debug, Serialize, SchemaType)]
pub struct TokenDetails {
    /// Who minted this token.
    pub minter:  Address,
    /// The percentage royalty.
    pub royalty: u8,
}

impl AddressState {
    fn empty(state_builder: &mut StateBuilder) -> Self {
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
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S = StateApi> {
    /// The state of addresses.
    state:         StateMap<Address, AddressState<S>, S>,
    /// All of the token IDs
    tokens:        StateSet<ContractTokenId, S>,
    /// Map with contract addresses providing implementations of additional
    /// standards.
    implementors:  StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
    /// Map with details of who minted the token and what the royalty payment
    /// is.
    token_details: StateMap<ContractTokenId, TokenDetails, S>,
    /// Boolean which controls whether royalties are paid.
    pay_royalty:   bool,
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
    /// Only a smart contract can call this function.
    ContractOnly,
    /// Failed to invoke a contract.
    InvokeContractError,
    /// No royalties can be paid out.
    NoRoyaltyPayable,
    /// This contract does not pay royalties.
    ContractDoesNotPayRoyalties,
    /// Trying to calculate royalties for an invalid token.
    InvalidTokenId,
    /// Royalties have to be between 0 and 100 perent.
    InvalidRoyaltyValue,
    /// Royalty payment destination address should be known.
    InvalidRoyaltyAddress,
    /// Overflow in royalty calculation.
    Overflow,
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

/// Mapping CustomContractError to ContractError
impl From<CustomContractError> for ContractError {
    fn from(c: CustomContractError) -> Self { Cis2Error::Custom(c) }
}

impl State {
    /// Construct a state with no tokens
    fn empty(state_builder: &mut StateBuilder, pay_royalty: bool) -> Self {
        State {
            state: state_builder.new_map(),
            tokens: state_builder.new_set(),
            implementors: state_builder.new_map(),
            token_details: state_builder.new_map(),
            pay_royalty,
        }
    }

    /// Mints an amount of tokens with a given address as the owner.
    fn mint(
        &mut self,
        token_id: &ContractTokenId,
        amount: ContractTokenAmount,
        owner: &Address,
        state_builder: &mut StateBuilder,
        royalty: u8,
    ) {
        self.tokens.insert(*token_id);
        let _ = self.token_details.insert(*token_id, TokenDetails {
            minter: *owner,
            royalty,
        });

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
        mut amount: ContractTokenAmount,
        from: &Address,
        to: &Address,
        state_builder: &mut StateBuilder,
        royalties: &Option<CheckRoyaltyResult>,
    ) -> ContractResult<()> {
        ensure!(self.contains_token(token_id), ContractError::InvalidTokenId);
        // A zero transfer does not modify the state.
        if amount == 0.into() {
            return Ok(());
        }
        // Get the `from` state and balance, if not present it will fail since the
        // balance is interpreted as 0 and the transfer amount must be more than
        // 0 at this point.
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

        if let Some(royalties) = royalties {
            let mut royalties_state = self
                .state
                .entry(royalties.royalty_receiver)
                .occupied_or(CustomContractError::InvalidRoyaltyAddress)?;

            let mut minter_balance =
                royalties_state.balances.entry(*token_id).or_insert(TokenAmountU64(0));

            *minter_balance += concordium_cis2::TokenAmountU64(royalties.payment);
            amount -= concordium_cis2::TokenAmountU64(royalties.payment);
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
        state_builder: &mut StateBuilder,
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
        let _ = self.implementors.insert(std_id, implementors);
    }

    fn calculate_royalty_payments(
        &mut self,
        params: CheckRoyaltyParams,
    ) -> Result<CheckRoyaltyResult, ContractError> {
        let token_details =
            self.token_details.get(&params.id).ok_or(ContractError::InvalidTokenId)?;

        let minter = token_details.minter;
        let royalty_to_pay: u64 = params
            .sale_price
            .checked_mul(token_details.royalty as u64)
            .ok_or(CustomContractError::Overflow)?
            / 100;

        Ok(CheckRoyaltyResult {
            royalty_receiver: minter,
            payment:          royalty_to_pay,
        })
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
#[init(
    contract = "cis2_multi_royalties",
    parameter = "InitParams",
    event = "Cis2Event<ContractTokenId, ContractTokenAmount>"
)]
fn contract_init(ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<State> {
    // Construct the initial contract state.
    let params: InitParams = ctx.parameter_cursor().get()?;
    let state = State::empty(state_builder, params.pay_royalty);
    Ok(state)
}

#[derive(Serialize, SchemaType, Debug, PartialEq, Eq)]
pub struct ViewAddressState {
    pub balances:  Vec<(ContractTokenId, ContractTokenAmount)>,
    pub operators: Vec<Address>,
}

#[derive(Serialize, SchemaType)]
pub struct ViewState {
    pub state:  Vec<(Address, ViewAddressState)>,
    pub tokens: Vec<ContractTokenId>,
}

/// View function for testing. This reports on the entire state of the contract
/// for testing purposes. In a realistic example there `balance_of` and similar
/// functions with a smaller response.
#[receive(contract = "cis2_multi_royalties", name = "view", return_value = "ViewState")]
fn contract_view(_ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<ViewState> {
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
fn contract_mint(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut Logger,
) -> ContractResult<()> {
    // Get the contract owner
    let owner = ctx.owner();
    // Get the sender of the transaction
    let sender = ctx.sender();

    ensure!(sender.matches_account(&owner), ContractError::Unauthorized);

    // Parse the parameter.
    let params: MintParams = ctx.parameter_cursor().get()?;
    ensure!(params.royalty_percentage <= 100, CustomContractError::InvalidRoyaltyValue.into());

    let (state, builder) = host.state_and_builder();
    for (token_id, token_amount) in params.tokens {
        // Mint the token in the state.
        state.mint(&token_id, token_amount, &params.owner, builder, params.royalty_percentage);

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
fn contract_transfer(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut Logger,
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
        let mut royalties: Option<CheckRoyaltyResult> = None;

        if state.pay_royalty {
            let royalty_parameters = CheckRoyaltyParams {
                id:         token_id,
                sale_price: amount.into(),
            };

            let royal_result = state.calculate_royalty_payments(royalty_parameters)?;
            royalties = Some(royal_result);
        }

        // Update the contract state
        state.transfer(&token_id, amount, &from, &to_address, builder, &royalties)?;

        let mut receivers_amount = amount;
        if let Some(royalties) = royalties {
            // Log transfer event
            logger.log(&Cis2Event::Transfer(TransferEvent {
                token_id,
                amount: concordium_cis2::TokenAmountU64(royalties.payment),
                from,
                to: royalties.royalty_receiver,
            }))?;
            receivers_amount -= concordium_cis2::TokenAmountU64(royalties.payment);
        }
        // Log transfer event
        logger.log(&Cis2Event::Transfer(TransferEvent {
            token_id,
            amount: receivers_amount,
            from,
            to: to_address,
        }))?;

        // If the receiver is a contract we invoke it.
        // Please note that the royalty receiver is an account therefore no receiveHook
        // function is required for it.
        if let Receiver::Contract(address, entrypoint_name) = to {
            let parameter = OnReceivingCis2Params {
                token_id,
                amount: receivers_amount,
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
fn contract_update_operator(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut Logger,
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
fn contract_operator_of(
    ctx: &ReceiveContext,
    host: &Host<State>,
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
fn contract_on_cis2_received(ctx: &ReceiveContext, host: &Host<State>) -> ContractResult<()> {
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
        EntrypointName::new_unchecked("transfer"),
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
/// - Sender is not the owner of the contract instance.
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_multi_royalties",
    name = "setImplementors",
    parameter = "SetImplementorsParams",
    error = "ContractError",
    mutable
)]
fn contract_set_implementor(ctx: &ReceiveContext, host: &mut Host<State>) -> ContractResult<()> {
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
/// - The token id does not exist in state
#[receive(
    contract = "cis2_multi_royalties",
    name = "check_royalty",
    parameter = "CheckRoyaltyParams",
    error = "ContractError",
    mutable
)]
fn contract_check_royalty(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
) -> ContractResult<CheckRoyaltyResult> {
    ensure!(host.state().pay_royalty, CustomContractError::ContractDoesNotPayRoyalties.into());

    let params: CheckRoyaltyParams = ctx.parameter_cursor().get()?;
    ensure!(params.sale_price > 0, CustomContractError::NoRoyaltyPayable.into());
    ensure!(host.state().contains_token(&params.id), ContractError::InvalidTokenId);
    let token_details =
        host.state().token_details.get(&params.id).ok_or(ContractError::InvalidTokenId)?;
    ensure!(token_details.royalty > 0, CustomContractError::NoRoyaltyPayable.into());

    host.state_mut().calculate_royalty_payments(params)
}

/// View function to see whether we support paying royalties
#[receive(
    contract = "cis2_multi_royalties",
    name = "contract_pays_royalties",
    return_value = "bool"
)]
fn contract_pays_royalties(_ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<bool> {
    // At the moment the parameters are not used in this scope
    let state = host.state();

    Ok(state.pay_royalty)
}
