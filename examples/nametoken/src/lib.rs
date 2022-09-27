//! A NameToken smart contract example using the Concordium Token Standard CIS2.
//!
//! # Description
//! A contract that allows for registering domain names and some metainformation about these.
//! A domain name can be registered if it is not already taken. Only account addresses can be
//! owners. The ownership can be transferred to another account address, by the current owner.
//! Registering and updating the metadata requires a fixed fee.
//!
//! # Token
//! The nametoken is essentially a NFT. Therefore we expose it as an instance of CIS-2 standard.
//! This allows for trading of domain names on NFT auctions.

#![cfg_attr(not(feature = "std"), no_std)]

use concordium_cis2::*;
use concordium_std::*;

/// The baseurl for the token metadata, gets appended with the token ID as hex
/// encoding before emitted in the TokenMetadata event.
const TOKEN_METADATA_BASE_URL: &str = "https://some.example/nametoken/";

/// List of supported standards by this contract address.
const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 2] =
    [CIS0_STANDARD_IDENTIFIER, CIS2_STANDARD_IDENTIFIER];

// Fees

// Registration fee in CCD
const REGISTRACTION_FEE : Amount = Amount::from_ccd(70);

// Data update fee in CCD
const UPDATE_FEE : Amount = Amount::from_ccd(7);

// Extension fee in CCD
const RENEWAL_FEE : Amount = Amount::from_ccd(7);

// How long the registered name is owned before it needs to be renewed
const REGISTRATION_PERIOD_DAYS : u64 = 365;

// Types

/// Contract token ID type.
type ContractTokenId = TokenIdFixed<32>;

/// Contract token amount.
/// Since the tokens are non-fungible the total supply of any token will be at
/// most 1 and it is fine to use a small type for representing token amounts.
type ContractTokenAmount = TokenAmountU8;

/// The parameter for the contract function `register` which registers a name
/// for a given address.
#[derive(Serial, Deserial, SchemaType)]
struct RegisterNameParams {
    /// Owner of the newly registered name
    owner:  AccountAddress,
    /// Name
    name: String,
}

#[derive(Serial, DeserialWithState, Deletable, StateClone)]
#[concordium(state_parameter = "S")]
struct NameInfo<S: HasStateApi> {
    // name owner
    owner: AccountAddress,
    // expiration date
    name_expires: Timestamp,
    // associated data
    data: StateBox<Vec<u8>,S>
} 

impl<S: HasStateApi> NameInfo<S> {
    fn fresh(owner: AccountAddress, name_expires: Timestamp, state_builder: &mut StateBuilder<S>) -> Self {
        NameInfo {
            owner,
            name_expires,
            data: state_builder.new_box(Vec::new())
        }
    }
}

/// The state for each address.
#[derive(Serial, DeserialWithState, Deletable, StateClone)]
#[concordium(state_parameter = "S")]
struct AddressState<S> {
    /// The tokens owned by this address.
    owned_names: StateSet<ContractTokenId, S>,
    /// The address which are currently enabled as operators for this address.
    operators:   StateSet<Address, S>,
}

impl<S: HasStateApi> AddressState<S> {
    fn empty(state_builder: &mut StateBuilder<S>) -> Self {
        AddressState {
            owned_names: state_builder.new_set(),
            operators:   state_builder.new_set(),
        }
    }
}

/// The contract state.
// Note: The specification does not specify how to structure the contract state
// and this could be structured in a more space efficient way depending on the use case.
#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S: HasStateApi> {
    /// The state for each account address.
    state:        StateMap<AccountAddress, AddressState<S>, S>,
    /// All of the token IDs
    all_names:    StateMap<ContractTokenId, NameInfo<S>, S>,
    /// Map with contract addresses providing implementations of additional
    /// standards.
    implementors: StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
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

#[derive(Debug, Serialize, SchemaType)]
struct UpdateDataParams {
    name: String,
    data: Vec<u8>,
}


/// The custom errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Failed logging: Log is full.
    LogFull,
    /// Failed logging: Log is malformed.
    LogMalformed,
    /// Failing to register a name because it already exists
    /// in this contract.
    NameIsTaken,
    /// Only accounts can own names
    OwnerShouldBeAccount,
    /// The amount does not match the fee
    IncorrectFee,
    // some invarians of the state are broken
    InconsistentState,
    /// Failed to invoke a contract.
    InvokeContractError,
    /// Name is not found in the registry
    NameNotFound,
}

/// Wrapping the custom errors in a type with CIS2 errors.
type ContractError = Cis2Error<CustomContractError>;

type ContractResult<A> = Result<A, ContractError>;

/// Mapping the logging errors to CustomContractError.
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

// Functions for creating, updating and querying the contract state.
impl<S: HasStateApi> State<S> {
    /// Creates a new state with no tokens.
    fn empty(state_builder: &mut StateBuilder<S>) -> Self {
        State {
            state:        state_builder.new_map(),
            all_names:    state_builder.new_map(),
            implementors: state_builder.new_map(),
        }
    }

    /// Register a name if it's not taken
    fn register_fresh(
        &mut self,
        name: &ContractTokenId,
        owner: &AccountAddress,
        expires : Timestamp,
        state_builder: &mut StateBuilder<S>,
    ) -> ContractResult<()> {
        let name_info = NameInfo::fresh(*owner, expires, state_builder);
        // make sure that the name is not taken
        ensure!(self.all_names.insert(*name, name_info).is_none(), CustomContractError::NameIsTaken.into());
        let mut owner_state =
            self.state.entry(*owner).or_insert_with(|| AddressState::empty(state_builder));
        owner_state.owned_names.insert(*name);
        Ok(())
    }

    // Register a name if it's present in the registry, but expired
    fn register_expired(
        &mut self,
        now : Timestamp,
        name: &ContractTokenId,
        owner: &AccountAddress,
        state_builder: &mut StateBuilder<S>,
    ) -> ContractResult<()> {
        let name_info = self.all_names.get(name).ok_or::<ContractError>(CustomContractError::InconsistentState.into())?;
        let old_expires = name_info.name_expires;
        // check whether the name has expired
        ensure!(now > old_expires, CustomContractError::NameIsTaken.into());
        // transfer ownership
        self.transfer(name, 1.into(), &Address::Account(name_info.owner), &Address::Account(*owner), state_builder)?;
        Ok(())
    } 

    // Update existing data
    fn update_data(
        &mut self,
        name: &ContractTokenId,
        data: &[u8],
    ) -> ContractResult<()> {
        // Insert and ensure that the key is present
        self.all_names
            .get_mut(&name)
            .map(|mut ni| { ni.data.replace(data.to_vec()) })
            .ok_or::<ContractError>(CustomContractError::InconsistentState.into())?;
        Ok(())
    }

    fn renew (
        &mut self,
        name: &ContractTokenId,
    ) -> ContractResult<()> {
       let mut entry = self.all_names.entry(*name).occupied_or::<ContractError>(CustomContractError::NameNotFound.into())?;
       let new_expires = entry.get_ref().name_expires.checked_add(Duration::from_days(REGISTRATION_PERIOD_DAYS))
                              .ok_or::<ContractError>(CustomContractError::InvokeContractError.into())?;
       entry.modify(|x| x.name_expires=new_expires);
       Ok(())
    }

    /// Check that the token ID currently exists in this contract.
    #[inline(always)]
    fn contains_token(&self, token_id: &ContractTokenId) -> bool {
        self.all_names.get(token_id).is_some()
    }

    /// Get the current balance of a given token ID for a given address.
    /// Results in an error if the token ID does not exist in the state.
    /// Since this contract only contains NFTs, the balance will always be
    /// either 1 or 0.
    fn balance(
        &self,
        token_id: &ContractTokenId,
        address: &Address,
    ) -> ContractResult<ContractTokenAmount> {
        ensure!(self.contains_token(token_id), ContractError::InvalidTokenId);
        let balance = if let Address::Account(addr) = address {
            self    
            .state
            .get(addr)
            .map(|address_state| {
                if address_state.owned_names.contains(token_id) {
                    1
                } else {
                    0
                }
            })
            .unwrap_or(0)
        } else {
            0
        };
        Ok(balance.into())
    }

    /// Check if a given address is an operator of a given owner address.
    fn is_operator(&self, address: &Address, owner: &AccountAddress) -> bool {
        self.state
            .get(owner)
            .map(|address_state| address_state.operators.contains(address))
            .unwrap_or(false)
    }

    /// Update the state with a transfer of some token.
    /// Results in an error if the token ID does not exist in the state or if
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
        // Since this contract only contains NFTs, no one will have an amount greater
        // than 1. And since the amount cannot be the zero at this point, the
        // address must have insufficient funds for any amount other than 1.
        ensure_eq!(amount, 1.into(), ContractError::InsufficientFunds);

        let from_acc = match from {
            Address::Account(addr) => addr,
            Address::Contract(_) => bail!(CustomContractError::OwnerShouldBeAccount.into()) 
        };
        let to_acc = match to {
            Address::Account(addr) => addr,
            Address::Contract(_) => bail!(CustomContractError::OwnerShouldBeAccount.into()) 
        };
        {
          let mut from_address_state =
              self.state.get_mut(from_acc).ok_or(ContractError::InsufficientFunds)?;
          // Find and remove the token from the owner, if nothing is removed, we know the
          // address did not own the token.
          let from_had_the_token = from_address_state.owned_names.remove(token_id);
          ensure!(from_had_the_token, ContractError::InsufficientFunds);
        } 

        // Add the token to the new owner.
        let mut to_address_state =
            self.state.entry(*to_acc).or_insert_with(|| AddressState::empty(state_builder));
        to_address_state.owned_names.insert(*token_id);

        let name_info =
            self.all_names.get(token_id).ok_or(ContractError::InsufficientFunds)?;
        // Add the token to the new owner updating the expiration date.
        // Expiration date is updated in the same way as for registration
        let new_expires = name_info.name_expires
                           .checked_add(Duration::from_days(REGISTRATION_PERIOD_DAYS))
                           .ok_or::<ContractError>(CustomContractError::InvokeContractError.into())?;
        // update the name info (owner and expiration date) keeping data intact
        // the map must contain the token id, if not - return an error
        self.all_names
            .get_mut(&token_id)
            .map(|mut ni| {ni.owner = *to_acc; ni.name_expires = new_expires})
            .ok_or::<ContractError>(CustomContractError::InconsistentState.into())?;
        Ok(())
        
        // if let Some(mut ni) = self.all_names.get_mut(&token_id) {
        //                    ni.owner = *to_acc;
        //                    ni.name_expires = new_expires;
        //                    Ok(())
        //                }
        // else { 
        //    Err(Cis2Error::Custom(CustomContractError::InvokeContractError))
        // }        
    }

    /// Update the state adding a new operator for a given address.
    /// Succeeds even if the `operator` is already an operator for the
    /// `address. If the owner is not an account, return an error
    fn add_operator(
        &mut self,
        owner: &Address,
        operator: &Address,
        state_builder: &mut StateBuilder<S>,
    ) -> ContractResult<()> {
        match owner {
            Address::Account(addr) => {
                let mut owner_state =
                    self.state.entry(*addr).or_insert_with(|| AddressState::empty(state_builder));
                owner_state.operators.insert(*operator);
                Ok(())
            },
            Address::Contract(_) => Err(CustomContractError::OwnerShouldBeAccount.into())
        }
    }
    /// Update the state removing an operator for a given address.
    /// Succeeds even if the `operator` is _not_ an operator for the `address`.
    fn remove_operator(&mut self, owner: &Address, operator: &Address) -> ContractResult<()> {
        match owner {
            Address::Account(addr) =>  {
                self.state.entry(*addr).and_modify(|address_state| {
                    address_state.operators.remove(operator);
                });
                Ok(())
                },
            Address::Contract(_) => Err(CustomContractError::OwnerShouldBeAccount.into())
        }
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

/// Initialize contract instance with no token types initially.
#[init(contract = "nametoken")]
fn contract_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    // Construct the initial contract state.
    Ok(State::empty(state_builder))
}

#[derive(Serialize, SchemaType)]
struct ViewNameInfo {
    owner : AccountAddress,
    name_expires: Timestamp,
    data: Vec<u8>
} 

#[derive(Serialize, SchemaType)]
struct ViewAddressState {
    owned_names: Vec<ContractTokenId>,
    operators:    Vec<Address>,
}

#[derive(Serialize, SchemaType)]
struct ViewState {
    state:     Vec<(AccountAddress, ViewAddressState)>,
    all_names: Vec<(ContractTokenId, ViewNameInfo)>,
    }

fn view_nameinfo<S: HasStateApi>(names : (StateRef<TokenIdFixed<32>>, StateRef<NameInfo<S>>)) -> (TokenIdFixed<32>, ViewNameInfo) {
    let (a_token_id, a_name_info) = names;
    let name_info = ViewNameInfo {
        owner: a_name_info.owner,
        name_expires : a_name_info.name_expires,
        data: a_name_info.data.get().iter().map(|x| *x).collect()
    };
    (*a_token_id, name_info)
}

/// View function that returns the entire contents of the state. Meant for
/// testing.
#[receive(contract = "nametoken", name = "view", return_value = "ViewState")]
fn contract_view<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<ViewState> {
    let state = host.state();

    let mut inner_state = Vec::new();
    for (k, a_state) in state.state.iter() {
        let owned_names = a_state.owned_names.iter().map(|x| *x).collect();
        let operators = a_state.operators.iter().map(|x| *x).collect();
        inner_state.push((*k, ViewAddressState {
            owned_names,
            operators,
        }));
    }
    let all_names = state.all_names.iter().map(|x| view_nameinfo(x)).collect();

    Ok(ViewState {
        state: inner_state,
        all_names,
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
///     - The minted token ID already exists.
///     - Fails to log Mint event
///     - Fails to log TokenMetadata event
///
/// Note: Can at most mint 32 token types in one call due to the limit on the
/// number of logs a smart contract can produce on each function call.
#[receive(
    contract = "nametoken",
    name = "mint",
    crypto_primitives,
    payable,
    parameter = "RegisterNameParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_register<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    amount : Amount,
    logger: &mut impl HasLogger,
    crypto_primitives : &impl HasCryptoPrimitives
) -> ContractResult<()> {
    // Validate the amount
    ensure_eq!(amount, REGISTRACTION_FEE, CustomContractError::IncorrectFee.into());
     // Parse the parameter.
    let params: RegisterNameParams = ctx.parameter_cursor().get()?;
    // Hash the name
    let name_hash = crypto_primitives.hash_sha2_256(&params.name.as_bytes()).0;
    let (state, builder) = host.state_and_builder();
    let now = ctx.metadata().slot_time();
    // calculate the expiration date
    let expires = now.checked_add(Duration::from_days(REGISTRATION_PERIOD_DAYS))
                     .ok_or::<ContractError>(CustomContractError::InvokeContractError.into())?;
    let token_id = TokenIdFixed(name_hash);
    if state.contains_token(&token_id) {
        // token was registered, try to register it as expired
        state.register_expired(now, &token_id, &params.owner, builder)
    } else {
        // token is not registered, make a fresh registration
        state.register_fresh(&token_id, &params.owner, expires, builder)?;
        // Event for minted NFT.
        logger.log(&Cis2Event::Mint(MintEvent {
                token_id,
                amount: ContractTokenAmount::from(1),
                owner: params.owner.into(),
            }))?;
    
        // Metadata URL for the NFT.
        logger.log(&Cis2Event::TokenMetadata::<_, ContractTokenAmount>(TokenMetadataEvent {
                token_id,
                metadata_url: MetadataUrl {
                    url:  build_token_metadata_url(&token_id),
                    hash: None,
                }}))?;
        Ok(())
    }
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
    contract = "nametoken",
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
        let from_acc = match from {
            Address::Account(addr) => addr,
            Address::Contract(_) => bail!(CustomContractError::OwnerShouldBeAccount.into()) 
        };
        // Authenticate the sender for this transfer
        ensure!(from == sender || state.is_operator(&sender, &from_acc), ContractError::Unauthorized);
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

#[receive(
    contract = "nametoken",
    name = "renewName",
    parameter = "String",
    error = "ContractError",
    crypto_primitives,
    payable,
    mutable
)]
fn contract_renew<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    amount: Amount,
    crypto_primitives : &impl HasCryptoPrimitives
) -> ContractResult<()> {
    // Get the sender of the transaction
    let sender = ctx.sender();
    // Validate the amount
    ensure_eq!(amount, RENEWAL_FEE, CustomContractError::IncorrectFee.into());
    // Parse the parameter.
    let name: String = ctx.parameter_cursor().get()?;
    let name_hash = crypto_primitives.hash_sha2_256(&name.as_bytes()).0;
    let state = host.state();
    let token_id = &TokenIdFixed(name_hash);
    let name_info = state.all_names.get(token_id).ok_or(ContractError::Unauthorized)?;
    // Authenticate the sender for this transfer
    ensure!(Address::Account(name_info.owner) == sender || state.is_operator(&sender, &name_info.owner), ContractError::Unauthorized);
    // Renwe the name
    host.state_mut().renew(token_id)
}

#[receive(
    contract = "nametoken",
    name = "updateData",
    parameter = "UpdateDataParams",
    error = "ContractError",
    crypto_primitives,
    payable,
    mutable
)]
fn contract_update_data<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    amount: Amount,
    crypto_primitives : &impl HasCryptoPrimitives
) -> ContractResult<()> {
    // Get the sender of the transaction
    let sender = ctx.sender();
    // Validate the amount
    ensure_eq!(amount, UPDATE_FEE, CustomContractError::IncorrectFee.into());
    // Parse the parameter.
    let params: UpdateDataParams = ctx.parameter_cursor().get()?;
    // Hash the name
    let name_hash = crypto_primitives.hash_sha2_256(&params.name.as_bytes()).0;
    let state = host.state_mut();
    let name_info = state.all_names.get(&TokenIdFixed(name_hash)).ok_or::<ContractError>(CustomContractError::NameNotFound.into())?;
    let owner = name_info.owner;
    // Authenticate the sender for this transfer
    ensure!(Address::Account(owner) == sender || state.is_operator(&sender, &owner), ContractError::Unauthorized);
    state.update_data(&TokenIdFixed(name_hash), params.data.as_slice())
}

/// Enable or disable addresses as operators of the sender address.
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Fails to log event.
#[receive(
    contract = "nametoken",
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
            OperatorUpdate::Add => state.add_operator(&sender, &param.operator, builder)?,
            OperatorUpdate::Remove => state.remove_operator(&sender, &param.operator)?,
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

/// Takes a list of queries. Each query is an owner address and some address to
/// check as an operator of the owner address.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "nametoken",
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
        let owner = match query.owner {
            Address::Account(addr) => addr,
            Address::Contract(_) => bail!(CustomContractError::OwnerShouldBeAccount.into())
        };
        // Query the state for address being an operator of owner.
        let is_operator = host.state().is_operator(&query.address, &owner);
        response.push(is_operator);
    }
    let result = OperatorOfQueryResponse::from(response);
    Ok(result)
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
    contract = "nametoken",
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

/// Parameter type for the CIS-2 function `tokenMetadata` specialized to the
/// subset of TokenIDs used by this contract.
type ContractTokenMetadataQueryParams = TokenMetadataQueryParams<ContractTokenId>;

/// Get the token metadata URLs and checksums given a list of token IDs.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "nametoken",
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

/// Get the supported standards or addresses for a implementation given list of
/// standard identifiers.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "nametoken",
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
    contract = "nametoken",
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
    use concordium_std::test_infrastructure::*;

    const CURRENT_TIME: u64 = 1;
    const ACCOUNT_0: AccountAddress = AccountAddress([0u8; 32]);
    const ADDRESS_0: Address = Address::Account(ACCOUNT_0);
    const ACCOUNT_1: AccountAddress = AccountAddress([1u8; 32]);
    const ADDRESS_1: Address = Address::Account(ACCOUNT_1);
    const NAME_0: &str = "google.com";
    const NAME_1: &str = "concordium.com";
    //const TOKEN_2: ContractTokenId = TokenIdU32(43);

    /// Test helper function which creates a contract state with two tokens with
    /// id `TOKEN_0` and id `TOKEN_1` owned by `ADDRESS_0`
    fn initial_state<S: HasStateApi>(expires: Timestamp, state_builder: &mut StateBuilder<S>) -> State<S> {
        let mut state = State::empty(state_builder);
        let crypto_primitives = TestCryptoPrimitives::new();
        let token_0 = crypto_primitives.hash_sha2_256(NAME_0.as_bytes()).0;
        let token_1 = crypto_primitives.hash_sha2_256(NAME_1.as_bytes()).0;
        state.register_fresh(&TokenIdFixed(token_0), &ACCOUNT_0, expires, state_builder).expect_report("Failed to register NAME_0");
        state.register_fresh(&TokenIdFixed(token_1), &ACCOUNT_1, expires, state_builder).expect_report("Failed to register NAME_1");
        //state.mint(TOKEN_1, &ADDRESS_0, state_builder).expect_report("Failed to mint TOKEN_1");
        state
    }

    /// Test registering a fresh name, ensuring the the name is owned by the given address and
    /// the appropriate events are logged.
    #[concordium_test]
    #[cfg(feature = "crypto-primitives")]
    fn test_register_fresh() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(CURRENT_TIME));
        ctx.set_sender(ADDRESS_0.into());
        ctx.set_owner(ACCOUNT_0);

        // and parameter.
        let parameter = RegisterNameParams {
            name: NAME_0.to_string(),
            owner: ACCOUNT_0,
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::empty(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        let crypto_primitives = TestCryptoPrimitives::new();

        // Call the contract function.
        let result: ContractResult<()> = contract_register(&ctx, &mut host, REGISTRACTION_FEE, &mut logger, &crypto_primitives);

        // Check the result
        claim!(result.is_ok(), "Results in rejection");

        let token_0 = TokenIdFixed(crypto_primitives.hash_sha2_256(NAME_0.as_bytes()).0);

        // Check the state
        // Note. This is rather expensive as an iterator is created and then traversed -
        // should be avoided when writing smart contracts.
        claim_eq!(host.state().all_names.iter().count(), 1, "Expected one name in all names.");
        claim_eq!(host.state().state.iter().count(), 1, "Expected one name in the state.");
        
        let name_info = host.state().all_names.get(&token_0).expect_report("Token is expected to exist");
        claim_eq!(name_info.owner, ACCOUNT_0, "The name must be owned by ACCOUNT_0");
        
        let addr_state = host.state().state.get(&ACCOUNT_0).expect_report("ACCOUNT_0 must own a name");
        claim!(addr_state.owned_names.contains(&token_0), "ACCOUNT_0 must own token 0");

        let balance0 =
            host.state().balance(&token_0, &ACCOUNT_0.into()).expect_report("Token is expected to exist");
        claim_eq!(balance0, 1.into(), "Token balance should be non-zero");

        // Check the logs
        claim!(
            logger.logs.contains(&to_bytes(&Cis2Event::Mint(MintEvent {
                owner:    ADDRESS_0,
                token_id: token_0,
                amount:   ContractTokenAmount::from(1),
            }))),
            "Expected an event for minting NAME_0"
        );
    }

    /// Test registering an expired name, ensuring the the name is owned by the new given address
    #[concordium_test]
    #[cfg(feature = "crypto-primitives")]
    fn test_register_expired() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        let old_owner = ACCOUNT_0;
        let new_owner = ACCOUNT_1;

        // the time of expiry in the past
        let old_expiry = Timestamp::from_timestamp_millis(1);
        
        // ensure that the current date is beyond the expiry date,
        // so we can register the expired name
        let now = old_expiry
                    .checked_add(Duration::from_days(10))
                    .expect_report("Failed to calculate the date");
        ctx.set_metadata_slot_time(now);
        ctx.set_sender(ADDRESS_0.into());
        ctx.set_owner(old_owner);

        // and parameter.
        let parameter = RegisterNameParams {
            name: NAME_0.to_string(),
            owner: new_owner,
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();

        // create initial state where NAME_0 was owned by ACCOUNT_1
        let state = initial_state(old_expiry, &mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        let crypto_primitives = TestCryptoPrimitives::new();

        // Call the contract function.
        let result: ContractResult<()> = contract_register(&ctx, &mut host, REGISTRACTION_FEE, &mut logger, &crypto_primitives);

        // Check the result
        claim!(result.is_ok(), "Results in rejection");

        let token_0 = TokenIdFixed(crypto_primitives.hash_sha2_256(NAME_0.as_bytes()).0);

        let name_info = host.state().all_names.get(&token_0).expect_report("Token is expected to exist");
        claim_eq!(name_info.owner, new_owner, "The name must be owned by the new owner");
        
        let addr_state = host.state().state.get(&new_owner).expect_report("The new owner must own a name");
        claim!(addr_state.owned_names.contains(&token_0), "The new owner must own the name");

        let balance_new =
            host.state().balance(&token_0, &new_owner.into()).expect_report("Token is expected to exist");
        claim_eq!(balance_new, 1.into(), "Token balance should be non-zero");

        let balance_old =
            host.state().balance(&token_0, &old_owner.into()).expect_report("Token is expected to exist");
        claim_eq!(balance_old, 0.into(), "Token balance should be zero");

        // Check the logs, there should be no record for minting, 
        // because it's a registration of an expired name
        claim_eq!(
            logger.logs.contains(&to_bytes(&Cis2Event::Mint(MintEvent {
                owner:    new_owner.into(),
                token_id: token_0,
                amount:   ContractTokenAmount::from(1),
            }))),
            false,
            "Expected an event for minting NAME_0"
        );
    }

    #[concordium_test]
    #[cfg(feature = "crypto-primitives")]
    fn test_register_fails_incorrect_fee() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(CURRENT_TIME));
        ctx.set_sender(ADDRESS_0.into());
        ctx.set_owner(ACCOUNT_0);

        // and parameter.
        let parameter = RegisterNameParams {
            name: NAME_0.to_string(),
            owner: ACCOUNT_0,
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = State::empty(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        let crypto_primitives = TestCryptoPrimitives::new();

        // Call the contract function wiht zero cdd
        let result: ContractResult<()> = contract_register(&ctx, &mut host, Amount::from_ccd(0), &mut logger, &crypto_primitives);

        // Check the result
        let err = result.expect_err_report("Expected to fail");
        claim_eq!(err, ContractError::Custom(CustomContractError::IncorrectFee), "Error is expected to be IncorrectFee");
    }



    
}
