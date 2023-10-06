//! A NameToken smart contract example using the Concordium Token Standard
//! CIS2.
//!
//! # Description
//! A contract that allows for registering and managing names. A name can be
//! used as a verifiable human-readable name for an address. They also can have
//! some data attached, like website URLs, accounts in various systems, etc.
//! Only account addresses can be owners. The ownership can be transferred to
//! another account address.
//!
//! # Operations
//! The contract allows for
//!  - registering new names;
//!  - updating data associated with a name;
//!  - renewing a name;
//!  - viewing information about a name (owner and data).
//!
//! To register, renew and update one has to pay a fee. Registration succeeds if
//! either name is not yet registered, or it is registered but expired. In this
//! case, ownership is transferred to the new owner and the expiration date is
//! updated as for the "fresh" registration. Updating data and renewing is only
//! possible if the name is not expired.
//!
//! # Token
//! NameToken is essentially an NFT that adheres to the CIS-2 token standard.
//! This allows for trading of domain names on NFT auctions. The contract is
//! based on the NFT example with modifications required for the name
//! management. Registering a fresh name is effectively minting. It generates
//! log events accordingly. However, taking over an expired name is not
//! considered minting. Ownership can be transferred by the owner or by an
//! operator. Owners are accounts only, but operators can be any address. Token
//! ownership is determined by the expiration date. Expired name tokens are not
//! burned, they are considered as not owned, that is the balance is 0 for the
//! address it was initially registered.
//!
//! Note: token ids are hashed names. The words "name" and "token id" are used
//! interchangeably.
//!
//! # Misc
//! This example demonstrates how to use crypto primitives (hashing) and
//! lazy-loaded data.

#![cfg_attr(not(feature = "std"), no_std)]

use concordium_cis2::*;
use concordium_std::*;

/// The baseurl for the token metadata, gets appended with the token ID as hex
/// encoding before emitted in the TokenMetadata event.
pub const TOKEN_METADATA_BASE_URL: &str = "https://some.example/nametoken/";

/// List of supported standards by this contract address.
pub const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 2] =
    [CIS0_STANDARD_IDENTIFIER, CIS2_STANDARD_IDENTIFIER];

// Fees

/// Registration fee in CCD
pub const REGISTRATION_FEE: Amount = Amount::from_ccd(70);

/// Data update fee in CCD
pub const UPDATE_FEE: Amount = Amount::from_ccd(7);

/// Renewal fee in CCD
pub const RENEWAL_FEE: Amount = Amount::from_ccd(7);

/// How long the registered name is owned before it needs to be renewed
pub const REGISTRATION_PERIOD_DAYS: u64 = 365;

// Types

/// Contract token ID type.
/// We pick `TokenIdFixed`, since we hash names with sha256, that gives a
/// fixed-length 32 byte array.
pub type ContractTokenId = TokenIdFixed<32>;

/// Contract token amount. Since the tokens are non-fungible the total supply
/// of any token will be at most 1 and it is fine to use a small type for
/// representing token amounts.
pub type ContractTokenAmount = TokenAmountU8;

/// The parameter for the contract function `register` which registers a name
/// for a given address.
#[derive(Serial, Deserial, SchemaType)]
pub struct RegisterNameParams {
    /// Owner of the newly registered name
    pub owner: AccountAddress,
    /// Name
    pub name:  String,
}

/// Data for each name.
#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
pub struct NameInfo<S: HasStateApi = StateApi> {
    /// Name owner
    pub owner:        AccountAddress,
    /// Expiration date
    pub name_expires: Timestamp,
    /// Associated data
    // `StateBox` allows for lazy loading data; this is helpful
    // in the situations when one wants to do a partial update not touching
    // this field, which can be large.
    pub data: StateBox<Vec<u8>, S>,
}

impl NameInfo {
    fn fresh(
        owner: AccountAddress,
        name_expires: Timestamp,
        state_builder: &mut StateBuilder,
    ) -> Self {
        NameInfo {
            owner,
            name_expires,
            data: state_builder.new_box(Vec::new()),
        }
    }
}

/// The state for each address.
#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
pub struct AddressState<S = StateApi> {
    /// The tokens owned by this address.
    pub owned_names: StateSet<ContractTokenId, S>,
    /// The address which are currently enabled as operators for this address.
    pub operators:   StateSet<Address, S>,
}

impl AddressState {
    fn empty(state_builder: &mut StateBuilder) -> Self {
        AddressState {
            owned_names: state_builder.new_set(),
            operators:   state_builder.new_set(),
        }
    }
}

/// The contract state.

#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S: HasStateApi = StateApi> {
    /// The address of the administrating account.
    /// Admin can withdraw the accumulated fees and update the admin account.
    admin:        AccountAddress,
    /// The state for each account address.
    state:        StateMap<AccountAddress, AddressState<S>, S>,
    /// All of the token IDs
    all_names:    StateMap<ContractTokenId, NameInfo<S>, S>,
    /// Map with contract addresses providing implementations of additional
    /// standards.
    implementors: StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
}

/// The parameter type for the contract function `setImplementors`. Takes a
/// standard identifier and list of contract addresses providing
/// implementations of this standard.
#[derive(Debug, Serialize, SchemaType)]
pub struct SetImplementorsParams {
    /// The identifier for the standard.
    pub id:           StandardIdentifierOwned,
    /// The addresses of the implementors of the standard.
    pub implementors: Vec<ContractAddress>,
}

#[derive(Debug, Serialize, SchemaType)]
pub struct UpdateDataParams {
    pub name: String,
    pub data: Vec<u8>,
}

/// The custom errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
pub enum CustomContractError {
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
    /// Some invariants of the state are broken
    InconsistentState,
    /// Failed to invoke a contract.
    InvokeContractError,
    /// Name is not found in the registry
    NameNotFound,
    /// Provided amount is to large (used for transfers to admin)
    AdminAmountTooLarge,
    /// Admin account not found
    MissingAdminAccount,
    /// Name has expired
    NameExpired,
    /// Overflow for numeric operations
    OverflowError,
}

/// Wrapping the custom errors in a type with CIS2 errors.
pub type ContractError = Cis2Error<CustomContractError>;

pub type ContractResult<A> = Result<A, ContractError>;

/// Mapping the logging errors to CustomContractError.
impl From<LogError> for CustomContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

/// Mapping the transfer errors to CustomContractError.
impl From<TransferError> for CustomContractError {
    fn from(le: TransferError) -> Self {
        match le {
            TransferError::AmountTooLarge => Self::AdminAmountTooLarge,
            TransferError::MissingAccount => Self::MissingAdminAccount,
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
impl State {
    /// Creates a new state with no tokens.
    fn empty(admin: AccountAddress, state_builder: &mut StateBuilder) -> Self {
        State {
            admin,
            state: state_builder.new_map(),
            all_names: state_builder.new_map(),
            implementors: state_builder.new_map(),
        }
    }

    /// Register a name if it's not taken
    fn register_fresh(
        &mut self,
        name: ContractTokenId,
        owner: AccountAddress,
        expires: Timestamp,
        state_builder: &mut StateBuilder,
    ) -> ContractResult<()> {
        let name_info = NameInfo::fresh(owner, expires, state_builder);
        // make sure that the name is not taken
        ensure!(
            self.all_names.insert(name, name_info).is_none(),
            CustomContractError::NameIsTaken.into()
        );
        let mut owner_state =
            self.state.entry(owner).or_insert_with(|| AddressState::empty(state_builder));
        owner_state.owned_names.insert(name);
        Ok(())
    }

    /// Register a name if it's present in the registry, but expired
    fn register_expired(
        &mut self,
        now: Timestamp,
        name: ContractTokenId,
        owner: AccountAddress,
        state_builder: &mut StateBuilder,
    ) -> ContractResult<AccountAddress> {
        let mut name_info = self
            .all_names
            .get_mut(&name)
            .ok_or(ContractError::Custom(CustomContractError::InconsistentState))?;
        let old_expires = name_info.name_expires;
        // Check whether the name has expired
        ensure!(now > old_expires, CustomContractError::NameIsTaken.into());

        let old_owner = name_info.owner;

        let new_expires = now
            .checked_add(Duration::from_days(REGISTRATION_PERIOD_DAYS))
            .ok_or(ContractError::Custom(CustomContractError::OverflowError))?;
        // Update expiration date
        name_info.name_expires = new_expires;
        // Replace old data with an empty vector
        let old_data = mem::replace(&mut name_info.data, state_builder.new_box(Vec::new()));
        // and delete old data to avoid space leaks
        old_data.delete();
        drop(name_info);

        // transfer ownership
        self.transfer(
            &name,
            1.into(),
            &Address::Account(old_owner),
            &Address::Account(owner),
            state_builder,
        )?;

        Ok(old_owner)
    }

    /// Update existing data
    fn update_data(&mut self, name: &ContractTokenId, data: &[u8]) -> ContractResult<()> {
        // Insert and ensure that the key is present
        self.all_names
            .get_mut(name)
            .map(|mut ni| ni.data.replace(data.to_vec()))
            .ok_or(ContractError::Custom(CustomContractError::InconsistentState))?;
        Ok(())
    }

    /// Renew an existing name
    fn renew(&mut self, name: &ContractTokenId) -> ContractResult<()> {
        let mut entry = self
            .all_names
            .entry(*name)
            .occupied_or(ContractError::Custom(CustomContractError::NameNotFound))?;
        let new_expires = entry
            .get_ref()
            .name_expires
            .checked_add(Duration::from_days(REGISTRATION_PERIOD_DAYS))
            .ok_or(ContractError::Custom(CustomContractError::OverflowError))?;
        entry.modify(|x| x.name_expires = new_expires);
        Ok(())
    }

    /// Check that the token ID currently exists in this contract.
    #[inline(always)]
    fn contains_token(&self, token_id: &ContractTokenId) -> bool {
        self.all_names.get(token_id).is_some()
    }

    /// Get the current balance of a given token ID for a given address.
    /// Results in an error if the token ID does not exist in the state. Since
    /// this contract only contains NFTs, the balance will always be either 1
    /// or 0.
    //  For maintainers: Ignoring the clippy warning as the suggestion is less readable.
    #[allow(clippy::bool_to_int_with_if)]
    fn balance(
        &self,
        now: Timestamp,
        token_id: &ContractTokenId,
        address: &Address,
    ) -> ContractResult<ContractTokenAmount> {
        ensure!(self.contains_token(token_id), ContractError::InvalidTokenId);
        let name_info = self.all_names.get(token_id).ok_or(ContractError::InvalidTokenId)?;
        let balance = if let Address::Account(addr) = address {
            self.state
                .get(addr)
                .map(|address_state| {
                    // tokens are only considered owned by an address if they are not expired
                    if address_state.owned_names.contains(token_id) && now <= name_info.name_expires
                    {
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
    //  Note: data associated with the name (token_id) is remains untouched after
    //  transfer.  Alternatively, one might consider erasing it.
    fn transfer(
        &mut self,
        token_id: &ContractTokenId,
        amount: ContractTokenAmount,
        from: &Address,
        to: &Address,
        state_builder: &mut StateBuilder,
    ) -> ContractResult<()> {
        ensure!(self.contains_token(token_id), ContractError::InvalidTokenId);

        // Make sure that addresses are accounts
        let from_acc = match from {
            Address::Account(addr) => addr,
            Address::Contract(_) => bail!(CustomContractError::OwnerShouldBeAccount.into()),
        };
        let to_acc = match to {
            Address::Account(addr) => addr,
            Address::Contract(_) => bail!(CustomContractError::OwnerShouldBeAccount.into()),
        };
        // A zero transfer does not modify the state.
        if amount == 0.into() {
            return Ok(());
        }
        // Since this contract only contains NFTs, no one will have an amount greater
        // than 1. And since the amount cannot be the zero at this point, the
        // address must have insufficient funds for any amount other than 1.
        ensure_eq!(amount, 1.into(), ContractError::InsufficientFunds);

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

        self.all_names
            .get_mut(token_id)
            .map(|mut ni| ni.owner = *to_acc)
            .ok_or(ContractError::Custom(CustomContractError::InconsistentState))?;
        Ok(())
    }

    /// Update the state adding a new operator for a given address.
    /// Succeeds even if the `operator` is already an operator for the
    /// `address. If the owner is not an account, return an error
    fn add_operator(
        &mut self,
        owner: &Address,
        operator: &Address,
        state_builder: &mut StateBuilder,
    ) -> ContractResult<()> {
        match owner {
            Address::Account(addr) => {
                let mut owner_state =
                    self.state.entry(*addr).or_insert_with(|| AddressState::empty(state_builder));
                owner_state.operators.insert(*operator);
                Ok(())
            }
            Address::Contract(_) => Err(CustomContractError::OwnerShouldBeAccount.into()),
        }
    }

    /// Update the state removing an operator for a given address.
    /// Succeeds even if the `operator` is _not_ an operator for the `address`.
    fn remove_operator(&mut self, owner: &Address, operator: &Address) -> ContractResult<()> {
        match owner {
            Address::Account(addr) => {
                self.state.entry(*addr).and_modify(|address_state| {
                    address_state.operators.remove(operator);
                });
                Ok(())
            }
            Address::Contract(_) => Err(CustomContractError::OwnerShouldBeAccount.into()),
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
pub fn build_token_metadata_url(token_id: &ContractTokenId) -> String {
    let mut token_metadata_url = String::from(TOKEN_METADATA_BASE_URL);
    token_metadata_url.push_str(&token_id.to_string());
    token_metadata_url
}

// Contract functions

/// Initialize contract instance with no token types initially.
/// Set the account that initialised the contract to be admin
#[init(contract = "NameToken")]
fn contract_init(ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<State> {
    // Construct the initial contract state.
    Ok(State::empty(ctx.init_origin(), state_builder))
}

#[derive(Serialize, SchemaType, PartialEq, Eq, Debug)]
pub struct ViewNameInfo {
    pub owner:        AccountAddress,
    pub name_expires: Timestamp,
    pub data:         Vec<u8>,
}

#[derive(Serialize, SchemaType, PartialEq, Eq, Debug)]
pub struct ViewAddressState {
    pub owned_names: Vec<ContractTokenId>,
    pub operators:   Vec<Address>,
}

#[derive(Serialize, SchemaType, PartialEq, Eq, Debug)]
pub struct ViewState {
    pub state:     Vec<(AccountAddress, ViewAddressState)>,
    pub all_names: Vec<(ContractTokenId, ViewNameInfo)>,
}

fn into_view_name_info(name_info: &NameInfo) -> ViewNameInfo {
    ViewNameInfo {
        owner:        name_info.owner,
        name_expires: name_info.name_expires,
        data:         name_info.data.get().to_vec(),
    }
}

fn view_nameinfo(
    name: (StateRef<TokenIdFixed<32>>, StateRef<NameInfo>),
) -> (TokenIdFixed<32>, ViewNameInfo) {
    let (a_token_id, a_name_info) = name;
    let name_info = into_view_name_info(&a_name_info);
    (*a_token_id, name_info)
}

/// View function that returns the entire contents of the state. Meant for
/// testing.
#[receive(contract = "NameToken", name = "view", return_value = "ViewState")]
fn contract_view(_ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<ViewState> {
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
    let all_names = state.all_names.iter().map(view_nameinfo).collect();

    Ok(ViewState {
        state: inner_state,
        all_names,
    })
}

/// Query the info about a name.
/// The name is expected to be a string.
///
/// It rejects if:
/// - Fails to parse parameter.
/// - Name doesn't exist
#[receive(
    contract = "NameToken",
    name = "viewNameInfo",
    crypto_primitives,
    parameter = "String",
    return_value = "ViewNameInfo",
    error = "ContractError"
)]
fn contract_nameinfo_view(
    ctx: &ReceiveContext,
    host: &Host<State>,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<ViewNameInfo> {
    let params: String = ctx.parameter_cursor().get()?;
    let name_hash = crypto_primitives.hash_sha2_256(params.as_bytes()).0;
    let name_info = host
        .state()
        .all_names
        .get(&TokenIdFixed(name_hash))
        .ok_or(ContractError::Custom(CustomContractError::NameNotFound))?;
    Ok(into_view_name_info(&name_info))
}

/// Register a new name with a given address as the owner. The name
/// parameter is a string, which is then hashed and used as a token id. Can
/// be called by anyone, but requires to pay a registration fee.
///
/// Two scenarios are possible
/// - Register a fresh name (not previously registered); considered as minting.
///   In this case, logs a `Mint` and a `TokenMetadata` event for the new name
///   token. The url for the token metadata is the token ID encoded in hex,
///   appended on the`TOKEN_METADATA_BASE_URL`.
///
///   It rejects if:
///   - Fee is incorrect.
///   - Fails to parse parameter.
///   - Overflows when calculating the expiration date.
///   - The token fails to be minted, which could be if:
///       - Fails to log `Mint` event
///       - Fails to log `TokenMetadata` event
///
/// - Register an expired name, that is, a name that was previously registered,
///   but has expired now. In this case logs a `Transfer` event, since the
///   ownership is transfered.
///
///   It rejects if:
///   - Fee is incorrect.
///   - Fails to parse parameter.
///   - Overflows when calculating the expiration date.
///   - The token exists, but has not expired.
///   - The token fails to be transfered, which could be if:
///       - Fails to log `Transfer` event
#[receive(
    contract = "NameToken",
    name = "register",
    crypto_primitives,
    payable,
    parameter = "RegisterNameParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_register(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    amount: Amount,
    logger: &mut impl HasLogger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<()> {
    // Validate the amount
    ensure_eq!(amount, REGISTRATION_FEE, CustomContractError::IncorrectFee.into());
    // Parse the parameter.
    let params: RegisterNameParams = ctx.parameter_cursor().get()?;
    // Hash the name
    let name_hash = crypto_primitives.hash_sha2_256(params.name.as_bytes()).0;
    let (state, builder) = host.state_and_builder();
    let now = ctx.metadata().slot_time();
    // Calculate the expiration date
    let expires = now
        .checked_add(Duration::from_days(REGISTRATION_PERIOD_DAYS))
        .ok_or(ContractError::Custom(CustomContractError::OverflowError))?;
    let token_id = TokenIdFixed(name_hash);
    if state.contains_token(&token_id) {
        // Token was registered, try to register it as expired
        let old_owner = state.register_expired(now, token_id, params.owner, builder)?;

        // Log transfer event
        logger.log(&Cis2Event::Transfer(TransferEvent {
            token_id,
            amount: ContractTokenAmount::from(1),
            from: Address::Account(old_owner),
            to: Address::Account(params.owner),
        }))?;
        Ok(())
    } else {
        // Token is not registered, make a fresh registration
        state.register_fresh(token_id, params.owner, expires, builder)?;
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
            },
        }))?;
        Ok(())
    }
}

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
///     - `from` or `to` are not account addresses.
/// - Fails to log event.
#[receive(
    contract = "NameToken",
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
    // Parse the parameter.
    let TransferParams(transfers): TransferParameter = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();
    // Get current block time
    let now = ctx.metadata().slot_time();

    for Transfer {
        token_id,
        amount,
        from,
        to,
        data: _,
    } in transfers
    {
        let to_address = to.address();
        // Fail early it one of the address is not account
        let to_acc = match to_address {
            Address::Account(addr) => addr,
            Address::Contract(_) => bail!(CustomContractError::OwnerShouldBeAccount.into()),
        };
        let from_acc = match from {
            Address::Account(addr) => addr,
            Address::Contract(_) => bail!(CustomContractError::OwnerShouldBeAccount.into()),
        };

        let (state, builder) = host.state_and_builder();
        // Authenticate the sender for this transfer
        ensure!(
            from == sender || state.is_operator(&sender, &from_acc),
            ContractError::Unauthorized
        );
        let name_info = state.all_names.get(&token_id).ok_or(ContractError::Unauthorized)?;
        // It's possible to transefer only if the name is not expired
        ensure!(now <= name_info.name_expires, CustomContractError::NameExpired.into());
        // Update the contract state
        state.transfer(&token_id, amount, &from, &Address::Account(to_acc), builder)?;

        // At this point we know that `from` and `to` are accounts, so we do not call
        // the receive hook function
        logger.log(&Cis2Event::Transfer(TransferEvent {
            token_id,
            amount,
            from,
            to: to_address,
        }))?;
    }
    Ok(())
}

/// Renew a name by updating its expiration date
///  It rejects if:
/// - Fee is incorrect
/// - It fails to parse the parameter.
/// - Name doesn't exist
/// - Name expired
/// - The sender is not the owner of the token, or an operator for this specific
///   `token_id` and `owner` address of the name.
#[receive(
    contract = "NameToken",
    name = "renewName",
    parameter = "String",
    error = "ContractError",
    crypto_primitives,
    payable,
    mutable
)]
fn contract_renew(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    amount: Amount,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<()> {
    // Validate the amount
    ensure_eq!(amount, RENEWAL_FEE, CustomContractError::IncorrectFee.into());
    // Get the sender of the transaction
    let sender = ctx.sender();
    // Parse the parameter.
    let name: String = ctx.parameter_cursor().get()?;
    let name_hash = crypto_primitives.hash_sha2_256(name.as_bytes()).0;
    let token_id = &TokenIdFixed(name_hash);
    let state = host.state();
    let name_info = state
        .all_names
        .get(token_id)
        .ok_or(ContractError::Custom(CustomContractError::NameNotFound))?;
    let expires = name_info.name_expires;
    // Authenticate the sender for this transfer
    ensure!(
        Address::Account(name_info.owner) == sender || state.is_operator(&sender, &name_info.owner),
        ContractError::Unauthorized
    );
    // Ensure that the name has not expired
    let now = ctx.metadata().slot_time();
    ensure!(now <= expires, CustomContractError::NameExpired.into());
    // Renew the name
    host.state_mut().renew(token_id)
}

#[receive(
    contract = "NameToken",
    name = "withdraw",
    parameter = "Amount",
    error = "ContractError",
    mutable
)]
fn contract_withdraw(ctx: &ReceiveContext, host: &mut Host<State>) -> ContractResult<()> {
    // Get the contract admin
    let admin = host.state().admin;
    // Get the sender of the transaction
    let sender = ctx.sender();
    // Only admin can withdraw
    ensure!(sender.matches_account(&admin), ContractError::Unauthorized);

    // Read the parameter
    let amount: Amount = ctx.parameter_cursor().get()?;

    Ok(host.invoke_transfer(&admin, amount)?)
}

#[receive(
    contract = "NameToken",
    name = "updateAdmin",
    parameter = "AccountAddress",
    error = "ContractError",
    mutable
)]
fn contract_update_admin(ctx: &ReceiveContext, host: &mut Host<State>) -> ContractResult<()> {
    // Get the contract admin
    let admin = host.state().admin;

    // Get the sender of the transaction
    let sender = ctx.sender();

    // Only admin can update the admin address
    ensure!(sender.matches_account(&admin), ContractError::Unauthorized);

    // Read the parameter
    let new_admin: AccountAddress = ctx.parameter_cursor().get()?;

    let state = host.state_mut();
    state.admin = new_admin;
    Ok(())
}

/// Update data associated with a name
///
/// It rejects if:
/// - Fee is incorrect
/// - It fails to parse the parameter.
/// - Name doesn't exist
/// - Name expired
/// - The sender is not the owner of the token, or an operator for this specific
///   `token_id` and `owner` address of the name.
#[receive(
    contract = "NameToken",
    name = "updateData",
    parameter = "UpdateDataParams",
    error = "ContractError",
    crypto_primitives,
    payable,
    mutable
)]
fn contract_update_data(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    amount: Amount,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<()> {
    // Get the sender of the transaction
    let sender = ctx.sender();
    // Validate the amount
    ensure_eq!(amount, UPDATE_FEE, CustomContractError::IncorrectFee.into());
    // Parse the parameter.
    let params: UpdateDataParams = ctx.parameter_cursor().get()?;
    // Hash the name
    let name_hash = crypto_primitives.hash_sha2_256(params.name.as_bytes()).0;
    let state = host.state_mut();
    let name_info = state
        .all_names
        .get(&TokenIdFixed(name_hash))
        .ok_or(ContractError::Custom(CustomContractError::NameNotFound))?;
    let owner = name_info.owner;
    // Authenticate the sender for this transfer
    ensure!(
        Address::Account(owner) == sender || state.is_operator(&sender, &owner),
        ContractError::Unauthorized
    );
    // Ensure that the name is not expired
    let now = ctx.metadata().slot_time();
    ensure!(now <= name_info.name_expires, CustomContractError::NameExpired.into());
    state.update_data(&TokenIdFixed(name_hash), params.data.as_slice())
}

/// Enable or disable addresses as operators of the sender address.
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Fails to log event.
#[receive(
    contract = "NameToken",
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
    contract = "NameToken",
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
        let owner = match query.owner {
            Address::Account(addr) => addr,
            Address::Contract(_) => bail!(CustomContractError::OwnerShouldBeAccount.into()),
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
pub type ContractBalanceOfQueryParams = BalanceOfQueryParams<ContractTokenId>;
/// Response type for the CIS-2 function `balanceOf` specialized to the subset
/// of TokenAmounts used by this contract.
pub type ContractBalanceOfQueryResponse = BalanceOfQueryResponse<ContractTokenAmount>;

/// Get the balance of given token IDs and addresses.
/// The balance is considered 0 if the name has expired.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "NameToken",
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
    let now = ctx.metadata().slot_time();
    for query in params.queries {
        // Query the state for balance.
        let amount = host.state().balance(now, &query.token_id, &query.address)?;
        response.push(amount);
    }
    let result = ContractBalanceOfQueryResponse::from(response);
    Ok(result)
}

/// Parameter type for the CIS-2 function `tokenMetadata` specialized to the
/// subset of TokenIDs used by this contract.
pub type ContractTokenMetadataQueryParams = TokenMetadataQueryParams<ContractTokenId>;

/// Get the token metadata URLs and checksums given a list of token IDs.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "NameToken",
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

/// Get the supported standards or addresses for a implementation given list of
/// standard identifiers.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "NameToken",
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
    contract = "NameToken",
    name = "setImplementors",
    parameter = "SetImplementorsParams",
    error = "ContractError",
    mutable
)]
fn contract_set_implementor(ctx: &ReceiveContext, host: &mut Host<State>) -> ContractResult<()> {
    // Authorize the sender.
    ensure!(ctx.sender().matches_account(&host.state().admin), ContractError::Unauthorized);
    // Parse the parameter.
    let params: SetImplementorsParams = ctx.parameter_cursor().get()?;
    // Update the implementors in the state
    host.state_mut().set_implementors(params.id, params.implementors);
    Ok(())
}
