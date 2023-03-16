//! A NFT smart contract example using the Concordium Token Standard CIS2 with
//! sponsored transactions (CIS3).
//!
//! # Description
//! An instance of this smart contract can contain a number of different tokens
//! each identified by a token ID. A token is then globally identified by the
//! contract address together with the token ID.
//!
//! In this example the contract is initialized with no tokens, and tokens can
//! be minted through a `mint` contract function, which will only succeed for
//! the contract owner. No functionality to burn token is defined in this
//! example.
//!
//! Note: The word 'address' refers to either an account address or a
//! contract address.
//!
//! This contract implements the Concordium Token Standard CIS2. In addition, it
//! implements the CIS3 standard which includes features for sponsored
//! transactions.
//!
//! The use case for this smart contract is for third-party service providers
//! (the owner of this contract) that deal with conventional clients/users that
//! don't want to acquire crypto (such as CCD) from an exchange. The third-party
//! has often traditional fiat channels open (off-chain) with the conventional
//! clients/users and wants to offer to submit transactions on behalf of the
//! user on-chain. The user/client has to sign its intended transaction before
//! communicating it (off-chain) to the third-party service provider
//! (often paying some fees in fiat money). The third-party service provider
//! submits the transaction on behalf of the user and pays the transaction fee
//! to execute the transaction on-chain.
//!
//! Concordium smart contracts currently have no way to query the corresponding
//! public key(s) of an account within the smart contract code. For
//! the time being this smart contract uses a `public_key_registry` that
//! allows only the owner of the contract instance (or the account itself) to
//! register a public key for a given account. Once an account has a public key
//! registered, the mapping between the public key and the account can not be
//! updated anymore. The users/clients are advised to check if the correct
//! public key is registered to their account or register a public key
//! themselves (if they don't want to make use of the sponsored transaction
//! feature of this smart contract). This smart contract assumes a
//! trusted third-party service provider since the use case is for users/clients
//! that pay fiat money off-chain to the third-party service to request the
//! submission of sponsored transactions on their behalf.
//!
//! The Concordium team is working on exposing the public key within the smart
//! contract code and this feature is planned to be included in the next
//! protocol update in 6-12 months. After that protocol update, the
//! `public_key_registry` will not be necessary anymore.
//!
//! As follows from the CIS2 specification, the contract has a `transfer`
//! function for transferring an amount of a specific token type from one
//! address to another address. An address can enable and disable one or more
//! addresses as operators with the `updateOperator` function. An operator of
//! some address is allowed to transfer any tokens owned by this address.
//! As follows from the CIS3 specification, the contract has a `permit`
//! function. It is the sponsored counterparts to the `transfer/updateOperator`
//! function and can be executed by anyone on behalf of an account given a
//! signed transaction by the private key corresponding to the public key that
//! is registered for that account.
#![cfg_attr(not(feature = "std"), no_std)]

use concordium_cis2::*;
use concordium_std::{collections::BTreeMap, *};

/// The baseurl for the token metadata, gets appended with the token ID as hex
/// encoding before emitted in the TokenMetadata event.
const TOKEN_METADATA_BASE_URL: &str = "https://some.example/token/";

/// The standard identifier for the CIS-3: Concordium Token Standard 3.
pub const CIS3_STANDARD_IDENTIFIER: StandardIdentifier<'static> =
    StandardIdentifier::new_unchecked("CIS-3");

/// List of supported standards by this contract address.
const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 3] =
    [CIS0_STANDARD_IDENTIFIER, CIS2_STANDARD_IDENTIFIER, CIS3_STANDARD_IDENTIFIER];

/// Tag for the CIS3 Registration event.
pub const REGISTRATION_EVENT_TAG: u8 = 0u8;

/// Tagged events to be serialized for the event log.
#[derive(Debug, Serial)]
enum Event {
    /// Registration of a public key for a given account. The
    /// corresponding private key will have to sign the transactions that
    /// can be executed via the `permit` function.
    Registration(RegistrationEvent),
}

/// The RegistrationEvent is logged when a new public key is registered.
#[derive(Debug, Serialize, SchemaType)]
pub struct RegistrationEvent {
    /// Account that a public key will be registered to.
    account:    AccountAddress,
    /// The public key that should be linked to the above account.
    public_key: PublicKeyEd25519,
}

// Implementing a custom schemaType to the `Event` combining all CIS2/CIS3
// events.
impl schema::SchemaType for Event {
    fn get_type() -> schema::Type {
        let mut event_map = BTreeMap::new();
        event_map.insert(
            REGISTRATION_EVENT_TAG,
            (
                "Registration".to_string(),
                schema::Fields::Named(vec![
                    (String::from("account"), AccountAddress::get_type()),
                    (String::from("public_key"), PublicKeyEd25519::get_type()),
                ]),
            ),
        );
        event_map.insert(
            TRANSFER_EVENT_TAG,
            (
                "Transfer".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), ContractTokenId::get_type()),
                    (String::from("amount"), ContractTokenAmount::get_type()),
                    (String::from("from"), Address::get_type()),
                    (String::from("to"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            MINT_EVENT_TAG,
            (
                "Mint".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), ContractTokenId::get_type()),
                    (String::from("amount"), ContractTokenAmount::get_type()),
                    (String::from("owner"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            BURN_EVENT_TAG,
            (
                "Burn".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), ContractTokenId::get_type()),
                    (String::from("amount"), ContractTokenAmount::get_type()),
                    (String::from("owner"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            UPDATE_OPERATOR_EVENT_TAG,
            (
                "UpdateOperator".to_string(),
                schema::Fields::Named(vec![
                    (String::from("update"), OperatorUpdate::get_type()),
                    (String::from("owner"), Address::get_type()),
                    (String::from("operator"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            TOKEN_METADATA_EVENT_TAG,
            (
                "TokenMetadata".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), ContractTokenId::get_type()),
                    (String::from("metadata_url"), MetadataUrl::get_type()),
                ]),
            ),
        );
        schema::Type::TaggedEnum(event_map)
    }
}

// Type aliases

/// Contract token ID type.
/// To save bytes we use a token ID type limited to a `u32`.
type ContractTokenId = TokenIdU32;

/// Contract token amount.
/// Since the tokens are non-fungible the total supply of any token will be at
/// most 1 and it is fine to use a small type for representing token amounts.
type ContractTokenAmount = TokenAmountU8;

/// The parameter for the contract function `mint` which mints a number of
/// tokens to a given address.
#[derive(Serial, Deserial, SchemaType)]
struct MintParams {
    /// Owner of the newly minted tokens.
    owner:  Address,
    /// A collection of tokens to mint.
    #[concordium(size_length = 1)]
    tokens: collections::BTreeSet<ContractTokenId>,
}

/// The state for each address.
#[derive(Serial, DeserialWithState, Deletable, StateClone)]
#[concordium(state_parameter = "S")]
struct AddressState<S> {
    /// The tokens owned by this address.
    owned_tokens: StateSet<ContractTokenId, S>,
    /// The address which are currently enabled as operators for this address.
    operators:    StateSet<Address, S>,
}

impl<S: HasStateApi> AddressState<S> {
    fn empty(state_builder: &mut StateBuilder<S>) -> Self {
        AddressState {
            owned_tokens: state_builder.new_set(),
            operators:    state_builder.new_set(),
        }
    }
}

/// The contract state.
// Note: The specification does not specify how to structure the contract state
// and this could be structured in a more space efficient way depending on the use case.
#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S> {
    /// The state for each address.
    state:               StateMap<Address, AddressState<S>, S>,
    /// All of the token IDs
    all_tokens:          StateSet<ContractTokenId, S>,
    /// Map with contract addresses providing implementations of additional
    /// standards.
    implementors:        StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
    /// A registry to link an account to an public key and its nonce. The
    /// corresponding private key registered here has full access to the
    /// tokens controlled by the account. The nonce is used to prevent replay
    /// attacks of signed transactions.
    public_key_registry: StateMap<AccountAddress, (PublicKeyEd25519, u64), S>,
}

/// Part of the parameter type for the contract function `registerPublicKey`.
/// Takes the account and the public key that should be linked.
#[derive(Debug, Serialize, SchemaType)]
pub struct RegisterPublicKeyParam {
    /// Account that a public key will be registered to.
    account:    AccountAddress,
    /// The public key that should be linked to the above account.
    public_key: PublicKeyEd25519,
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

/// Part of the parameter type for the contract function `permit`.
/// Specifies the transaction payload that should be forwarded to either the
/// `transfer` or the `updateOperator` function.
#[derive(Debug, Serialize, SchemaType, Clone)]
enum PermitPayload {
    Transfer(TransferParameter),
    UpdateOperator(UpdateOperatorParams),
}

/// Part of the parameter type for the contract function `permit`.
/// Specifies the message that is signed.
#[derive(SchemaType, Serialize)]
struct PermitMessage {
    /// The contract_address that the signature is intended for.
    contract_address: ContractAddress,
    /// The entry_point that the signature is intended for.
    entry_point:      OwnedEntrypointName,
    /// A nonce to prevent replay attacks.
    nonce:            u64,
    /// A timestamp to make signatures expire.
    timestamp:        Timestamp,
    /// The payload that should be forwarded to either the `transfer` or the
    /// `updateOperator` function.
    payload:          PermitPayload,
}

/// The parameter type for the contract function `permit`.
/// Takes a signature, the signer, and the message that was signed.
#[derive(Serialize, SchemaType)]
pub struct PermitParam {
    /// Signature/s. The CIS3 standard supports multi-sig accounts but because
    /// the `public_key_registry` in this contract maps one public key to one
    /// account, only one signature has to be provided for this contract. This
    /// signature has to be at the key 0 in both maps below.
    #[concordium(size_length = 1)]
    signature: BTreeMap<u8, BTreeMap<u8, SignatureEd25519>>,
    /// Account that created the above signature.
    signer:    AccountAddress,
    /// Message that was signed.
    message:   PermitMessage,
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
    /// Failing to mint new tokens because one of the token IDs already exists
    /// in this contract.
    TokenIdAlreadyExists,
    /// Failed to invoke a contract.
    InvokeContractError,
    /// Failing to update the public key of an account that already has a public
    /// key registered.
    AccountAlreadyRegistered,
    /// Failing to get the public key. No public key was registered for the
    /// given account.
    NoPublicKey,
    /// Failed signature verification: Invalid signature.
    WrongSignature,
    /// Failed signature verification: A different nonce is expected.
    NonceMismatch,
    /// Failed signature verification: Signature was intended for a different
    /// contract.
    WrongContract,
    /// Failed signature verification: Signature was intended for a different
    /// entry_point.
    WrongEntryPoint,
    /// Failed signature verification: Signature is expired.
    Expired,
    /// Failed signature verification: Signature map is misconfigured.
    SignatureMapMisconfigured,
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
            state:               state_builder.new_map(),
            all_tokens:          state_builder.new_set(),
            implementors:        state_builder.new_map(),
            public_key_registry: state_builder.new_map(),
        }
    }

    /// Mint a new token with a given address as the owner
    fn mint(
        &mut self,
        token: ContractTokenId,
        owner: &Address,
        state_builder: &mut StateBuilder<S>,
    ) -> ContractResult<()> {
        ensure!(self.all_tokens.insert(token), CustomContractError::TokenIdAlreadyExists.into());

        let mut owner_state =
            self.state.entry(*owner).or_insert_with(|| AddressState::empty(state_builder));
        owner_state.owned_tokens.insert(token);
        Ok(())
    }

    /// Check that the token ID currently exists in this contract.
    #[inline(always)]
    fn contains_token(&self, token_id: &ContractTokenId) -> bool {
        self.all_tokens.contains(token_id)
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
        let balance = self
            .state
            .get(address)
            .map(|address_state| u8::from(address_state.owned_tokens.contains(token_id)))
            .unwrap_or(0);
        Ok(balance.into())
    }

    /// Check if a given address is an operator of a given owner address.
    fn is_operator(&self, address: &Address, owner: &Address) -> bool {
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

        {
            let mut from_address_state =
                self.state.get_mut(from).ok_or(ContractError::InsufficientFunds)?;
            // Find and remove the token from the owner, if nothing is removed, we know the
            // address did not own the token..
            let from_had_the_token = from_address_state.owned_tokens.remove(token_id);
            ensure!(from_had_the_token, ContractError::InsufficientFunds);
        }

        // Add the token to the new owner.
        let mut to_address_state =
            self.state.entry(*to).or_insert_with(|| AddressState::empty(state_builder));
        to_address_state.owned_tokens.insert(*token_id);
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
    /// Succeeds even if the `operator` is _not_ an operator for the `address`.
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

/// Initialize contract instance with no token types initially.
#[init(contract = "cis3_nft", event = "Event")]
fn contract_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    // Construct the initial contract state.
    Ok(State::empty(state_builder))
}

/// Part of the return paramter of the `view` function.
#[derive(Serialize, SchemaType, Debug, PartialEq)]
struct ViewAddressState {
    owned_tokens: Vec<ContractTokenId>,
    operators:    Vec<Address>,
}

/// Return paramter of the `view` function.
#[derive(Serialize, SchemaType, Debug)]
struct ViewState {
    state: Vec<(Address, ViewAddressState)>,
    all_tokens: Vec<ContractTokenId>,
    all_public_keys_and_nonces: Vec<(AccountAddress, (PublicKeyEd25519, u64))>,
}

/// View function that returns the entire contents of the state. Meant for
/// testing.
#[receive(contract = "cis3_nft", name = "view", return_value = "ViewState")]
fn contract_view<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ReceiveResult<ViewState> {
    let state = host.state();

    let mut inner_state = Vec::new();
    for (k, a_state) in state.state.iter() {
        let owned_tokens = a_state.owned_tokens.iter().map(|x| *x).collect();
        let operators = a_state.operators.iter().map(|x| *x).collect();
        inner_state.push((*k, ViewAddressState {
            owned_tokens,
            operators,
        }));
    }

    let all_tokens = state.all_tokens.iter().map(|x| *x).collect();

    let mut all_public_keys_and_nonces = Vec::new();
    for (account_address, public_key) in state.public_key_registry.iter() {
        all_public_keys_and_nonces.push((*account_address, *public_key));
    }

    Ok(ViewState {
        state: inner_state,
        all_tokens,
        all_public_keys_and_nonces,
    })
}

/// The parameter type for the contract function `registerPublicKey`.
#[derive(Debug, Serialize, SchemaType)]
pub struct RegisterPublicKeyParams(#[concordium(size_length = 2)] pub Vec<RegisterPublicKeyParam>);

/// Register a public key for a given account. The corresponding private
/// key can sign messages that can be submitted to the `permit` function. Can
/// only be called by the contract owner (third-party provider offering
/// sponsored transaction services) or the account itself. Once registered, the
/// public key cannot be updated. Logs a `Registration` event for each account.
/// Use this function with care, the corresponding private key registered here
/// has full access to the tokens controlled by the account.
///
/// It rejects if:
/// - The sender is not the contract instance owner or the account itself.
/// - Fails to parse parameter.
/// - A public key is already registered to the account.
/// - Fails to log the `Registration` event.
#[receive(
    contract = "cis3_nft",
    name = "registerPublicKeys",
    error = "ContractError",
    parameter = "RegisterPublicKeyParams",
    enable_logger,
    mutable
)]
fn contract_register_public_keys<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Get the contract owner
    let owner = ctx.owner();
    // Get the sender of the transaction
    let sender = ctx.sender();

    // Parse the parameter.
    let RegisterPublicKeyParams(params) = ctx.parameter_cursor().get()?;

    for param in params {
        // Only the contract instance owner or the account itself can add a public key.
        ensure!(
            sender.matches_account(&owner) || sender.matches_account(&param.account),
            ContractError::Unauthorized
        );

        // Register the public key.
        let old_public_key =
            host.state_mut().public_key_registry.insert(param.account, (param.public_key, 0));

        // Return an error if the owner tries to update/re-write a new public key for an
        // already registered account.
        ensure!(old_public_key.is_none(), CustomContractError::AccountAlreadyRegistered.into());

        // Log the registration event.
        logger.log(&Event::Registration(RegistrationEvent {
            account:    param.account,
            public_key: param.public_key,
        }))?;
    }

    Ok(())
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
    contract = "cis3_nft",
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

    for &token_id in params.tokens.iter() {
        // Mint the token in the state.
        state.mint(token_id, &params.owner, builder)?;

        // Event for minted NFT.
        logger.log(&Cis2Event::Mint(MintEvent {
            token_id,
            amount: ContractTokenAmount::from(1),
            owner: params.owner,
        }))?;

        // Metadata URL for the NFT.
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

/// Internal `transfer/permit` helper function. Invokes the `transfer`
/// function of the state. Logs a `Transfer` event and invokes a receive hook
/// function. The function assumes that the transfer is authorized.
fn transfer<S: HasStateApi>(
    transfer: concordium_cis2::Transfer<ContractTokenId, ContractTokenAmount>,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    let (state, builder) = host.state_and_builder();

    let to_address = transfer.to.address();
    // Update the contract state
    state.transfer(&transfer.token_id, transfer.amount, &transfer.from, &to_address, builder)?;

    // Log transfer event
    logger.log(&Cis2Event::Transfer(TransferEvent {
        token_id: transfer.token_id,
        amount:   transfer.amount,
        from:     transfer.from,
        to:       to_address,
    }))?;

    // If the receiver is a contract: invoke the receive hook function.
    if let Receiver::Contract(address, function) = transfer.to {
        let parameter = OnReceivingCis2Params {
            token_id: transfer.token_id,
            amount:   transfer.amount,
            from:     transfer.from,
            data:     transfer.data,
        };
        host.invoke_contract(&address, &parameter, function.as_entrypoint_name(), Amount::zero())?;
    }

    Ok(())
}

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
    contract = "cis3_nft",
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

    for transer in transfers {
        // Authenticate the sender for this transfer
        ensure!(
            transer.from == sender || host.state().is_operator(&sender, &transer.from),
            ContractError::Unauthorized
        );

        transfer(transer, host, logger)?;
    }
    Ok(())
}

/// Helper function that can be invoked to serializ the `PermitMessage`.
#[receive(
    contract = "cis3_nft",
    name = "serializationHelper",
    parameter = "PermitMessage",
    mutable
)]
fn contract_serialization_helper<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    _host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    Ok(())
}

/// Verify an ed25519 signature and allow the transfer of tokens or update of an
/// operator.
///
/// In case of a `transfer` action:
/// Logs a `Transfer` event and invokes a receive hook function for the
/// transfer.
///
/// In case of a `updateOperator` action:
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - A different nonce is expected.
/// - The signature was intended for a different contract.
/// - The signature was intended for a different `entry_point`.
/// - The signature is expired.
/// - No public key was registered for the given account.
/// - The signature can not be validated.
/// - Fails to log event.
/// - In case of a `transfer` action: it fails to be executed, which could be
///   if:
///     - The `token_id` does not exist.
///     - The token is not owned by the `from` address.
///     - The receive hook function calls rejects.

#[receive(
    contract = "cis3_nft",
    name = "permit",
    parameter = "PermitParam",
    crypto_primitives,
    mutable,
    enable_logger
)]
fn contract_permit<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<()> {
    // Parse the parameter.
    let param: PermitParam = ctx.parameter_cursor().get()?;

    ensure!(
        param.signature.len() == 1
            && param.signature.get(&0).ok_or(CustomContractError::SignatureMapMisconfigured)?.len()
                == 1,
        CustomContractError::SignatureMapMisconfigured.into()
    );

    let signature = *param
        .signature
        .get(&0)
        .ok_or(CustomContractError::SignatureMapMisconfigured)?
        .get(&0)
        .ok_or(CustomContractError::SignatureMapMisconfigured)?;

    // Update the nonce.
    let mut entry = host
        .state_mut()
        .public_key_registry
        .entry(param.signer)
        .occupied_or(CustomContractError::NoPublicKey)?;
    // Bump nonce.
    entry.1 += 1;
    // Get the public key and the current nonce.
    let public_key = entry.0;
    let nonce = entry.1;
    drop(entry);

    // Check the nonce to prevent replay attacks.
    ensure_eq!(param.message.nonce, nonce, CustomContractError::NonceMismatch.into());

    // Check that the signature was intended for this contract.
    ensure_eq!(
        param.message.contract_address,
        ctx.self_address(),
        CustomContractError::WrongContract.into()
    );

    // Check signature is not expired.
    ensure!(
        param.message.timestamp > ctx.metadata().slot_time(),
        CustomContractError::Expired.into()
    );

    let zeros: Vec<u8> = Vec::from([0, 0, 0, 0, 0, 0, 0, 0]);

    // Calculate the message hash.
    let message_hash = crypto_primitives
        .hash_sha2_256(
            &[
                to_bytes(&param.signer),
                zeros,
                hex::encode(to_bytes(&param.message)).as_bytes().to_vec(),
            ]
            .concat(),
        )
        .0;

    // Check signature.
    ensure!(
        crypto_primitives.verify_ed25519_signature(public_key, signature, &message_hash),
        CustomContractError::WrongSignature.into()
    );

    match param.message.payload {
        // Transfer the tokens.
        PermitPayload::Transfer(transfer_parameter) => {
            // Check that the signature was intended for this `entry_point`.
            ensure_eq!(
                param.message.entry_point,
                OwnedEntrypointName::new_unchecked("contract_transfer".into()),
                CustomContractError::WrongEntryPoint.into()
            );

            let TransferParams(transfers): TransferParameter = transfer_parameter;

            for transfer_struct in transfers {
                ensure!(
                    transfer_struct.from.matches_account(&param.signer),
                    ContractError::Unauthorized
                );

                transfer(transfer_struct, host, logger)?
            }
        }
        // Update the operator.
        PermitPayload::UpdateOperator(update_parameter) => {
            // Check that the signature was intended for this `entry_point`.
            ensure_eq!(
                param.message.entry_point,
                OwnedEntrypointName::new_unchecked("contract_update_operator".into()),
                CustomContractError::WrongEntryPoint.into()
            );

            let UpdateOperatorParams(updates): UpdateOperatorParams = update_parameter;

            let (state, builder) = host.state_and_builder();

            for update in updates {
                update_operator(
                    update.update,
                    concordium_std::Address::Account(param.signer),
                    update.operator,
                    state,
                    builder,
                    logger,
                )?;
            }
        }
    }

    Ok(())
}

/// Internal `updateOperator/permit` helper function. Invokes the
/// `add_operator/remove_operator` function of the state.
/// Logs a `UpdateOperator` event. The function assumes that the sender is
/// authorized to do the `updateOperator` action.
fn update_operator<S: HasStateApi>(
    update: OperatorUpdate,
    sender: Address,
    operator: Address,
    state: &mut State<S>,
    builder: &mut StateBuilder<S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Update the operator in the state.
    match update {
        OperatorUpdate::Add => state.add_operator(&sender, &operator, builder),
        OperatorUpdate::Remove => state.remove_operator(&sender, &operator),
    }

    // Log the appropriate event
    logger.log(&Cis2Event::<ContractTokenId, ContractTokenAmount>::UpdateOperator(
        UpdateOperatorEvent {
            owner: sender,
            operator,
            update,
        },
    ))?;

    Ok(())
}

/// Enable or disable addresses as operators of the sender address.
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Fails to log event.
#[receive(
    contract = "cis3_nft",
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
        update_operator(param.update, sender, param.operator, state, builder, logger)?;
    }
    Ok(())
}

/// Takes a list of queries. Each query is an owner address and some address to
/// check as an operator of the owner address.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis3_nft",
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
    contract = "cis3_nft",
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

/// Response type for the function `publicKeyOf`.
#[derive(Debug, Serialize, SchemaType)]
pub struct ContractPublicKeyQueryResponse(
    #[concordium(size_length = 2)] pub Vec<Option<(PublicKeyEd25519, u64)>>,
);

impl From<Vec<Option<(PublicKeyEd25519, u64)>>> for ContractPublicKeyQueryResponse {
    fn from(results: concordium_std::Vec<Option<(concordium_std::PublicKeyEd25519, u64)>>) -> Self {
        ContractPublicKeyQueryResponse(results)
    }
}

/// The parameter type for the contract function `publicKeyOf`. A query for the
/// public key and nonce of a given account.
type ContractPublicKeyQueryParams = PublicKeyOfQueryParams;

/// The parameter type for the contract function `publicKeyOf`. A query for the
/// public key and nonce of a given account.
#[derive(Debug, Serialize, SchemaType)]
pub struct PublicKeyOfQueryParams {
    /// List of public key queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<PublicKeyQuery>,
}

/// Part of the parameter type for the contract function `publicKeyOf`.
#[derive(Debug, Serialize, SchemaType)]
pub struct PublicKeyQuery {
    /// The account for which the public key and nonce should be queried.
    pub account: AccountAddress,
}

/// Get the public keys and noces of accounts.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis3_nft",
    name = "publicKeyOf",
    parameter = "ContractPublicKeyQueryParams",
    return_value = "ContractPublicKeyQueryResponse",
    error = "ContractError"
)]
fn contract_public_key_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<ContractPublicKeyQueryResponse> {
    // Parse the parameter.
    let params: ContractPublicKeyQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response: Vec<Option<(PublicKeyEd25519, u64)>> =
        Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for the public_key and nonce.
        let entry = host
            .state()
            .public_key_registry
            .get(&query.account)
            .map(|registry_entry| (registry_entry.0, registry_entry.1));

        response.push(entry);
    }
    let result = ContractPublicKeyQueryResponse::from(response);
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
    contract = "cis3_nft",
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
    contract = "cis3_nft",
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
    contract = "cis3_nft",
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
    const ACCOUNT_2: AccountAddress = AccountAddress([2u8; 32]);
    const ADDRESS_2: Address = Address::Account(ACCOUNT_2);
    const TOKEN_0: ContractTokenId = TokenIdU32(0);
    const TOKEN_1: ContractTokenId = TokenIdU32(42);
    const TOKEN_2: ContractTokenId = TokenIdU32(43);
    const TOKEN_3: ContractTokenId = TokenIdU32(44);

    const PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([
        152, 217, 249, 210, 0, 59, 49, 241, 216, 183, 234, 114, 190, 177, 54, 200, 163, 77, 20,
        235, 2, 178, 107, 11, 31, 37, 153, 68, 179, 56, 214, 14,
    ]);
    const OTHER_PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([
        55, 162, 168, 229, 46, 250, 217, 117, 219, 246, 88, 14, 119, 52, 228, 242, 73, 234, 165,
        234, 138, 118, 62, 147, 74, 134, 113, 205, 126, 68, 100, 153,
    ]);

    const SIGNATURE_TRANSFER: SignatureEd25519 = SignatureEd25519([
        41, 30, 172, 147, 94, 2, 134, 188, 182, 138, 207, 11, 169, 95, 87, 131, 77, 182, 122, 106,
        202, 179, 50, 213, 176, 68, 235, 175, 10, 158, 195, 107, 251, 90, 104, 98, 26, 127, 194,
        79, 241, 120, 176, 17, 241, 154, 15, 94, 36, 39, 26, 123, 72, 52, 192, 129, 246, 211, 36,
        72, 57, 15, 212, 12,
    ]);
    const SIGNATURE_UPDATE_OPERATOR: SignatureEd25519 = SignatureEd25519([
        116, 227, 129, 72, 55, 43, 24, 163, 39, 208, 34, 87, 141, 46, 215, 176, 59, 176, 240, 136,
        83, 202, 122, 127, 193, 94, 148, 82, 164, 233, 78, 231, 217, 207, 244, 47, 218, 118, 43,
        234, 56, 231, 197, 114, 6, 144, 163, 118, 104, 62, 218, 111, 238, 48, 175, 100, 82, 86, 19,
        237, 54, 144, 175, 2,
    ]);

    /// Test helper function which creates a contract state with two tokens with
    /// id `TOKEN_0` owned by `ADDRESS_0` and id `TOKEN_1` owned by `ADDRESS_1`.
    fn initial_state<S: HasStateApi>(state_builder: &mut StateBuilder<S>) -> State<S> {
        let mut state = State::empty(state_builder);
        state.mint(TOKEN_0, &ADDRESS_0, state_builder).expect_report("Failed to mint TOKEN_0");
        state.mint(TOKEN_1, &ADDRESS_1, state_builder).expect_report("Failed to mint TOKEN_1");
        state
    }

    /// Test initialization succeeds.
    #[concordium_test]
    fn test_init() {
        // Setup the context
        let ctx = TestInitContext::empty();
        let mut builder = TestStateBuilder::new();

        // Call the contract function.
        let result = contract_init(&ctx, &mut builder);

        // Check the result
        let state = result.expect_report("Contract initialization failed");

        // Check the state
        // Note. This is rather expensive as an iterator is created and then traversed -
        // should be avoided when writing smart contracts.
        claim_eq!(state.all_tokens.iter().count(), 0, "No token should be initialized");
    }

    /// Test minting, ensuring the new tokens are owned by the given address and
    /// the appropriate events are logged.
    #[concordium_test]
    fn test_mint() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_owner(ACCOUNT_0);

        // and parameter.
        let mut tokens = collections::BTreeSet::new();
        tokens.insert(TOKEN_0);
        tokens.insert(TOKEN_1);
        tokens.insert(TOKEN_2);
        let parameter = MintParams {
            tokens,
            owner: ADDRESS_0,
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
        // Note. This is rather expensive as an iterator is created and then traversed -
        // should be avoided when writing smart contracts.
        claim_eq!(host.state().all_tokens.iter().count(), 3, "Expected three tokens in the state.");

        let balance0 =
            host.state().balance(&TOKEN_0, &ADDRESS_0).expect_report("Token is expected to exist");
        claim_eq!(balance0, 1.into(), "Tokens should be owned by the given address 0");

        let balance1 =
            host.state().balance(&TOKEN_1, &ADDRESS_0).expect_report("Token is expected to exist");
        claim_eq!(balance1, 1.into(), "Tokens should be owned by the given address 0");

        let balance2 =
            host.state().balance(&TOKEN_2, &ADDRESS_0).expect_report("Token is expected to exist");
        claim_eq!(balance2, 1.into(), "Tokens should be owned by the given address 0");

        // Check the logs
        claim!(
            logger.logs.contains(&to_bytes(&Cis2Event::Mint(MintEvent {
                owner:    ADDRESS_0,
                token_id: TOKEN_0,
                amount:   ContractTokenAmount::from(1),
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
                        url:  format!("{}00000000", TOKEN_METADATA_BASE_URL),
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
                        url:  format!("{}2A000000", TOKEN_METADATA_BASE_URL),
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
            amount:   ContractTokenAmount::from(1),
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
        let balance2 =
            host.state().balance(&TOKEN_1, &ADDRESS_1).expect_report("Token is expected to exist");
        claim_eq!(
            balance0,
            0.into(),
            "Token owner balance should be decreased by the transferred amount"
        );
        claim_eq!(
            balance1,
            1.into(),
            "Token receiver balance should be increased by the transferred amount"
        );
        claim_eq!(
            balance2,
            1.into(),
            "Token receiver balance for token 1 should be the same as before"
        );

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "Only one event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Cis2Event::Transfer(TransferEvent {
                from:     ADDRESS_0,
                to:       ADDRESS_1,
                token_id: TOKEN_0,
                amount:   ContractTokenAmount::from(1),
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
            amount:   ContractTokenAmount::from(1),
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
            amount:   ContractTokenAmount::from(1),
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
        let balance1 = host
            .state_mut()
            .balance(&TOKEN_0, &ADDRESS_1)
            .expect_report("Token is expected to exist");
        claim_eq!(
            balance0,
            0.into(),
            "Token owner balance should be decreased by the transferred amount"
        );
        claim_eq!(
            balance1,
            1.into(),
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
                amount:   ContractTokenAmount::from(1),
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
            update:   OperatorUpdate::Add,
            operator: ADDRESS_1,
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

    /// Test `view` function.
    #[concordium_test]
    fn test_view() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_owner(ACCOUNT_0);

        let mut state_builder = TestStateBuilder::new();

        // Create the state values
        let mut public_key_registry = state_builder.new_map();
        public_key_registry.insert(ACCOUNT_1, (PUBLIC_KEY, 0));
        public_key_registry.insert(ACCOUNT_2, (OTHER_PUBLIC_KEY, 1));

        let mut all_tokens = state_builder.new_set();
        all_tokens.insert(TOKEN_0);
        all_tokens.insert(TOKEN_1);

        let mut state = state_builder.new_map();
        let mut operators = state_builder.new_set();
        operators.insert(ADDRESS_2);
        let mut owned_tokens = state_builder.new_set();
        owned_tokens.insert(TOKEN_0);
        owned_tokens.insert(TOKEN_1);
        state.insert(ADDRESS_1, AddressState {
            owned_tokens,
            operators,
        });

        let state = State {
            state,
            all_tokens,
            implementors: state_builder.new_map(),
            public_key_registry,
        };

        let host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result = contract_view(&ctx, &host);

        let returned_view_state = result.expect_report("Failed getting contract_view result value");

        claim_eq!(
            returned_view_state.all_public_keys_and_nonces,
            [(ACCOUNT_1, (PUBLIC_KEY, 0)), (ACCOUNT_2, (OTHER_PUBLIC_KEY, 1))],
            "Correct public keys should be returned by the view function"
        );

        claim_eq!(
            returned_view_state.all_tokens,
            vec![TOKEN_0, TOKEN_1],
            "Correct tokens should be returned by the view function"
        );

        claim_eq!(
            returned_view_state.state[0].0,
            ADDRESS_1,
            "Correct address in state should be returned by the view function"
        );

        claim_eq!(
            returned_view_state.state[0].1,
            ViewAddressState {
                owned_tokens: vec![TOKEN_0, TOKEN_1],
                operators:    vec![concordium_std::Address::Account(ACCOUNT_2)],
            },
            "Correct ViewAddressState should be returned by the view function"
        );
    }

    /// Test register a public key.
    #[concordium_test]
    fn test_register_public_key() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_owner(ACCOUNT_0);

        // and parameter.
        let register_public_key_param_0 = RegisterPublicKeyParam {
            account:    ACCOUNT_1,
            public_key: PUBLIC_KEY,
        };

        let register_public_key_param_1 = RegisterPublicKeyParam {
            account:    ACCOUNT_2,
            public_key: OTHER_PUBLIC_KEY,
        };

        let parameter =
            RegisterPublicKeyParams(vec![register_public_key_param_0, register_public_key_param_1]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> =
            contract_register_public_keys(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        let public_key =
            host.state().public_key_registry.get(&ACCOUNT_1).expect_report("Expect a public key").0;

        claim_eq!(public_key, PUBLIC_KEY, "Account_1 should have a public key registered");

        // Check the state.
        let public_key =
            host.state().public_key_registry.get(&ACCOUNT_2).expect_report("Expect a public key").0;

        claim_eq!(public_key, OTHER_PUBLIC_KEY, "Account_2 should have a public key registered");

        // Checking that `ACCOUNT_1/ACCOUNT_2` has the correct public key registered and
        // there is no public key registered for `ACCOUNT_0`.
        let public_key_of_query_vector = PublicKeyOfQueryParams {
            queries: vec![
                PublicKeyQuery {
                    account: ACCOUNT_0,
                },
                PublicKeyQuery {
                    account: ACCOUNT_1,
                },
                PublicKeyQuery {
                    account: ACCOUNT_2,
                },
            ],
        };
        let parameter_bytes = to_bytes(&public_key_of_query_vector);

        ctx.set_parameter(&parameter_bytes);

        // Checking the return value of the `contract_public_key_of` function
        let result: ContractResult<ContractPublicKeyQueryResponse> =
            contract_public_key_of(&ctx, &host);

        claim_eq!(
            result.as_ref().expect_report("Expect a public key").0[0],
            None,
            "ACCOUNT_0 should have no public key registered"
        );

        claim_eq!(
            result.as_ref().expect_report("Expect a public key").0[1],
            Some((PUBLIC_KEY, 0)),
            "ACCOUNT_1 should have a public key registered"
        );

        claim_eq!(
            result.as_ref().expect_report("Expect a public key").0[2],
            Some((OTHER_PUBLIC_KEY, 0)),
            "ACCOUNT_2 should have a public key registered"
        );

        // Check the logs.
        claim_eq!(logger.logs.len(), 2, "Two events should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Event::Registration(RegistrationEvent {
                account:    ACCOUNT_1,
                public_key: PUBLIC_KEY,
            })),
            "Incorrect event emitted"
        );
        claim_eq!(
            logger.logs[1],
            to_bytes(&Event::Registration(RegistrationEvent {
                account:    ACCOUNT_2,
                public_key: OTHER_PUBLIC_KEY,
            })),
            "Incorrect event emitted"
        )
    }

    /// Test can NOT update the public key.
    #[concordium_test]
    fn test_can_not_update_public_key() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_owner(ACCOUNT_0);

        // and parameter.
        let register_public_key_param = RegisterPublicKeyParam {
            account:    ACCOUNT_1,
            public_key: PUBLIC_KEY,
        };

        let parameter = RegisterPublicKeyParams(vec![register_public_key_param]);
        let parameter_bytes = to_bytes(&parameter);

        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> =
            contract_register_public_keys(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // and parameter.
        let register_public_key_param = RegisterPublicKeyParam {
            account:    ACCOUNT_1,
            public_key: OTHER_PUBLIC_KEY,
        };

        let parameter = RegisterPublicKeyParams(vec![register_public_key_param]);
        let parameter_bytes = to_bytes(&parameter);

        ctx.set_parameter(&parameter_bytes);

        // Call the contract function.
        let result: ContractResult<()> =
            contract_register_public_keys(&ctx, &mut host, &mut logger);

        // Check the result.
        let err = result.expect_err_report("Expected to fail");
        claim_eq!(
            err,
            concordium_cis2::Cis2Error::Custom(CustomContractError::AccountAlreadyRegistered),
            "Error is expected to be AccountAlreadyRegistered"
        )
    }

    /// Test other can not register a public key.
    #[concordium_test]
    fn test_other_can_not_register_public_key() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_2);
        ctx.set_owner(ACCOUNT_0);

        // and parameter.
        let register_public_key_param = RegisterPublicKeyParam {
            account:    ACCOUNT_1,
            public_key: PUBLIC_KEY,
        };

        let parameter = RegisterPublicKeyParams(vec![register_public_key_param]);
        let parameter_bytes = to_bytes(&parameter);

        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> =
            contract_register_public_keys(&ctx, &mut host, &mut logger);

        // Check the result.
        let err = result.expect_err_report("Expected to fail");
        claim_eq!(err, ContractError::Unauthorized, "Error is expected to be Unauthorized")
    }

    /// Test permit transfer.
    #[concordium_test]
    fn test_permit_transfer() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_owner(ACCOUNT_0);
        ctx.set_self_address(ContractAddress {
            index:    0,
            subindex: 0,
        });
        ctx.set_named_entrypoint(OwnedEntrypointName::new_unchecked(
            "contract_permit_transfer".into(),
        ));
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(0));

        // and parameter.
        let register_public_key_param = RegisterPublicKeyParam {
            account:    ACCOUNT_1,
            public_key: PUBLIC_KEY,
        };

        let parameter = RegisterPublicKeyParams(vec![register_public_key_param]);
        let parameter_bytes = to_bytes(&parameter);

        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Register public key.
        let result: ContractResult<()> =
            contract_register_public_keys(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Mint token to ACCOUNT_1
        let mut tokens = collections::BTreeSet::new();
        tokens.insert(TOKEN_3);
        let parameter = MintParams {
            tokens,
            owner: concordium_std::Address::Account(ACCOUNT_1),
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        // Call the contract function.
        let result: ContractResult<()> = contract_mint(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Create input parematers for the `permit` transfer function.
        let transfer = Transfer {
            from:     ADDRESS_1,
            to:       Receiver::from_account(ACCOUNT_0),
            token_id: TOKEN_1,
            amount:   ContractTokenAmount::from(1),
            data:     AdditionalData::empty(),
        };
        let payload = TransferParams::from(vec![transfer]);

        let mut inner_signature_map = BTreeMap::new();
        inner_signature_map.insert(0, SIGNATURE_TRANSFER);

        let mut signature_map = BTreeMap::new();
        signature_map.insert(0, inner_signature_map);

        let permit_transfer_param = PermitParam {
            signature: signature_map,
            signer:    ACCOUNT_1,
            message:   PermitMessage {
                timestamp:        Timestamp::from_timestamp_millis(10000000000),
                contract_address: ContractAddress {
                    index:    0,
                    subindex: 0,
                },
                entry_point:      OwnedEntrypointName::new_unchecked("contract_transfer".into()),
                nonce:            1,
                payload:          PermitPayload::Transfer(payload),
            },
        };

        let parameter_bytes = to_bytes(&permit_transfer_param);
        ctx.set_parameter(&parameter_bytes);

        let crypto_primitives = TestCryptoPrimitives::new();

        // Check the state.
        let balance0 =
            host.state().balance(&TOKEN_1, &ADDRESS_0).expect_report("Token is expected to exist");
        let balance1 = host
            .state_mut()
            .balance(&TOKEN_1, &ADDRESS_1)
            .expect_report("Token is expected to exist");

        claim_eq!(balance0, 0.into(), "Token balance of address0 should be 0");
        claim_eq!(balance1, 1.into(), "Token balance of address1 should be 1");

        // Inovke `permit` function.
        let result: ContractResult<()> =
            contract_permit(&ctx, &mut host, &mut logger, &crypto_primitives);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        let balance0 =
            host.state().balance(&TOKEN_1, &ADDRESS_0).expect_report("Token is expected to exist");
        let balance1 = host
            .state_mut()
            .balance(&TOKEN_1, &ADDRESS_1)
            .expect_report("Token is expected to exist");

        claim_eq!(
            balance0,
            1.into(),
            "Token receiver balance should be decreased by the transferred amount"
        );
        claim_eq!(
            balance1,
            0.into(),
            "Token owner balance should be increased by the transferred amount"
        );

        // Check the logs.
        claim_eq!(logger.logs.len(), 4, "Four events should be logged");
        claim_eq!(
            logger.logs[3],
            to_bytes(&Cis2Event::Transfer(TransferEvent {
                from:     ADDRESS_1,
                to:       ADDRESS_0,
                token_id: TOKEN_1,
                amount:   ContractTokenAmount::from(1),
            })),
            "Incorrect event emitted"
        )
    }

    /// Test permit updateOperator.
    #[concordium_test]
    fn test_permit_update_operator() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_owner(ACCOUNT_0);
        ctx.set_self_address(ContractAddress {
            index:    0,
            subindex: 0,
        });
        ctx.set_named_entrypoint(OwnedEntrypointName::new_unchecked(
            "contract_update_operator".into(),
        ));
        ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(0));

        // and parameter.
        let register_public_key_param = RegisterPublicKeyParam {
            account:    ACCOUNT_1,
            public_key: PUBLIC_KEY,
        };

        let parameter = RegisterPublicKeyParams(vec![register_public_key_param]);
        let parameter_bytes = to_bytes(&parameter);

        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Register public key.
        let result: ContractResult<()> =
            contract_register_public_keys(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Create input parematers for the `permit` updateOperator function.
        let update_operator = UpdateOperator {
            update:   OperatorUpdate::Add,
            operator: ADDRESS_0,
        };
        let payload = UpdateOperatorParams(vec![update_operator]);

        let mut inner_signature_map = BTreeMap::new();
        inner_signature_map.insert(0, SIGNATURE_UPDATE_OPERATOR);

        let mut signature_map = BTreeMap::new();
        signature_map.insert(0, inner_signature_map);

        let crypto_primitives = TestCryptoPrimitives::new();

        let permit_transfer_param = PermitParam {
            signature: signature_map,
            signer:    ACCOUNT_1,
            message:   PermitMessage {
                timestamp:        Timestamp::from_timestamp_millis(10000000000),
                contract_address: ContractAddress {
                    index:    0,
                    subindex: 0,
                },
                entry_point:      OwnedEntrypointName::new_unchecked(
                    "contract_update_operator".into(),
                ),
                nonce:            1,
                payload:          PermitPayload::UpdateOperator(payload),
            },
        };

        let parameter_bytes = to_bytes(&permit_transfer_param);
        ctx.set_parameter(&parameter_bytes);

        // Inovke `permit` function.
        let result: ContractResult<()> =
            contract_permit(&ctx, &mut host, &mut logger, &crypto_primitives);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        let is_operator = host.state().is_operator(&ADDRESS_0, &ADDRESS_1);
        claim!(is_operator, "Account should be an operator");

        // Check the logs.
        claim_eq!(logger.logs.len(), 2, "Two events should be logged");
        claim_eq!(
            logger.logs[1],
            to_bytes(&Cis2Event::<ContractTokenId, ContractTokenAmount>::UpdateOperator(
                UpdateOperatorEvent {
                    owner:    ADDRESS_1,
                    operator: ADDRESS_0,
                    update:   OperatorUpdate::Add,
                }
            )),
            "Incorrect event emitted"
        )
    }
}
