//! A NFT smart contract example using the Concordium Token Standard CIS2 with
//! sponsored transactions (CIS3).
//!
//! # Description
//! An instance of this smart contract can contain a number of different tokens
//! each identified by a token ID. A token is then globally identified by the
//! contract address together with the token ID.
//!
//! In this example the contract is initialized with no tokens, and tokens can
//! be minted through a `mint` contract function. No functionality to burn a
//! token is defined in this example.
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
//! signed message by the private key corresponding to the public key that
//! is registered for that account.
#![cfg_attr(not(feature = "std"), no_std)]

use concordium_cis2::*;
use concordium_std::{collections::BTreeMap, EntrypointName, *};

/// The url for the token metadata. Every `token_id` in this contract has the
/// same metadata url for simplicity.
const TOKEN_METADATA_URL: &str = "https://gist.githubusercontent.com/abizjak/ab5b6fc0afb78acf23ee24d979eb7639/raw/7c03f174d628df1d2fd0dc8cffb319c89e770708/metadata.json";

/// The standard identifier for the CIS-3: Concordium Token Standard 3.
pub const CIS3_STANDARD_IDENTIFIER: StandardIdentifier<'static> =
    StandardIdentifier::new_unchecked("CIS-3");

/// List of supported standards by this contract address.
const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 3] =
    [CIS0_STANDARD_IDENTIFIER, CIS2_STANDARD_IDENTIFIER, CIS3_STANDARD_IDENTIFIER];

/// List of supported entrypoints by the `permit` function (CIS3 standard).
const SUPPORTS_PERMIT_ENTRYPOINTS: [EntrypointName; 2] =
    [EntrypointName::new_unchecked("updateOperator"), EntrypointName::new_unchecked("transfer")];

/// Tag for the CIS3 Nonce event.
pub const NONCE_EVENT_TAG: u8 = u8::MAX - 5;

/// Tagged events to be serialized for the event log.
#[derive(Debug, Serial)]
#[concordium(repr(u8))]
enum Event {
    /// The event tracks the nonce used by the signer of the `PermitMessage`
    /// whenever the `permit` function is invoked.
    #[concordium(tag = 250)]
    Nonce(NonceEvent),
}

/// The NonceEvent is logged when the `permit` function is invoked. The event
/// tracks the nonce used by the signer of the `PermitMessage`.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct NonceEvent {
    /// Account that signed the `PermitMessage`.
    pub account: AccountAddress,
    /// The nonce that was used in the `PermitMessage`.
    pub nonce:   u64,
}

// Implementing a custom schemaType to the `Event` combining all CIS2/CIS3
// events.
impl schema::SchemaType for Event {
    fn get_type() -> schema::Type {
        let mut event_map = BTreeMap::new();
        event_map.insert(
            NONCE_EVENT_TAG,
            (
                "Nonce".to_string(),
                schema::Fields::Named(vec![
                    (String::from("account"), AccountAddress::get_type()),
                    (String::from("nonce"), u64::get_type()),
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
pub type ContractTokenId = TokenIdU32;

/// Contract token amount.
/// Since the tokens are non-fungible the total supply of any token will be at
/// most 1 and it is fine to use a small type for representing token amounts.
pub type ContractTokenAmount = TokenAmountU8;

/// The parameter for the contract function `mint` which mints one
/// token to a given address.
#[derive(Serial, Deserial, SchemaType)]
pub struct MintParams {
    /// Owner of the newly minted token.
    pub owner: Address,
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
    /// Counter to increase the `token_id` at every mint function invoke.
    token_id_counter: u32,
    /// The state for each address.
    state:            StateMap<Address, AddressState<S>, S>,
    /// All of the token IDs
    all_tokens:       StateSet<ContractTokenId, S>,
    /// Map with contract addresses providing implementations of additional
    /// standards.
    implementors:     StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
    /// A registry to link an account to its next nonce. The nonce is used to
    /// prevent replay attacks of the signed message. The nonce is increased
    /// sequentially every time a signed message (corresponding to the
    /// account) is successfully executed in the `permit` function. This
    /// mapping keeps track of the next nonce that needs to be used by the
    /// account to generate a signature.
    nonces_registry:  StateMap<AccountAddress, u64, S>,
}

/// The parameter type for the contract function `supportsPermit`.
#[derive(Debug, Serialize, SchemaType)]
pub struct SupportsPermitQueryParams {
    /// The list of supportPermit queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<OwnedEntrypointName>,
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
/// Specifies the message that is signed.
#[derive(SchemaType, Serialize)]
pub struct PermitMessage {
    /// The contract_address that the signature is intended for.
    pub contract_address: ContractAddress,
    /// A nonce to prevent replay attacks.
    pub nonce:            u64,
    /// A timestamp to make signatures expire.
    pub timestamp:        Timestamp,
    /// The entry_point that the signature is intended for.
    pub entry_point:      OwnedEntrypointName,
    /// The serialized payload that should be forwarded to either the `transfer`
    /// or the `updateOperator` function.
    #[concordium(size_length = 2)]
    pub payload:          Vec<u8>,
}

/// The parameter type for the contract function `permit`.
/// Takes a signature, the signer, and the message that was signed.
#[derive(Serialize, SchemaType)]
pub struct PermitParam {
    /// Signature/s. The CIS3 standard supports multi-sig accounts but because
    /// the `public_key_registry` in this contract maps one public key to one
    /// account, only one signature has to be provided for this contract. This
    /// signature has to be at the key 0 in both maps below.
    pub signature: AccountSignatures,
    /// Account that created the above signature.
    pub signer:    AccountAddress,
    /// Message that was signed.
    pub message:   PermitMessage,
}

#[derive(Serialize)]
pub struct PermitParamPartial {
    /// Signature/s. The CIS3 standard supports multi-sig accounts but because
    /// the `public_key_registry` in this contract maps one public key to one
    /// account, only one signature has to be provided for this contract. This
    /// signature has to be at the key 0 in both maps below.
    signature: AccountSignatures,
    /// Account that created the above signature.
    signer:    AccountAddress,
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
    /// Failed to query public key of account because account does not exist on
    /// chain.
    AccountDoesNotExist,
    /// Only account with one credential and one public key is supported
    OnlyAccountWithOneCredentialAndOnePublicKeySupported,
    /// Failed to mint new tokens because one of the token IDs already exists
    /// in this contract.
    TokenIdAlreadyExists,
    /// Failed to mint new token because max token_id is reached.
    MaxTokenID,
    /// Failed to invoke a contract.
    InvokeContractError,
    /// Failed to verify signature because signer account does not exist on
    /// chain.
    MissingAccount,
    /// Failed to verify signature because data was malformed.
    MalformedData,
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

/// Mapping CustomContractError to ContractError
impl From<CheckAccountSignatureError> for CustomContractError {
    fn from(e: CheckAccountSignatureError) -> Self {
        match e {
            CheckAccountSignatureError::MissingAccount => Self::MissingAccount,
            CheckAccountSignatureError::MalformedData => Self::MalformedData,
        }
    }
}

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
            token_id_counter: 0,
            state:            state_builder.new_map(),
            all_tokens:       state_builder.new_set(),
            implementors:     state_builder.new_map(),
            nonces_registry:  state_builder.new_map(),
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
    state:      Vec<(Address, ViewAddressState)>,
    all_tokens: Vec<ContractTokenId>,
    all_nonces: Vec<(AccountAddress, u64)>,
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

    let mut all_nonces = Vec::new();
    for (account_address, nonce) in state.nonces_registry.iter() {
        all_nonces.push((*account_address, *nonce));
    }

    Ok(ViewState {
        state: inner_state,
        all_tokens,
        all_nonces,
    })
}

/// The parameter type for the contract function `registerPublicKey`.
#[derive(Debug, Serialize, SchemaType)]
pub struct RegisterPublicKeyParams(#[concordium(size_length = 2)] pub Vec<RegisterPublicKeyParam>);

/// Mint one token with a given address as the owner of this token.
/// There are no restrictions on who can call the mint function.
/// Logs a `Mint` and a `TokenMetadata` event for each token.
/// The url for the token metadata is the same for all token IDs.
///
/// It rejects if:
/// - Fails to parse parameter.
/// - Any of the tokens fails to be minted, which could be if:
///     - Fails to log Mint event
///     - Fails to log TokenMetadata event
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
    // Parse the parameter.
    let params: MintParams = ctx.parameter_cursor().get()?;

    // Increase the token_id_counter.
    host.state_mut().token_id_counter += 1;

    let token_id = concordium_cis2::TokenIdU32(host.state().token_id_counter);

    // Check that max token_id is not reached.
    ensure!(
        token_id != concordium_cis2::TokenIdU32(u32::MAX),
        CustomContractError::MaxTokenID.into()
    );

    let (state, builder) = host.state_and_builder();

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
            url:  String::from(TOKEN_METADATA_URL),
            hash: None,
        },
    }))?;

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

/// Helper function that can be invoked at the front-end to serialize the
/// `PermitMessage` before signing it in the wallet.
#[receive(contract = "cis3_nft", name = "serializationHelper", parameter = "PermitMessage")]
fn contract_serialization_helper<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    _host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    Ok(())
}

/// Helper function to calculate the `message_hash`.
#[receive(
    contract = "cis3_nft",
    name = "viewMessageHash",
    parameter = "PermitParam",
    return_value = "[u8;32]",
    crypto_primitives,
    mutable
)]
fn contract_view_message_hash<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    _host: &mut impl HasHost<State<S>, StateApiType = S>,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<[u8; 32]> {
    // Parse the parameter.
    let mut cursor = ctx.parameter_cursor();
    // The input parameter is `PermitParam` but we only read the initial part of it
    // with `PermitParamPartial`. I.e. we read the `signature` and the
    // `signer`, but not the `message` here.
    let param: PermitParamPartial = cursor.get()?;

    // The input parameter is `PermitParam` but we have only read the initial part
    // of it with `PermitParamPartial` so far. We read in the `message` now.
    // `(cursor.size() - cursor.cursor_position()` is the length of the message in
    // bytes.
    let mut message_bytes = vec![0; (cursor.size() - cursor.cursor_position()) as usize];

    cursor.read_exact(&mut message_bytes)?;

    // The message signed in the Concordium browser wallet is prepended with the
    // `account` address and 8 zero bytes. Accounts in the Concordium browser wallet
    // can either sign a regular transaction (in that case the prepend is
    // `account` address and the nonce of the account which is by design >= 1)
    // or sign a message (in that case the prepend is `account` address and 8 zero
    // bytes). Hence, the 8 zero bytes ensure that the user does not accidentally
    // sign a transaction. The account nonce is of type u64 (8 bytes).
    let mut msg_prepend = vec![0; 32 + 8];
    // Prepend the `account` address of the signer.
    msg_prepend[0..32].copy_from_slice(param.signer.as_ref());
    // Prepend 8 zero bytes.
    msg_prepend[32..40].copy_from_slice(&[0u8; 8]);
    // Calculate the message hash.
    let message_hash =
        crypto_primitives.hash_sha2_256(&[&msg_prepend[0..40], &message_bytes].concat()).0;

    Ok(message_hash)
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
        param.signature.sigs.len() == 1
            && param
                .signature
                .sigs
                .get(&0)
                .ok_or(CustomContractError::SignatureMapMisconfigured)?
                .sigs
                .len()
                == 1,
        CustomContractError::SignatureMapMisconfigured.into()
    );

    // Update the nonce.
    let mut entry = host.state_mut().nonces_registry.entry(param.signer).or_insert_with(|| 0);

    // Get the current nonce.
    let nonce = *entry;
    // Bump nonce.
    *entry += 1;
    drop(entry);

    let message = param.message;

    // Check the nonce to prevent replay attacks.
    ensure_eq!(message.nonce, nonce, CustomContractError::NonceMismatch.into());

    // Check that the signature was intended for this contract.
    ensure_eq!(
        message.contract_address,
        ctx.self_address(),
        CustomContractError::WrongContract.into()
    );

    // Check signature is not expired.
    ensure!(message.timestamp > ctx.metadata().slot_time(), CustomContractError::Expired.into());

    let message_hash = contract_view_message_hash(ctx, host, crypto_primitives)?;

    // Check signature.
    let valid_signature =
        host.check_account_signature(param.signer, &param.signature, &message_hash)?;
    ensure!(valid_signature, CustomContractError::WrongSignature.into());

    if message.entry_point.as_entrypoint_name() == EntrypointName::new_unchecked("transfer") {
        // Transfer the tokens.

        let TransferParams(transfers): TransferParameter = from_bytes(&message.payload)?;

        for transfer_struct in transfers {
            ensure!(
                transfer_struct.from.matches_account(&param.signer),
                ContractError::Unauthorized
            );

            transfer(transfer_struct, host, logger)?
        }
    } else if message.entry_point.as_entrypoint_name()
        == EntrypointName::new_unchecked("updateOperator")
    {
        // Update the operator.
        let UpdateOperatorParams(updates): UpdateOperatorParams = from_bytes(&message.payload)?;

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
    } else {
        bail!(CustomContractError::WrongEntryPoint.into())
    }

    // Log the nonce event.
    logger.log(&Event::Nonce(NonceEvent {
        account: param.signer,
        nonce,
    }))?;

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
    Ok(ContractBalanceOfQueryResponse::from(response))
}

/// Response type for the function `publicKeyOf`.
#[derive(Debug, Serialize, SchemaType)]
pub struct PublicKeyOfQueryResponse(
    #[concordium(size_length = 2)] pub Vec<Option<AccountPublicKeys>>,
);

impl From<Vec<Option<AccountPublicKeys>>> for PublicKeyOfQueryResponse {
    fn from(results: concordium_std::Vec<Option<AccountPublicKeys>>) -> Self {
        PublicKeyOfQueryResponse(results)
    }
}

/// The parameter type for the contract function `publicKeyOf`. A query for the
/// public key and nonce of a given account.
#[derive(Debug, Serialize, SchemaType)]
pub struct VecOfAccountAddresses {
    /// List of public key queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<AccountAddressStruct>,
}

/// Part of the parameter type for the contract function `publicKeyOf`.
#[derive(Debug, Serialize, SchemaType)]
pub struct AccountAddressStruct {
    /// The account for which the public key and nonce should be queried.
    pub account: AccountAddress,
}

/// Get the public keys of accounts. `None` is returned if the account does not
/// exist on chain.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis3_nft",
    name = "publicKeyOf",
    parameter = "VecOfAccountAddresses",
    return_value = "PublicKeyOfQueryResponse",
    error = "ContractError"
)]
fn contract_public_key_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<PublicKeyOfQueryResponse> {
    // Parse the parameter.
    let params: VecOfAccountAddresses = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response: Vec<Option<AccountPublicKeys>> = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the public_key.
        let public_keys = host.account_public_keys(query.account).ok();

        response.push(public_keys);
    }
    let result = PublicKeyOfQueryResponse::from(response);
    Ok(result)
}

/// Response type for the function `nonceOf`.
#[derive(Debug, Serialize, SchemaType)]
pub struct NonceOfQueryResponse(#[concordium(size_length = 2)] pub Vec<u64>);

impl From<Vec<u64>> for NonceOfQueryResponse {
    fn from(results: concordium_std::Vec<u64>) -> Self { NonceOfQueryResponse(results) }
}

/// Get the nonces of accounts.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis3_nft",
    name = "nonceOf",
    parameter = "VecOfAccountAddresses",
    return_value = "NonceOfQueryResponse",
    error = "ContractError"
)]
fn contract_nonce_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<NonceOfQueryResponse> {
    // Parse the parameter.
    let params: VecOfAccountAddresses = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response: Vec<u64> = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the next nonce.
        let nonce =
            host.state().nonces_registry.get(&query.account).map(|nonce| *nonce).unwrap_or(0);

        response.push(nonce);
    }
    Ok(NonceOfQueryResponse::from(response))
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
            url:  String::from(TOKEN_METADATA_URL),
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

/// Get the entrypoints supported by the `permit` function given a
/// list of entrypoints.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis3_nft",
    name = "supportsPermit",
    parameter = "SupportsPermitQueryParams",
    return_value = "SupportsQueryResponse",
    error = "ContractError"
)]
fn contract_supports_permit<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    _host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<SupportsQueryResponse> {
    // Parse the parameter.
    let params: SupportsPermitQueryParams = ctx.parameter_cursor().get()?;

    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for entrypoint in params.queries {
        if SUPPORTS_PERMIT_ENTRYPOINTS.contains(&entrypoint.as_entrypoint_name()) {
            response.push(SupportResult::Support);
        } else {
            response.push(SupportResult::NoSupport);
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
    const TOKEN_1: ContractTokenId = TokenIdU32(1);
    const TOKEN_2: ContractTokenId = TokenIdU32(2);

    /// Test helper function which creates a contract state with two tokens with
    /// id `TOKEN_1` owned by `ADDRESS_0` and id `TOKEN_2` owned by `ADDRESS_1`.
    fn initial_state<S: HasStateApi>(state_builder: &mut StateBuilder<S>) -> State<S> {
        let mut state = State::empty(state_builder);
        state.mint(TOKEN_1, &ADDRESS_0, state_builder).expect_report("Failed to mint TOKEN_1");
        state.mint(TOKEN_2, &ADDRESS_1, state_builder).expect_report("Failed to mint TOKEN_2");
        state.token_id_counter = 2;
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
        let parameter = MintParams {
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
        claim_eq!(host.state().all_tokens.iter().count(), 1, "Expected one token in the state.");

        let balance0 =
            host.state().balance(&TOKEN_1, &ADDRESS_0).expect_report("Token is expected to exist");
        claim_eq!(balance0, 1.into(), "Tokens should be owned by the given address 0");

        // Check the logs
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
                    token_id:     TOKEN_1,
                    metadata_url: MetadataUrl {
                        url:  TOKEN_METADATA_URL.to_string(),
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
            token_id: TOKEN_1,
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
            host.state().balance(&TOKEN_1, &ADDRESS_0).expect_report("Token is expected to exist");
        let balance1 =
            host.state().balance(&TOKEN_1, &ADDRESS_1).expect_report("Token is expected to exist");
        let balance2 =
            host.state().balance(&TOKEN_2, &ADDRESS_1).expect_report("Token is expected to exist");
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
                token_id: TOKEN_1,
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
            token_id: TOKEN_1,
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
            token_id: TOKEN_1,
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
            host.state().balance(&TOKEN_1, &ADDRESS_0).expect_report("Token is expected to exist");
        let balance1 = host
            .state_mut()
            .balance(&TOKEN_1, &ADDRESS_1)
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
                token_id: TOKEN_1,
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
        let mut nonces_registry = state_builder.new_map();
        nonces_registry.insert(ACCOUNT_1, 0);
        nonces_registry.insert(ACCOUNT_2, 1);

        let mut all_tokens = state_builder.new_set();
        all_tokens.insert(TOKEN_1);
        all_tokens.insert(TOKEN_2);

        let mut state = state_builder.new_map();
        let mut operators = state_builder.new_set();
        operators.insert(ADDRESS_2);
        let mut owned_tokens = state_builder.new_set();
        owned_tokens.insert(TOKEN_1);
        owned_tokens.insert(TOKEN_2);
        state.insert(ADDRESS_1, AddressState {
            owned_tokens,
            operators,
        });

        let state = State {
            token_id_counter: 2,
            state,
            all_tokens,
            implementors: state_builder.new_map(),
            nonces_registry,
        };

        let host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result = contract_view(&ctx, &host);

        let returned_view_state = result.expect_report("Failed getting contract_view result value");

        claim_eq!(
            returned_view_state.all_nonces,
            [(ACCOUNT_1, 0), (ACCOUNT_2, 1)],
            "Correct public keys should be returned by the view function"
        );

        claim_eq!(
            returned_view_state.all_tokens,
            vec![TOKEN_1, TOKEN_2],
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
                owned_tokens: vec![TOKEN_1, TOKEN_2],
                operators:    vec![concordium_std::Address::Account(ACCOUNT_2)],
            },
            "Correct ViewAddressState should be returned by the view function"
        );
    }

    // /// Test permit transfer.
    // #[concordium_test]
    // fn test_permit_transfer() {
    //     // Setup the context
    //     let mut ctx = TestReceiveContext::empty();
    //     ctx.set_sender(ADDRESS_0);
    //     ctx.set_owner(ACCOUNT_0);
    //     ctx.set_self_address(ContractAddress {
    //         index: 0,
    //         subindex: 0,
    //     });
    //     ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(0));

    //     let mut logger = TestLogger::init();
    //     let mut state_builder = TestStateBuilder::new();
    //     let state = initial_state(&mut state_builder);
    //     let mut host = TestHost::new(state, state_builder);

    //     // Register public key.
    //     // let result: ContractResult<()> =
    //     //     contract_register_public_keys(&ctx, &mut host, &mut logger);

    //     // // Check the result.
    //     // claim!(result.is_ok(), "Results in rejection");

    //     // // Check the result.
    //     // claim!(result.is_ok(), "Results in rejection");

    //     // Create input parematers for the `permit` transfer function.
    //     let transfer = Transfer {
    //         from: ADDRESS_1,
    //         to: Receiver::from_account(ACCOUNT_0),
    //         token_id: TOKEN_2,
    //         amount: ContractTokenAmount::from(1),
    //         data: AdditionalData::empty(),
    //     };
    //     let payload = TransferParams::from(vec![transfer]);

    //     let mut inner_signature_map = BTreeMap::new();
    //     inner_signature_map.insert(0u8,
    // concordium_std::Signature::Ed25519(SIGNATURE_TRANSFER));

    //     let mut signature_map = BTreeMap::new();
    //     signature_map.insert(
    //         0u8,
    //         CredentialSignatures {
    //             sigs: inner_signature_map,
    //         },
    //     );

    //     let permit_transfer_param = PermitParam {
    //         signature: AccountSignatures {
    //             sigs: signature_map,
    //         },
    //         signer: ACCOUNT_1,
    //         message: PermitMessage {
    //             timestamp: Timestamp::from_timestamp_millis(10000000000),
    //             contract_address: ContractAddress {
    //                 index: 0,
    //                 subindex: 0,
    //             },
    //             entry_point:
    // OwnedEntrypointName::new_unchecked("transfer".into()),
    // nonce: 0,             payload: to_bytes(&payload),
    //         },
    //     };

    //     let parameter_bytes = to_bytes(&permit_transfer_param);
    //     ctx.set_parameter(&parameter_bytes);

    //     let crypto_primitives = TestCryptoPrimitives::new();

    //     // Check the state.
    //     let balance0 =
    //         host.state().balance(&TOKEN_2, &ADDRESS_0).expect_report("Token
    // is expected to exist");     let balance1 = host
    //         .state_mut()
    //         .balance(&TOKEN_2, &ADDRESS_1)
    //         .expect_report("Token is expected to exist");

    //     claim_eq!(balance0, 0.into(), "Token balance of address0 should be
    // 0");     claim_eq!(balance1, 1.into(), "Token balance of address1
    // should be 1");

    //     // Invoke `viewMessageHash` function.
    //     let result: ContractResult<[u8; 32]> =
    //         contract_view_message_hash(&ctx, &mut host, &crypto_primitives);

    //     let message_hash = result.expect_report("Message hash should be
    // viewable");

    //     // Check signature.
    //     claim!(
    //         crypto_primitives.verify_ed25519_signature(
    //             PUBLIC_KEY,
    //             SIGNATURE_TRANSFER,
    //             &message_hash
    //         ),
    //         "Signature should be correct"
    //     );

    //     // Inovke `permit` function.
    //     let result: ContractResult<()> =
    //         contract_permit(&ctx, &mut host, &mut logger,
    // &crypto_primitives);

    //     // Check the result.
    //     claim!(result.is_ok(), "Results in rejection");

    //     // Check the state.
    //     let balance0 =
    //         host.state().balance(&TOKEN_2, &ADDRESS_0).expect_report("Token
    // is expected to exist");     let balance1 = host
    //         .state_mut()
    //         .balance(&TOKEN_2, &ADDRESS_1)
    //         .expect_report("Token is expected to exist");

    //     claim_eq!(
    //         balance0,
    //         1.into(),
    //         "Token receiver balance should be decreased by the transferred
    // amount"     );
    //     claim_eq!(
    //         balance1,
    //         0.into(),
    //         "Token owner balance should be increased by the transferred
    // amount"     );

    //     // Check the logs.
    //     claim_eq!(logger.logs.len(), 3, "Three events should be logged");
    //     claim_eq!(
    //         logger.logs[1],
    //         to_bytes(&Cis2Event::Transfer(TransferEvent {
    //             from: ADDRESS_1,
    //             to: ADDRESS_0,
    //             token_id: TOKEN_2,
    //             amount: ContractTokenAmount::from(1),
    //         })),
    //         "Incorrect transfer event logged"
    //     );
    //     claim_eq!(
    //         logger.logs[2],
    //         to_bytes(&Event::Nonce(NonceEvent {
    //             account: ACCOUNT_1,
    //             nonce: 0,
    //         })),
    //         "Incorrect nonce event logged"
    //     )
    // }

    // /// Test permit updateOperator.
    // #[concordium_test]
    // fn test_permit_update_operator() {
    //     // Setup the context
    //     let mut ctx = TestReceiveContext::empty();
    //     ctx.set_sender(ADDRESS_0);
    //     ctx.set_owner(ACCOUNT_0);
    //     ctx.set_self_address(ContractAddress {
    //         index: 0,
    //         subindex: 0,
    //     });
    //     ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(0));

    //     // and parameter.
    //     let register_public_key_param = RegisterPublicKeyParam {
    //         account: ACCOUNT_1,
    //         public_key: PUBLIC_KEY,
    //     };

    //     let parameter =
    // RegisterPublicKeyParams(vec![register_public_key_param]);
    //     let parameter_bytes = to_bytes(&parameter);

    //     ctx.set_parameter(&parameter_bytes);

    //     let mut logger = TestLogger::init();
    //     let mut state_builder = TestStateBuilder::new();
    //     let state = initial_state(&mut state_builder);
    //     let mut host = TestHost::new(state, state_builder);

    //     // Register public key.
    //     let result: ContractResult<()> =
    //         contract_register_public_keys(&ctx, &mut host, &mut logger);

    //     // Check the result.
    //     claim!(result.is_ok(), "Results in rejection");

    //     // Create input parematers for the `permit` updateOperator function.
    //     let update_operator = UpdateOperator {
    //         update: OperatorUpdate::Add,
    //         operator: ADDRESS_0,
    //     };
    //     let payload = UpdateOperatorParams(vec![update_operator]);

    //     let mut inner_signature_map = BTreeMap::new();
    //     inner_signature_map.insert(0, SIGNATURE_UPDATE_OPERATOR);

    //     let mut signature_map = BTreeMap::new();
    //     signature_map.insert(0, inner_signature_map);

    //     let crypto_primitives = TestCryptoPrimitives::new();

    //     let permit_transfer_param = PermitParam {
    //         signature: signature_map,
    //         signer: ACCOUNT_1,
    //         message: PermitMessage {
    //             timestamp: Timestamp::from_timestamp_millis(10000000000),
    //             contract_address: ContractAddress {
    //                 index: 0,
    //                 subindex: 0,
    //             },
    //             entry_point:
    // OwnedEntrypointName::new_unchecked("updateOperator".into()),
    //             nonce: 0,
    //             payload: to_bytes(&payload),
    //         },
    //     };

    //     let parameter_bytes = to_bytes(&permit_transfer_param);
    //     ctx.set_parameter(&parameter_bytes);

    //     // Invoke `viewMessageHash` function.
    //     let result: ContractResult<[u8; 32]> =
    //         contract_view_message_hash(&ctx, &mut host, &crypto_primitives);

    //     let message_hash = result.expect_report("Message hash should be
    // viewable");

    //     // Check signature.
    //     claim!(
    //         crypto_primitives.verify_ed25519_signature(
    //             PUBLIC_KEY,
    //             SIGNATURE_UPDATE_OPERATOR,
    //             &message_hash
    //         ),
    //         "Signature should be correct"
    //     );

    //     // Inovke `permit` function.
    //     let result: ContractResult<()> =
    //         contract_permit(&ctx, &mut host, &mut logger,
    // &crypto_primitives);

    //     // Check the result.
    //     claim!(result.is_ok(), "Results in rejection");

    //     // Check the state.
    //     let is_operator = host.state().is_operator(&ADDRESS_0, &ADDRESS_1);
    //     claim!(is_operator, "Account should be an operator");

    //     // Check the logs.
    //     claim_eq!(logger.logs.len(), 3, "Three events should be logged");
    //     claim_eq!(
    //         logger.logs[1],
    //         to_bytes(&Cis2Event::<ContractTokenId,
    // ContractTokenAmount>::UpdateOperator(             UpdateOperatorEvent
    // {                 owner: ADDRESS_1,
    //                 operator: ADDRESS_0,
    //                 update: OperatorUpdate::Add,
    //             }
    //         )),
    //         "Incorrect update operator event logged"
    //     );
    //     claim_eq!(
    //         logger.logs[2],
    //         to_bytes(&Event::Nonce(NonceEvent {
    //             account: ACCOUNT_1,
    //             nonce: 0,
    //         })),
    //         "Incorrect nonce event logged"
    //     )
    // }
}
