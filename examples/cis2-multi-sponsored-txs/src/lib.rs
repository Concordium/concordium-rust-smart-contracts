//! A multi token example implementation of the Concordium Token Standard CIS2
//! and the Concordium Sponsored Transaction Standard CIS3.
//!
//! # Description
//! An instance of this smart contract can contain a number of different token
//! types each identified by a token ID. A token type is then globally
//! identified by the contract address together with the token ID.
//!
//! In this example the contract is initialized with no tokens, and tokens can
//! be minted through a `mint` contract function, which can be called by anyone.
//! The `mint` function airdrops the `MINT_AIRDROP` amount of tokens to a
//! specified `owner` address in the input parameter. No functionality to burn
//! token is defined in this example.
//!
//! Note: The word 'address' refers to either an account address or a
//! contract address.
//!
//! This contract implements the Concordium Token Standard CIS2. In addition, it
//! implements the CIS3 standard which includes features for sponsored
//! transactions.
//!
//! The use case for CIS3 in this smart contract is for third-party service
//! providers (the owner of this contract) that deal with conventional
//! clients/users that don't want to acquire crypto (such as CCD) from an
//! exchange. The third-party has often traditional fiat channels open
//! (off-chain) with the conventional clients/users and wants to offer to submit
//! transactions on behalf of the user on-chain. The user/client has to sign its
//! intended transaction before communicating it (off-chain) to the third-party
//! service provider (often paying some fees in fiat money). The third-party
//! service provider submits the transaction on behalf of the user and pays the
//! transaction fee to execute the transaction on-chain.
//!
//! As follows from the CIS2 specification, the contract has a `transfer`
//! function for transferring an amount of a specific token type from one
//! address to another address. An address can enable and disable one or more
//! addresses as operators with the `updateOperator` function. An operator of
//! an address is allowed to transfer any tokens owned by this address.
//! As follows from the CIS3 specification, the contract has a `permit`
//! function. It is the sponsored counterpart to the `transfer/updateOperator`
//! function and can be executed by anyone on behalf of an account given a
//! signed message.
//!
//! This contract also contains an example of a function to be called when
//! receiving tokens. In which case the contract will forward the tokens to
//! the contract owner.
//! This function is not very useful and is only there to showcase a simple
//! implementation of a token receive hook.
//!
//! Concordium supports natively multi-sig accounts. Each account address on
//! Concordium is controlled by one or several credential(s) (real-world
//! identities) and each credential has one or several public-private key
//! pair(s). Both the key and signature structures of an account are represented
//! as two-level maps (e.g. BTreeMap<CredentialIndexU8,
//! BTreeMap<PublicKeyIndexU8, PublicKey>> or BTreeMap<CredentialIndexU8,
//! BTreeMap<SignatureIndexU8, Signature>>). The outer map of
//! `BTreeMap<CredentialIndexU8, BTreeMap<PublicKeyIndexU8, PublicKey>>` has an
//! `AccountThreshold` (number of credentials needed to sign the transaction
//! initiated by that account) and the inner map has a `SignatureThreshold`
//! (number of Signatures needed for a specific credential so that this
//! credential is considered to have signed the transaction initiated by that
//! account). The CIS3 standard supports multi-sig accounts. For basic accounts
//! (that have exactly one credential and exactly one public key for that
//! credential), the signaturesMaps/publicKeyMaps in this contract, will have
//! only one value at key 0 in the inner and outer maps.

#![cfg_attr(not(feature = "std"), no_std)]
use concordium_cis2::*;
use concordium_std::{collections::BTreeMap, EntrypointName, *};

/// List of supported standards by this contract address.
const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 2] =
    [CIS0_STANDARD_IDENTIFIER, CIS2_STANDARD_IDENTIFIER];

/// List of supported entrypoints by the `permit` function (CIS3 standard).
const SUPPORTS_PERMIT_ENTRYPOINTS: [EntrypointName; 2] =
    [EntrypointName::new_unchecked("updateOperator"), EntrypointName::new_unchecked("transfer")];

/// Tag for the CIS3 Nonce event.
pub const NONCE_EVENT_TAG: u8 = u8::MAX - 5;

/// The amount of tokens to airdrop when the mint function is invoked.
pub const MINT_AIRDROP: TokenAmountU64 = TokenAmountU64(100);

/// Tagged events to be serialized for the event log.
#[derive(Debug, Serial, Deserial, PartialEq, Eq)]
#[concordium(repr(u8))]
pub enum Event {
    /// The event tracks the nonce used by the signer of the `PermitMessage`
    /// whenever the `permit` function is invoked.
    #[concordium(tag = 250)]
    Nonce(NonceEvent),
    #[concordium(forward = cis2_events)]
    Cis2Event(Cis2Event<ContractTokenId, ContractTokenAmount>),
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

// Types

/// Contract token ID type.
/// To save bytes we use a small token ID type, but is limited to be represented
/// by a `u8`.
pub type ContractTokenId = TokenIdU8;

/// Contract token amount type.
pub type ContractTokenAmount = TokenAmountU64;

/// The parameter for the contract function `mint` which mints/airdrops a number
/// of tokens to the owner address.
#[derive(Serialize, SchemaType)]
pub struct MintParams {
    /// Owner of the newly minted tokens.
    pub owner:        Address,
    /// The metadata_url of the token (needs to be present for the first time
    /// this token_id is minted).
    pub metadata_url: MetadataUrl,
    /// The token_id to mint/create additional tokens.
    pub token_id:     ContractTokenId,
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
    state:           StateMap<Address, AddressState<S>, S>,
    /// All of the token IDs
    tokens:          StateMap<ContractTokenId, MetadataUrl, S>,
    /// Map with contract addresses providing implementations of additional
    /// standards.
    implementors:    StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
    /// A registry to link an account to its next nonce. The nonce is used to
    /// prevent replay attacks of the signed message. The nonce is increased
    /// sequentially every time a signed message (corresponding to the
    /// account) is successfully executed in the `permit` function. This
    /// mapping keeps track of the next nonce that needs to be used by the
    /// account to generate a signature.
    nonces_registry: StateMap<AccountAddress, u64, S>,
}
/// The parameter type for the contract function `supportsPermit`.
#[derive(Debug, Serialize, SchemaType)]
pub struct SupportsPermitQueryParams {
    /// The list of supportPermit queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<OwnedEntrypointName>,
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
    /// Signature/s. The CIS3 standard supports multi-sig accounts.
    pub signature: AccountSignatures,
    /// Account that created the above signature.
    pub signer:    AccountAddress,
    /// Message that was signed.
    pub message:   PermitMessage,
}

#[derive(Serialize)]
pub struct PermitParamPartial {
    /// Signature/s. The CIS3 standard supports multi-sig accounts.
    signature: AccountSignatures,
    /// Account that created the above signature.
    signer:    AccountAddress,
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
    /// Invalid contract name.
    InvalidContractName,
    /// Only a smart contract can call this function.
    ContractOnly,
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
}

pub type ContractError = Cis2Error<CustomContractError>;

pub type ContractResult<A> = Result<A, ContractError>;

/// Mapping account signature error to CustomContractError
impl From<CheckAccountSignatureError> for CustomContractError {
    fn from(e: CheckAccountSignatureError) -> Self {
        match e {
            CheckAccountSignatureError::MissingAccount => Self::MissingAccount,
            CheckAccountSignatureError::MalformedData => Self::MalformedData,
        }
    }
}

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

impl State {
    /// Construct a state with no tokens
    fn empty(state_builder: &mut StateBuilder) -> Self {
        State {
            state:           state_builder.new_map(),
            tokens:          state_builder.new_map(),
            implementors:    state_builder.new_map(),
            nonces_registry: state_builder.new_map(),
        }
    }

    /// Mints an amount of tokens with a given address as the owner.
    fn mint(
        &mut self,
        token_id: &ContractTokenId,
        mint_param: &MintParams,
        owner: &Address,
        state_builder: &mut StateBuilder,
    ) {
        self.tokens.insert(*token_id, mint_param.metadata_url.to_owned());
        let mut owner_state =
            self.state.entry(*owner).or_insert_with(|| AddressState::empty(state_builder));
        let mut owner_balance = owner_state.balances.entry(*token_id).or_insert(0.into());
        *owner_balance += MINT_AIRDROP;
    }

    /// Check that the token ID currently exists in this contract.
    #[inline(always)]
    fn contains_token(&self, token_id: &ContractTokenId) -> bool {
        self.get_token(token_id).is_some()
    }

    fn get_token(&self, token_id: &ContractTokenId) -> Option<MetadataUrl> {
        self.tokens.get(token_id).map(|x| x.to_owned())
    }

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
        state_builder: &mut StateBuilder,
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
        self.implementors.insert(std_id, implementors);
    }
}

// Contract functions

/// Initialize contract instance with a no token types.
#[init(
    contract = "cis2_multi_sponsored_txs",
    event = "Cis2Event<ContractTokenId, ContractTokenAmount>"
)]
fn contract_init(_ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<State> {
    // Construct the initial contract state.
    Ok(State::empty(state_builder))
}

#[derive(Serialize, SchemaType, PartialEq, Eq, Debug)]
pub struct ViewAddressState {
    pub balances:  Vec<(ContractTokenId, ContractTokenAmount)>,
    pub operators: Vec<Address>,
}

#[derive(Serialize, SchemaType, PartialEq, Eq)]
pub struct ViewState {
    pub state:  Vec<(Address, ViewAddressState)>,
    pub tokens: Vec<ContractTokenId>,
}

/// View function for testing. This reports on the entire state of the contract
/// for testing purposes. In a realistic example there `balance_of` and similar
/// functions with a smaller response.
#[receive(contract = "cis2_multi_sponsored_txs", name = "view", return_value = "ViewState")]
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
        tokens.push(*v.0);
    }

    Ok(ViewState {
        state: inner_state,
        tokens,
    })
}

/// Mint/Airdrops the fixed amount of `MINT_AIRDROP` of new tokens to the
/// `owner` address. ATTENTION: Can be called by anyone. You should add your
/// custom access control to this function.
///
/// Logs a `Mint` and a `TokenMetadata` event for each token.
/// The url for the token metadata is the token ID encoded in hex, appended on
/// the `TOKEN_METADATA_BASE_URL`.
///
/// It rejects if:
/// - Fails to parse parameter.
/// - Fails to log Mint event.
/// - Fails to log TokenMetadata event.
#[receive(
    contract = "cis2_multi_sponsored_txs",
    name = "mint",
    parameter = "MintParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_mint(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let params: MintParams = ctx.parameter_cursor().get()?;

    let (state, builder) = host.state_and_builder();
    // Mint the token in the state.
    state.mint(&params.token_id, &params, &params.owner, builder);

    // Event for minted token.
    logger.log(&Cis2Event::Mint(MintEvent {
        token_id: params.token_id,
        amount:   MINT_AIRDROP,
        owner:    params.owner,
    }))?;

    // Metadata URL for the token.
    logger.log(&Cis2Event::TokenMetadata::<_, ContractTokenAmount>(TokenMetadataEvent {
        token_id:     params.token_id,
        metadata_url: params.metadata_url,
    }))?;
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
// #[receive(
//     contract = "cis2_multi_sponsored_txs",
//     name = "transfer",
//     parameter = "TransferParameter",
//     error = "ContractError",
//     enable_logger,
//     mutable
// )]
// fn contract_transfer(
//     ctx: &ReceiveContext,
//     host: &mut Host<State>,
//     logger: &mut impl HasLogger,
// ) -> ContractResult<()> {
//     // Parse the parameter.
//     let TransferParams(transfers): TransferParameter = ctx.parameter_cursor().get()?;
//     // Get the sender who invoked this contract function.
//     let sender = ctx.sender();

//     for Transfer {
//         token_id,
//         amount,
//         from,
//         to,
//         data,
//     } in transfers
//     {
//         let (state, builder) = host.state_and_builder();
//         // Authenticate the sender for this transfer
//         ensure!(from == sender || state.is_operator(&sender, &from),
// ContractError::Unauthorized);         let to_address = to.address();
//         // Update the contract state
//         state.transfer(&token_id, amount, &from, &to_address, builder)?;

//         // Log transfer event
//         logger.log(&Cis2Event::Transfer(TransferEvent {
//             token_id,
//             amount,
//             from,
//             to: to_address,
//         }))?;

//         // If the receiver is a contract we invoke it.
//         if let Receiver::Contract(address, entrypoint_name) = to {
//             let parameter = OnReceivingCis2Params {
//                 token_id,
//                 amount,
//                 from,
//                 data,
//             };
//             host.invoke_contract(
//                 &address,
//                 &parameter,
//                 entrypoint_name.as_entrypoint_name(),
//                 Amount::zero(),
//             )?;
//         }
//     }
//     Ok(())
// }

/// Internal `transfer/permit` helper function. Invokes the `transfer`
/// function of the state. Logs a `Transfer` event and invokes a receive hook
/// function. The function assumes that the transfer is authorized.
fn transfer(
    transfer: concordium_cis2::Transfer<ContractTokenId, ContractTokenAmount>,
    host: &mut Host<State>,
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
    contract = "cis2_multi_sponsored_txs",
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
#[receive(
    contract = "cis2_multi_sponsored_txs",
    name = "serializationHelper",
    parameter = "PermitMessage"
)]
fn contract_serialization_helper(_ctx: &ReceiveContext, _host: &Host<State>) -> ContractResult<()> {
    Ok(())
}

/// Helper function to calculate the `message_hash`.
#[receive(
    contract = "cis2_multi_sponsored_txs",
    name = "viewMessageHash",
    parameter = "PermitParam",
    return_value = "[u8;32]",
    crypto_primitives,
    mutable
)]
fn contract_view_message_hash(
    ctx: &ReceiveContext,
    _host: &mut Host<State>,
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
    let mut msg_prepend = [0; 32 + 8];
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
/// - The signature can not be validated.
/// - Fails to log event.
/// - In case of a `transfer` action: it fails to be executed, which could be
///   if:
///     - The `token_id` does not exist.
///     - The token is not owned by the `from` address.
///     - The receive hook function call rejects.
#[receive(
    contract = "cis2_multi_sponsored_txs",
    name = "permit",
    parameter = "PermitParam",
    crypto_primitives,
    mutable,
    enable_logger
)]
fn contract_permit(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<()> {
    // Parse the parameter.
    let param: PermitParam = ctx.parameter_cursor().get()?;

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
fn update_operator(
    update: OperatorUpdate,
    sender: Address,
    operator: Address,
    state: &mut State,
    builder: &mut StateBuilder,
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
    contract = "cis2_multi_sponsored_txs",
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
        update_operator(param.update, sender, param.operator, state, builder, logger)?;
    }
    Ok(())
}

/// Enable or disable addresses as operators of the sender address.
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Fails to log event.
// #[receive(
//     contract = "cis2_multi_sponsored_txs",
//     name = "updateOperator",
//     parameter = "UpdateOperatorParams",
//     error = "ContractError",
//     enable_logger,
//     mutable
// )]
// fn contract_update_operator(
//     ctx: &ReceiveContext,
//     host: &mut Host<State>,
//     logger: &mut impl HasLogger,
// ) -> ContractResult<()> {
//     // Parse the parameter.
//     let UpdateOperatorParams(params) = ctx.parameter_cursor().get()?;
//     // Get the sender who invoked this contract function.
//     let sender = ctx.sender();

//     let (state, builder) = host.state_and_builder();
//     for param in params {
//         // Update the operator in the state.
//         match param.update {
//             OperatorUpdate::Add => state.add_operator(&sender, &param.operator, builder),
//             OperatorUpdate::Remove => state.remove_operator(&sender, &param.operator),
//         }

//         // Log the appropriate event
//         logger.log(&Cis2Event::<ContractTokenId, ContractTokenAmount>::UpdateOperator(
//             UpdateOperatorEvent {
//                 owner: sender,
//                 operator: param.operator,
//                 update: param.update,
//             },
//         ))?;
//     }
//     Ok(())
// }

/// Parameter type for the CIS-2 function `balanceOf` specialized to the subset
/// of TokenIDs used by this contract.
pub type ContractBalanceOfQueryParams = BalanceOfQueryParams<ContractTokenId>;

/// Response type for the CIS-2 function `balanceOf` specialized to the subset
/// of TokenAmounts used by this contract.
pub type ContractBalanceOfQueryResponse = BalanceOfQueryResponse<ContractTokenAmount>;

/// Get the balance of given token IDs and addresses.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "cis2_multi_sponsored_txs",
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
    contract = "cis2_multi_sponsored_txs",
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

/// Response type for the function `publicKeyOf`.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct PublicKeyOfQueryResponse(
    #[concordium(size_length = 2)] pub Vec<Option<AccountPublicKeys>>,
);

impl From<Vec<Option<AccountPublicKeys>>> for PublicKeyOfQueryResponse {
    fn from(results: concordium_std::Vec<Option<AccountPublicKeys>>) -> Self {
        PublicKeyOfQueryResponse(results)
    }
}

/// The parameter type for the contract functions `publicKeyOf/noneOf`. A query
/// for the public key/nonce of a given account.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct VecOfAccountAddresses {
    /// List of queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<AccountAddress>,
}

/// Get the public keys of accounts. `None` is returned if the account does not
/// exist on chain.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_multi_sponsored_txs",
    name = "publicKeyOf",
    parameter = "VecOfAccountAddresses",
    return_value = "PublicKeyOfQueryResponse",
    error = "ContractError"
)]
fn contract_public_key_of(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<PublicKeyOfQueryResponse> {
    // Parse the parameter.
    let params: VecOfAccountAddresses = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response: Vec<Option<AccountPublicKeys>> = Vec::with_capacity(params.queries.len());
    for account in params.queries {
        // Query the public_key.
        let public_keys = host.account_public_keys(account).ok();

        response.push(public_keys);
    }
    let result = PublicKeyOfQueryResponse::from(response);
    Ok(result)
}

/// Response type for the function `nonceOf`.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct NonceOfQueryResponse(#[concordium(size_length = 2)] pub Vec<u64>);

impl From<Vec<u64>> for NonceOfQueryResponse {
    fn from(results: concordium_std::Vec<u64>) -> Self { NonceOfQueryResponse(results) }
}

/// Get the nonces of accounts.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_multi_sponsored_txs",
    name = "nonceOf",
    parameter = "VecOfAccountAddresses",
    return_value = "NonceOfQueryResponse",
    error = "ContractError"
)]
fn contract_nonce_of(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<NonceOfQueryResponse> {
    // Parse the parameter.
    let params: VecOfAccountAddresses = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response: Vec<u64> = Vec::with_capacity(params.queries.len());
    for account in params.queries {
        // Query the next nonce.
        let nonce = host.state().nonces_registry.get(&account).map(|nonce| *nonce).unwrap_or(0);

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
    contract = "cis2_multi_sponsored_txs",
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
        let metadata_url = match host.state().tokens.get(&token_id) {
            Some(metadata_url) => metadata_url.clone(),
            None => bail!(ContractError::InvalidTokenId),
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
#[receive(contract = "cis2_multi_sponsored_txs", name = "onReceivingCIS2", error = "ContractError")]
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
    contract = "cis2_multi_sponsored_txs",
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

/// Get the entrypoints supported by the `permit` function given a
/// list of entrypoints.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_multi_sponsored_txs",
    name = "supportsPermit",
    parameter = "SupportsPermitQueryParams",
    return_value = "SupportsQueryResponse",
    error = "ContractError"
)]
fn contract_supports_permit(
    ctx: &ReceiveContext,
    _host: &Host<State>,
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
    contract = "cis2_multi_sponsored_txs",
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
