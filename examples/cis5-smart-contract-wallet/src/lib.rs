//! #
use concordium_cis2::*;
use concordium_std::*;

#[derive(SchemaType, Serialize)]
pub struct VerificationParameter {
    pub public_key: PublicKeyEd25519,
    pub signature:  SignatureEd25519,
    pub message:    Vec<u8>,
}

/// Part of the parameter type for the contract function `permit`.
/// Specifies the message that is signed.
#[derive(SchemaType, Serialize)]
pub struct SigningMessage {
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
    pub message:   SigningMessage,
}

#[derive(Serialize)]
pub struct PermitParamPartial {
    /// Signature/s. The CIS3 standard supports multi-sig accounts.
    pub signature: AccountSignatures,
    /// Account that created the above signature.
    pub signer:    AccountAddress,
}

/// Contract token ID type.
pub type ContractTokenId = TokenIdVec;

/// Contract token amount.
/// Since the tokens are non-fungible the total supply of any token will be at
/// most 1 and it is fine to use a small type for representing token amounts.
pub type ContractTokenAmount = TokenAmountU256;

/// Tagged events to be serialized for the event log.
#[derive(Debug, Serial, Deserial, PartialEq, Eq, SchemaType)]
#[concordium(repr(u8))]
pub enum Event {
    /// The event tracks when a role is revoked from an address.
    #[concordium(tag = 244)]
    InternalCis2TokensTransfer(InternalCis2TokensTransferEvent),
    /// The event tracks when a role is revoked from an address.
    #[concordium(tag = 245)]
    InternalNativeCurrencyTransferEvent(InternalNativeCurrencyTransferEvent),
    /// The event tracks when a role is revoked from an address.
    #[concordium(tag = 246)]
    WithdrawCis2Tokens(WithdrawCis2TokensEvent),
    /// The event tracks when a role is revoked from an address.
    #[concordium(tag = 247)]
    WithdrawNativeCurrency(WithdrawNativeCurrencyEvent),
    /// The event tracks when a role is revoked from an address.
    #[concordium(tag = 248)]
    DepositCis2Tokens(DepositCis2TokensEvent),
    /// The event tracks when a role is revoked from an address.
    #[concordium(tag = 249)]
    DepositNativeCurrency(DepositNativeCurrencyEvent),
    /// Cis3 event.
    /// The event tracks the nonce used by the signer of the `PermitMessage`
    /// whenever the `permit` function is invoked.
    #[concordium(tag = 250)]
    Nonce(NonceEvent),
}

#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct InternalCis2TokensTransferEvent {
    /// Account that signed the `PermitMessage`.
    pub token_amount: ContractTokenAmount,
    /// The nonce that was used in the `PermitMessage`.
    pub token_id: ContractTokenId,
    /// The nonce that was used in the `PermitMessage`.
    pub cis2_token_contract_address: ContractAddress,
    /// The nonce that was used in the `PermitMessage`.
    pub from: PublicKeyEd25519,
    /// The nonce that was used in the `PermitMessage`.
    pub to: PublicKeyEd25519,
}

#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct InternalNativeCurrencyTransferEvent {
    /// Account that signed the `PermitMessage`.
    pub ccd_amount: Amount,
    /// The nonce that was used in the `PermitMessage`.
    pub from:       PublicKeyEd25519,
    /// The nonce that was used in the `PermitMessage`.
    pub to:         PublicKeyEd25519,
}

#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct WithdrawCis2TokensEvent {
    /// Account that signed the `PermitMessage`.
    pub token_amount: ContractTokenAmount,
    /// The nonce that was used in the `PermitMessage`.
    pub token_id: ContractTokenId,
    /// The nonce that was used in the `PermitMessage`.
    pub cis2_token_contract_address: ContractAddress,
    /// The nonce that was used in the `PermitMessage`.
    pub from: PublicKeyEd25519,
    /// The nonce that was used in the `PermitMessage`.
    pub to: Address,
}

#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct WithdrawNativeCurrencyEvent {
    /// Account that signed the `PermitMessage`.
    pub ccd_amount: Amount,
    /// The nonce that was used in the `PermitMessage`.
    pub from:       PublicKeyEd25519,
    /// The nonce that was used in the `PermitMessage`.
    pub to:         Address,
}

#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct DepositCis2TokensEvent {
    /// Account that signed the `PermitMessage`.
    pub token_amount: ContractTokenAmount,
    /// The nonce that was used in the `PermitMessage`.
    pub token_id: ContractTokenId,
    /// The nonce that was used in the `PermitMessage`.
    pub cis2_token_contract_address: ContractAddress,
    /// The nonce that was used in the `PermitMessage`.
    pub from: Address,
    /// The nonce that was used in the `PermitMessage`.
    pub to: PublicKeyEd25519,
}

#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct DepositNativeCurrencyEvent {
    /// Account that signed the `PermitMessage`.
    pub ccd_amount: Amount,
    /// The nonce that was used in the `PermitMessage`.
    pub from:       Address,
    /// The nonce that was used in the `PermitMessage`.
    pub to:         PublicKeyEd25519,
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

/// The state for each address.
#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
#[concordium(transparent)]
struct ContractAddressState<S = StateApi> {
    /// The amount of tokens owned by this address.
    balances: StateMap<ContractTokenId, StateMap<PublicKeyEd25519, ContractTokenAmount, S>, S>,
}

impl ContractAddressState {
    fn empty(state_builder: &mut StateBuilder) -> Self {
        ContractAddressState {
            balances: state_builder.new_map(),
        }
    }
}

/// The contract state,
///
/// Note: The specification does not specify how to structure the contract state
/// and this could be structured in a more space-efficient way.
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S = StateApi> {
    /// The state of addresses.
    token_balances:  StateMap<ContractAddress, ContractAddressState<S>, S>,
    ///
    native_balances: StateMap<PublicKeyEd25519, Amount, S>,
    /// A map with contract addresses providing implementations of additional
    /// standards.
    implementors:    StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
    /// A registry to link an account to its next nonce. The nonce is used to
    /// prevent replay attacks of the signed message. The nonce is increased
    /// sequentially every time a signed message (corresponding to the
    /// account) is successfully executed in the `permit` function. This
    /// mapping keeps track of the next nonce that needs to be used by the
    /// account to generate a signature.
    nonces_registry: StateMap<PublicKeyEd25519, u64, S>,
}

// Functions for creating, updating and querying the contract state.
impl State {
    /// Creates a new state with no tokens.
    fn empty(state_builder: &mut StateBuilder) -> Self {
        State {
            native_balances: state_builder.new_map(),
            token_balances:  state_builder.new_map(),
            implementors:    state_builder.new_map(),
            nonces_registry: state_builder.new_map(),
        }
    }

    /// Get the current balance of a given token ID for a given address.
    /// Results in an error if the token ID does not exist in the state.
    /// Since this contract only contains NFTs, the balance will always be
    /// either 1 or 0.
    fn balance_tokens(
        &self,
        token_id: &ContractTokenId,
        cis2_token_contract_address: &ContractAddress,
        public_key: &PublicKeyEd25519,
    ) -> ContractResult<ContractTokenAmount> {
        let zero_token_amount = TokenAmountU256(0u8.into());

        Ok(self
            .token_balances
            .get(cis2_token_contract_address)
            .map(|a| {
                a.balances
                    .get(token_id)
                    .map(|s| s.get(public_key).map(|s| *s).unwrap_or_else(|| zero_token_amount))
                    .unwrap_or_else(|| zero_token_amount)
            })
            .unwrap_or_else(|| zero_token_amount))
    }

    /// Get the current balance of a given token ID for a given address.
    /// Results in an error if the token ID does not exist in the state.
    /// Since this contract only contains NFTs, the balance will always be
    /// either 1 or 0.
    fn balance_native_currency(&self, public_key: &PublicKeyEd25519) -> ContractResult<Amount> {
        Ok(self.native_balances.get(public_key).map(|s| *s).unwrap_or_else(Amount::zero))
    }

    /// Update the state with a transfer of some token.
    /// Results in an error if the token ID does not exist in the state or if
    /// the from address have insufficient tokens to do the transfer.
    fn transfer_native_currency(
        &mut self,
        from_public_key: PublicKeyEd25519,
        to_public_key: PublicKeyEd25519,
        amount: Amount,
    ) -> ContractResult<()> {
        // A zero transfer does not modify the state.
        if amount == Amount::zero() {
            return Ok(());
        }

        {
            let mut from_public_key_native_balance = self
                .native_balances
                .entry(from_public_key)
                .occupied_or(CustomContractError::InvalidPublicKey)
                .map(|x| *x)?;

            ensure!(from_public_key_native_balance >= amount, ContractError::InsufficientFunds);
            from_public_key_native_balance -= amount;
        }

        let mut to_public_key_native_balance = self
            .native_balances
            .entry(to_public_key)
            .occupied_or(CustomContractError::InvalidPublicKey)
            .map(|x| *x)?;

        to_public_key_native_balance += amount;

        Ok(())
    }

    /// Update the state with a transfer of some token.
    /// Results in an error if the token ID does not exist in the state or if
    /// the from address have insufficient tokens to do the transfer.
    fn transfer_cis2_tokens(
        &mut self,
        from_public_key: PublicKeyEd25519,
        to_public_key: PublicKeyEd25519,
        cis2_token_contract_address: ContractAddress,
        token_id: ContractTokenId,
        token_amount: ContractTokenAmount,
        logger: &mut impl HasLogger,
    ) -> ReceiveResult<()> {
        let zero_token_amount = TokenAmountU256(0u8.into());
        // A zero transfer does not modify the state.
        if token_amount == zero_token_amount {
            return Ok(());
        }

        let mut contract_balances = self
            .token_balances
            .entry(cis2_token_contract_address)
            .occupied_or(CustomContractError::InvalidPublicKey)?;

        let mut token_balances = contract_balances
            .balances
            .entry(token_id.clone())
            .occupied_or(CustomContractError::InvalidContractAddress)?;

        let mut from_cis2_token_balance = token_balances
            .entry(from_public_key)
            .occupied_or(CustomContractError::InsufficientFunds)?;

        ensure!(*from_cis2_token_balance >= token_amount, ContractError::InsufficientFunds.into());
        *from_cis2_token_balance -= token_amount;

        drop(from_cis2_token_balance);

        let mut to_cis2_token_balance =
            token_balances.entry(to_public_key).or_insert_with(|| TokenAmountU256(0u8.into()));

        // CHECK: can overflow happen
        *to_cis2_token_balance += token_amount;

        logger.log(&Event::InternalCis2TokensTransfer(InternalCis2TokensTransferEvent {
            token_amount,
            token_id,
            cis2_token_contract_address,
            from: from_public_key,
            to: to_public_key,
        }))?;

        Ok(())
    }

    // /// Check if state contains any implementors for a given standard.
    // fn have_implementors(&self, std_id: &StandardIdentifierOwned) ->
    // SupportResult {     if let Some(addresses) =
    // self.implementors.get(std_id) {
    //         SupportResult::SupportBy(addresses.to_vec())
    //     } else {
    //         SupportResult::NoSupport
    //     }
    // }

    // /// Set implementors for a given standard.
    // fn set_implementors(
    //     &mut self,
    //     std_id: StandardIdentifierOwned,
    //     implementors: Vec<ContractAddress>,
    // ) {
    //     self.implementors.insert(std_id, implementors);
    // }
}

/// The different errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
pub enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams, // -1
    /// Failed logging: Log is full.
    LogFull, // -2
    /// Failed logging: Log is malformed.
    LogMalformed, // -3
    /// Invalid contract name.
    OnlyContract, // -4
    InvalidPublicKey,       // -5
    InvalidContractAddress, // -6
    InvalidTokenId,         // -7
    InsufficientFunds,      // -8
}

pub type ContractError = Cis2Error<CustomContractError>;

pub type ContractResult<A> = Result<A, ContractError>;

/// Mapping CustomContractError to ContractError
impl From<CustomContractError> for ContractError {
    fn from(c: CustomContractError) -> Self { Cis2Error::Custom(c) }
}

#[init(contract = "smart_contract_wallet", event = "Event", error = "CustomContractError")]
fn contract_init(_ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<State> {
    Ok(State::empty(state_builder))
}

///
#[receive(
    contract = "smart_contract_wallet",
    name = "depositNativeCurrency",
    parameter = "PublicKeyEd25519",
    error = "CustomContractError",
    enable_logger,
    payable,
    mutable
)]
fn deposit_native_currency(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    amount: Amount,
    logger: &mut impl HasLogger,
) -> ReceiveResult<()> {
    let to: PublicKeyEd25519 = ctx.parameter_cursor().get()?;

    let mut public_key_balances =
        host.state_mut().native_balances.entry(to).or_insert_with(Amount::zero);

    *public_key_balances = amount;

    logger.log(&Event::DepositNativeCurrency(DepositNativeCurrencyEvent {
        ccd_amount: amount,
        from: ctx.sender(),
        to,
    }))?;

    Ok(())
}

///
#[receive(
    contract = "smart_contract_wallet",
    name = "depositCis2Tokens",
    parameter = "OnReceivingCis2DataParams<
    ContractTokenId,
    ContractTokenAmount,
    PublicKeyEd25519,
>",
    error = "CustomContractError",
    enable_logger,
    mutable
)]
fn deposit_cis2_tokens(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ReceiveResult<()> {
    let cis2_hook_param: OnReceivingCis2DataParams<
        ContractTokenId,
        ContractTokenAmount,
        PublicKeyEd25519,
    > = ctx.parameter_cursor().get()?;

    // Ensure that only contracts can call this hook function
    let contract_sender_address = match ctx.sender() {
        Address::Contract(contract_sender_address) => contract_sender_address,
        Address::Account(_) => bail!(CustomContractError::OnlyContract.into()),
    };

    let (state, builder) = host.state_and_builder();

    let mut contract_balances = state
        .token_balances
        .entry(contract_sender_address)
        .or_insert_with(|| ContractAddressState::empty(builder));

    let mut contract_token_balances = contract_balances
        .balances
        .entry(cis2_hook_param.token_id.clone())
        .or_insert_with(|| builder.new_map());

    let mut cis2_token_balance = contract_token_balances
        .entry(cis2_hook_param.data)
        .or_insert_with(|| TokenAmountU256(0u8.into()));

    *cis2_token_balance += cis2_hook_param.amount;

    logger.log(&Event::DepositCis2Tokens(DepositCis2TokensEvent {
        token_amount: cis2_hook_param.amount,
        token_id: cis2_hook_param.token_id,
        cis2_token_contract_address: contract_sender_address,
        from: cis2_hook_param.from,
        to: cis2_hook_param.data,
    }))?;

    Ok(())
}

///
#[receive(
    contract = "smart_contract_wallet",
    name = "internalTransferNativeCurrency",
    parameter = "PublicKeyEd25519",
    error = "CustomContractError",
    payable,
    mutable
)]
fn internal_transfer_native_currency(
    _ctx: &ReceiveContext,
    _host: &mut Host<State>,
    _amount: Amount,
) -> ReceiveResult<()> {
    // TODO: this needs to be authorized by the singer instead.
    // Authenticate the sender for this transfer
    // Get the sender who invoked this contract function.
    // let sender = ctx.sender();
    // ensure!(from == sender || state.is_operator(&sender, &from),
    // ContractError::Unauthorized);

    // let beneficiary: PublicKeyEd25519 = ctx.parameter_cursor().get()?;

    // let (state, builder) = host.state_and_builder();

    // let mut public_key_balances =
    //     state.balances.entry(beneficiary).or_insert_with(||
    // PublicKeyState::empty(builder));

    // public_key_balances.native_balance = amount;

    Ok(())
}

/// A single transfer of some amount of a token.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, Clone, SchemaType)]
pub struct Cis2TokensInternalTransferBatch {
    /// The address owning the tokens being transferred.
    pub from: PublicKeyEd25519,
    /// The address receiving the tokens being transferred.
    pub to: PublicKeyEd25519,
    /// The amount of tokens being transferred.
    pub token_amount: ContractTokenAmount,
    /// The ID of the token being transferred.
    pub token_id: ContractTokenId,
    ///
    pub cis2_token_contract_address: ContractAddress,
}

#[derive(Debug, Serialize, Clone, SchemaType)]
pub struct Cis2TokensInternalTransfer {
    /// The address owning the tokens being transferred.
    pub signer: PublicKeyEd25519,
    /// The address owning the tokens being transferred.
    pub signature: SignatureEd25519,
    /// The address owning the tokens being transferred.
    pub expiry_time: Timestamp,
    /// The address owning the tokens being transferred.
    pub nonce: u64,
    /// The address owning the tokens being transferred.
    pub service_fee: ContractTokenAmount,
    /// The address owning the tokens being transferred.
    pub service_fee_recipient: PublicKeyEd25519,
    /// The amount of tokens being transferred.
    pub service_fee_token_amount: ContractTokenAmount,
    /// The ID of the token being transferred.
    pub service_fee_token_id: ContractTokenId,
    ///
    pub service_fee_cis2_token_contract_address: ContractAddress,
    /// List of balance queries.
    #[concordium(size_length = 2)]
    pub simple_transfers: Vec<Cis2TokensInternalTransferBatch>,
}

/// The parameter type for the contract function `balanceOfNativeCurrency`.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct Cis2TokensInternalTransferParameter {
    /// List of balance queries.
    #[concordium(size_length = 2)]
    pub transfers: Vec<Cis2TokensInternalTransfer>,
}

///
#[receive(
    contract = "smart_contract_wallet",
    name = "internalTransferCis2Tokens",
    parameter = "Cis2TokensInternalTransferParameter",
    error = "CustomContractError",
    enable_logger,
    mutable
)]
fn internal_transfer_cis2_tokens(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ReceiveResult<()> {
    // Parse the parameter.
    let param: Cis2TokensInternalTransferParameter = ctx.parameter_cursor().get()?;

    for Cis2TokensInternalTransfer {
        signer,
        signature: _signature,
        expiry_time: _expiry_time,
        nonce: _nonce,
        service_fee: _service_fee,
        service_fee_recipient,
        service_fee_token_amount,
        service_fee_token_id,
        service_fee_cis2_token_contract_address,
        simple_transfers,
    } in param.transfers
    {
        // TODO: this needs to be authorized by the singer instead.
        // Authenticate the sender for this transfer
        // Get the sender who invoked this contract function.
        // let sender = ctx.sender();
        // ensure!(from == sender || state.is_operator(&sender, &from),
        // ContractError::Unauthorized);

        // TODO: Check signature and other parameters

        // Transfer service fee
        host.state_mut().transfer_cis2_tokens(
            signer,
            service_fee_recipient,
            service_fee_cis2_token_contract_address,
            service_fee_token_id.clone(),
            service_fee_token_amount,
            logger,
        )?;

        for Cis2TokensInternalTransferBatch {
            from,
            to,
            token_amount,
            token_id,
            cis2_token_contract_address,
        } in simple_transfers
        {
            // Update the contract state
            host.state_mut().transfer_cis2_tokens(
                from,
                to,
                cis2_token_contract_address,
                token_id.clone(),
                token_amount,
                logger,
            )?;
        }
    }

    Ok(())
}

/// A query for the balance of a given address for a given token.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct NativeCurrencyBalanceOfQuery {
    /// The public key for which to query the balance of.
    pub public_key: PublicKeyEd25519,
}

/// The parameter type for the contract function `balanceOfNativeCurrency`.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct NativeCurrencyBalanceOfParameter {
    /// List of balance queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<NativeCurrencyBalanceOfQuery>,
}

/// The response which is sent back when calling the contract function
/// `balanceOfNativeCurrency`.
/// It consists of the list of results corresponding to the list of queries.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
#[concordium(transparent)]
pub struct NativeCurrencyBalanceOfResponse(#[concordium(size_length = 2)] pub Vec<Amount>);

impl From<Vec<Amount>> for NativeCurrencyBalanceOfResponse {
    fn from(results: Vec<Amount>) -> Self { NativeCurrencyBalanceOfResponse(results) }
}

/// Get the balance of given token IDs and addresses.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "smart_contract_wallet",
    name = "balanceOfNativeCurrency",
    parameter = "NativeCurrencyBalanceOfParameter",
    return_value = "NativeCurrencyBalanceOfResponse",
    error = "CustomContractError"
)]
fn contract_balance_of_native_currency(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<NativeCurrencyBalanceOfResponse> {
    // Parse the parameter.
    let params: NativeCurrencyBalanceOfParameter = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for balance.
        let amount = host.state().balance_native_currency(&query.public_key)?;
        response.push(amount);
    }
    let result = NativeCurrencyBalanceOfResponse::from(response);
    Ok(result)
}

/// A query for the balance of a given address for a given token.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct Cis2TokensBalanceOfQuery {
    /// The ID of the token for which to query the balance of.
    pub token_id:                    ContractTokenId,
    ///
    pub cis2_token_contract_address: ContractAddress,
    /// The public key for which to query the balance of.
    pub public_key:                  PublicKeyEd25519,
}

/// The parameter type for the contract function `balanceOf`.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct Cis2TokensBalanceOfParameter {
    /// List of balance queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<Cis2TokensBalanceOfQuery>,
}

/// The response which is sent back when calling the contract function
/// `balanceOf`.
/// It consists of the list of results corresponding to the list of queries.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
#[concordium(transparent)]
pub struct Cis2TokensBalanceOfResponse(#[concordium(size_length = 2)] pub Vec<ContractTokenAmount>);

impl From<Vec<ContractTokenAmount>> for Cis2TokensBalanceOfResponse {
    fn from(results: Vec<ContractTokenAmount>) -> Self { Cis2TokensBalanceOfResponse(results) }
}

/// Get the balance of given token IDs and addresses.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "smart_contract_wallet",
    name = "balanceOfCis2Tokens",
    parameter = "Cis2TokensBalanceOfParameter",
    return_value = "Cis2TokensBalanceOfResponse",
    error = "CustomContractError"
)]
fn contract_balance_of_cis2_tokens(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<Cis2TokensBalanceOfResponse> {
    // Parse the parameter.
    let params: Cis2TokensBalanceOfParameter = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for balance.
        let amount = host.state().balance_tokens(
            &query.token_id,
            &query.cis2_token_contract_address,
            &query.public_key,
        )?;
        response.push(amount);
    }
    let result = Cis2TokensBalanceOfResponse::from(response);
    Ok(result)
}
