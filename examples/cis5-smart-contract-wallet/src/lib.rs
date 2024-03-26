//! #
use concordium_cis2::*;
use concordium_std::*;

// TODO: look up genesis hash
const GENESIS_HASH: [u8; 32] = [1u8; 32];

/// The standard identifier for the CIS-5: Smart Contract Wallet Standard.
pub const CIS5_STANDARD_IDENTIFIER: StandardIdentifier<'static> =
    StandardIdentifier::new_unchecked("CIS-5");

/// List of supported standards by this contract address.
const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 2] =
    [CIS0_STANDARD_IDENTIFIER, CIS5_STANDARD_IDENTIFIER];

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
    InternalNativeCurrencyTransfer(InternalNativeCurrencyTransferEvent),
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
    pub public_key: PublicKeyEd25519,
    /// The nonce that was used in the `PermitMessage`.
    pub nonce:      u64,
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
        ccd_amount: Amount,
        logger: &mut impl HasLogger,
    ) -> ReceiveResult<()> {
        // A zero transfer does not modify the state.
        if ccd_amount != Amount::zero() {
            {
                let mut from_public_key_native_balance = self
                    .native_balances
                    .entry(from_public_key)
                    .occupied_or(CustomContractError::InvalidPublicKey)?;

                ensure!(
                    *from_public_key_native_balance >= ccd_amount,
                    ContractError::InsufficientFunds.into()
                );
                *from_public_key_native_balance -= ccd_amount;
            }

            let mut to_public_key_native_balance =
                self.native_balances.entry(to_public_key).or_insert_with(Amount::zero);

            // TODO: check if overflow possible
            *to_public_key_native_balance += ccd_amount;
        }

        logger.log(&Event::InternalNativeCurrencyTransfer(
            InternalNativeCurrencyTransferEvent {
                ccd_amount,
                from: from_public_key,
                to: to_public_key,
            },
        ))?;

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
        if token_amount != zero_token_amount {
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

            ensure!(
                *from_cis2_token_balance >= token_amount,
                ContractError::InsufficientFunds.into()
            );
            *from_cis2_token_balance -= token_amount;

            drop(from_cis2_token_balance);

            let mut to_cis2_token_balance =
                token_balances.entry(to_public_key).or_insert_with(|| TokenAmountU256(0u8.into()));

            // CHECK: can overflow happen
            *to_cis2_token_balance += token_amount;
        }

        logger.log(&Event::InternalCis2TokensTransfer(InternalCis2TokensTransferEvent {
            token_amount,
            token_id,
            cis2_token_contract_address,
            from: from_public_key,
            to: to_public_key,
        }))?;

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
    WrongSignature,         // -9
    NonceMismatch,          // -10
    WrongContract,          // -11
    Expired,                // -12
    WrongEntryPoint,        // -13
    UnAuthorized,           // -14
    WrongSigningAmountType, // -15
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
    parameter = "OnReceivingCis2DataParams<ContractTokenId,ContractTokenAmount,PublicKeyEd25519,>",
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

#[derive(Debug, Serialize, Clone, SchemaType)]
pub enum SigningAmount {
    CCDAmount(Amount),
    TokenAmount(TokenAmount),
}

#[derive(Debug, Serialize, Clone, SchemaType)]
pub struct TokenAmount {
    pub token_amount:                ContractTokenAmount,
    /// The ID of the token being transferred.
    pub token_id:                    ContractTokenId,
    ///
    pub cis2_token_contract_address: ContractAddress,
}

/// A single transfer of some amount of a token.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, Clone, SchemaType)]
pub struct InternalTransferBatch {
    /// The address receiving the tokens being transferred.
    pub to:              PublicKeyEd25519,
    /// The amount of tokens being transferred.
    pub transfer_amount: SigningAmount,
}

#[derive(Debug, Serialize, Clone, SchemaType)]
pub struct InternalTransferMessage {
    /// The address owning the tokens being transferred.
    pub entry_point:           OwnedEntrypointName,
    /// The address owning the tokens being transferred.
    pub expiry_time:           Timestamp,
    /// The address owning the tokens being transferred.
    pub nonce:                 u64,
    /// The address owning the tokens being transferred.
    pub service_fee_recipient: PublicKeyEd25519,
    /// The amount of tokens being transferred.
    pub service_fee_amount:    SigningAmount,
    /// List of balance queries.
    #[concordium(size_length = 2)]
    pub simple_transfers:      Vec<InternalTransferBatch>,
}

#[derive(Debug, Serialize, Clone, SchemaType)]
pub struct InternalTransfer {
    /// The address owning the tokens being transferred.
    pub signer:    PublicKeyEd25519,
    /// The address owning the tokens being transferred.
    pub signature: SignatureEd25519,
    ///
    pub message:   InternalTransferMessage,
}

/// The parameter type for the contract function `balanceOfNativeCurrency`.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct InternalTransferParameter {
    /// List of balance queries.
    #[concordium(size_length = 2)]
    pub transfers: Vec<InternalTransfer>,
}

fn calculate_message_hash_from_bytes(
    message_bytes: &[u8],
    crypto_primitives: &impl HasCryptoPrimitives,
    ctx: &ReceiveContext,
) -> ContractResult<[u8; 32]> {
    // We prepend the message with a context string consistent of the genesis_hash
    // and this contract address.
    let mut msg_prepend = [0; 32 + 16];
    msg_prepend[0..32].copy_from_slice(GENESIS_HASH.as_ref());
    msg_prepend[32..40].copy_from_slice(&ctx.self_address().index.to_le_bytes());
    msg_prepend[40..48].copy_from_slice(&ctx.self_address().subindex.to_le_bytes());

    // Calculate the message hash.
    Ok(crypto_primitives.hash_sha2_256(&[&msg_prepend[0..48], &message_bytes].concat()).0)
}

fn validate_signature_and_increase_nonce(
    message: InternalTransferMessage,
    signer: PublicKeyEd25519,
    signature: SignatureEd25519,
    host: &mut Host<State>,
    crypto_primitives: &impl HasCryptoPrimitives,
    ctx: &ReceiveContext,
) -> ContractResult<()> {
    // Check signature is not expired.
    ensure!(message.expiry_time > ctx.metadata().slot_time(), CustomContractError::Expired.into());

    // Calculate the message hash.
    let message_hash =
        calculate_message_hash_from_bytes(&to_bytes(&message), crypto_primitives, ctx)?;

    // Check signature.
    let valid_signature =
        crypto_primitives.verify_ed25519_signature(signer, signature, &message_hash);
    ensure!(valid_signature, CustomContractError::WrongSignature.into());

    // Update the nonce.
    let mut entry = host.state_mut().nonces_registry.entry(signer).or_insert_with(|| 0);

    // Get the current nonce.
    let nonce_state = *entry;
    // Bump nonce.
    *entry += 1;

    // Check the nonce to prevent replay attacks.
    ensure_eq!(message.nonce, nonce_state, CustomContractError::NonceMismatch.into());

    Ok(())
}

///
#[receive(
    contract = "smart_contract_wallet",
    name = "internalTransferNativeCurrency",
    parameter = "InternalTransferParameter",
    error = "CustomContractError",
    crypto_primitives,
    enable_logger,
    mutable
)]
fn internal_transfer_native_currency(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ReceiveResult<()> {
    // Parse the parameter.
    let param: InternalTransferParameter = ctx.parameter_cursor().get()?;

    for internal_transfer in param.transfers {
        let InternalTransfer {
            signer,
            signature,
            message,
        } = internal_transfer.clone();

        let InternalTransferMessage {
            entry_point,
            expiry_time: _,
            nonce,
            service_fee_recipient,
            service_fee_amount,
            simple_transfers,
        } = message.clone();

        ensure_eq!(
            entry_point,
            "internalTransferNativeCurrency",
            CustomContractError::WrongEntryPoint.into()
        );

        let service_fee_ccd_amount = match service_fee_amount {
            SigningAmount::CCDAmount(ccd_amount) => ccd_amount,
            SigningAmount::TokenAmount(_) => {
                bail!(CustomContractError::WrongSigningAmountType.into())
            }
        };

        validate_signature_and_increase_nonce(
            message.clone(),
            signer,
            signature,
            host,
            crypto_primitives,
            ctx,
        )?;

        // Transfer service fee
        host.state_mut().transfer_native_currency(
            signer,
            service_fee_recipient,
            service_fee_ccd_amount,
            logger,
        )?;

        for InternalTransferBatch {
            to,
            transfer_amount,
        } in simple_transfers
        {
            let ccd_amount = match transfer_amount {
                SigningAmount::CCDAmount(ccd_amount) => ccd_amount,
                SigningAmount::TokenAmount(_) => {
                    bail!(CustomContractError::WrongSigningAmountType.into())
                }
            };

            // Update the contract state
            host.state_mut().transfer_native_currency(signer, to, ccd_amount, logger)?;
        }

        logger.log(&Event::Nonce(NonceEvent {
            public_key: signer,
            nonce,
        }))?;
    }

    Ok(())
}

/// Helper function to calculate the `message_hash`.
#[receive(
    contract = "smart_contract_wallet",
    name = "viewInternalTransferMessageHash",
    parameter = "InternalTransferMessage",
    return_value = "[u8;32]",
    error = "ContractError",
    crypto_primitives,
    mutable
)]
fn contract_view_internal_transfer_message_hash(
    ctx: &ReceiveContext,
    _host: &mut Host<State>,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<[u8; 32]> {
    // Parse the parameter.
    let param: InternalTransferMessage = ctx.parameter_cursor().get()?;

    calculate_message_hash_from_bytes(&to_bytes(&param), crypto_primitives, ctx)
}

///
#[receive(
    contract = "smart_contract_wallet",
    name = "internalTransferCis2Tokens",
    parameter = "InternalTransferParameter",
    error = "CustomContractError",
    crypto_primitives,
    enable_logger,
    mutable
)]
fn internal_transfer_cis2_tokens(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ReceiveResult<()> {
    // Parse the parameter.
    let param: InternalTransferParameter = ctx.parameter_cursor().get()?;

    for cis2_tokens_internal_transfer in param.transfers {
        let InternalTransfer {
            signer,
            signature,
            message,
        } = cis2_tokens_internal_transfer.clone();

        let InternalTransferMessage {
            entry_point,
            expiry_time: _,
            nonce,
            service_fee_recipient,
            service_fee_amount,
            simple_transfers,
        } = message.clone();

        ensure_eq!(
            entry_point,
            "internalTransferCis2Tokens",
            CustomContractError::WrongEntryPoint.into()
        );

        let service_fee = match service_fee_amount {
            SigningAmount::CCDAmount(_) => {
                bail!(CustomContractError::WrongSigningAmountType.into())
            }
            SigningAmount::TokenAmount(token_amount) => token_amount,
        };

        validate_signature_and_increase_nonce(
            message.clone(),
            signer,
            signature,
            host,
            crypto_primitives,
            ctx,
        )?;

        // Transfer service fee
        host.state_mut().transfer_cis2_tokens(
            signer,
            service_fee_recipient,
            service_fee.cis2_token_contract_address,
            service_fee.token_id,
            service_fee.token_amount,
            logger,
        )?;

        for InternalTransferBatch {
            to,
            transfer_amount,
        } in simple_transfers
        {
            let transfer = match transfer_amount {
                SigningAmount::CCDAmount(_) => {
                    bail!(CustomContractError::WrongSigningAmountType.into())
                }
                SigningAmount::TokenAmount(token_amount) => token_amount,
            };

            // Update the contract state
            host.state_mut().transfer_cis2_tokens(
                signer,
                to,
                transfer.cis2_token_contract_address,
                transfer.token_id,
                transfer.token_amount,
                logger,
            )?;
        }

        logger.log(&Event::Nonce(NonceEvent {
            public_key: signer,
            nonce,
        }))?;
    }

    Ok(())
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

/// Set the addresses for an implementation given a standard identifier and a
/// list of contract addresses.
///
/// It rejects if:
/// - Sender is not the owner of the contract instance.
/// - It fails to parse the parameter.
#[receive(
    contract = "smart_contract_wallet",
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

/// Get the supported standards or addresses for a implementation given list of
/// standard identifiers.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "smart_contract_wallet",
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
