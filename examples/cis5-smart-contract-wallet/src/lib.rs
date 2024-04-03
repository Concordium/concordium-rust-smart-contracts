//! A smart contract wallet.
//!
//! This contract implements the CIS-5 (Concordium standard interface 5) that
//! defines a smart contract wallet that can hold and transfer native currency
//! and CIS-2 tokens. https://proposals.concordium.software/CIS/cis-5.html
//!
//! Native currency/CIS-2 tokens can be deposited into the smart contract wallet
//! by specifying to which public key (PublicKeyEd25519 schema) the deposit
//! should be assigned. Authorization for token and currency transfers from the
//! smart contract's assigned public key balance is exclusively granted to the
//! holder of the corresponding private key, ensuring self-custodial control
//! over the assets.
//!
//! Transfers of native currency and CIS-2 token balances do not require
//! on-chain transaction submissions. Instead, the holder of the corresponding
//! private key can generate a valid signature and identify a third party to
//! submit the transaction on-chain, potentially incentivizing the third-party
//! involvement through a service fees. The `withdraw` and `internalTransfer`
//! functions transfer (authorized as part of the message that was signed) the
//! amount of service fee to the service fee recipient's public key.
//!
//! Any withdrawal (native currency or CIS-2 tokens) to a smart contract will
//! invoke a `receiveHook` function on that smart contract.
//!
//! The three main actions in the smart contract wallet that can be taken are:
//! - *deposit*: assigns the balance to a public key within the smart contract
//!   wallet.
//! - *internal transfer*: assigns the balance to a new public key within the
//!   smart contract wallet.
//! - *withdraw*: withdraws the balance out of the smart contract wallet to a
//!   native account or smart contract.
//!
//! The goal of this standard is to simplify the account creation onboarding
//! flow on Concordium. Users can hold/transfer native currency/CIS-2 tokens
//! without a valid account as a starting point (no KYC required). Once users
//! are ready to go through the KYC process to create a valid account on
//! Concordium, they can withdraw assets out of the smart contract wallet.
use concordium_cis2::*;
use concordium_std::*;

// The testnet genesis hash is:
// 0x4221332d34e1694168c2a0c0b3fd0f273809612cb13d000d5c2e00e85f50f796
const TESTNET_GENESIS_HASH: [u8; 32] = [
    66, 33, 51, 45, 52, 225, 105, 65, 104, 194, 160, 192, 179, 253, 15, 39, 56, 9, 97, 44, 177, 61,
    0, 13, 92, 46, 0, 232, 95, 80, 247, 150,
];

/// The standard identifier for the CIS-5: Smart Contract Wallet Standard.
pub const CIS5_STANDARD_IDENTIFIER: StandardIdentifier<'static> =
    StandardIdentifier::new_unchecked("CIS-5");

/// List of supported standards by this contract address.
const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 2] =
    [CIS0_STANDARD_IDENTIFIER, CIS5_STANDARD_IDENTIFIER];

/// Contract token ID type.
pub type ContractTokenId = TokenIdVec;

/// Contract token amount.
/// Since the wallet should be able to hold the balance of any CIS-2 token
/// contract, we use the largest TokenAmount.
pub type ContractTokenAmount = TokenAmountU256;

/// Tagged events to be serialized for the event log.
#[derive(Debug, Serial, Deserial, PartialEq, Eq, SchemaType)]
#[concordium(repr(u8))]
pub enum Event {
    /// The event tracks the nonce used in the message that was signed.
    #[concordium(tag = 250)]
    Nonce(NonceEvent),
    /// The event tracks ever time a CCD amount received by the contract is
    /// assigned to a public key.
    #[concordium(tag = 249)]
    DepositNativeCurrency(DepositNativeCurrencyEvent),
    /// The event tracks ever time a token amount received by the contract is
    /// assigned to a public key.
    #[concordium(tag = 248)]
    DepositCis2Tokens(DepositCis2TokensEvent),
    /// The event tracks ever time a CCD amount held by a public key is
    /// withdrawn to an address.
    #[concordium(tag = 247)]
    WithdrawNativeCurrency(WithdrawNativeCurrencyEvent),
    /// The event tracks ever time a token amount held by a public key is
    /// withdrawn to an address.
    #[concordium(tag = 246)]
    WithdrawCis2Tokens(WithdrawCis2TokensEvent),
    /// The event tracks ever time a CCD amount held by a public key is
    /// transferred to another public key within the contract.
    #[concordium(tag = 245)]
    InternalNativeCurrencyTransfer(InternalNativeCurrencyTransferEvent),
    /// The event tracks ever time a token amount held by a public key is
    /// transferred to another public key within the contract.
    #[concordium(tag = 244)]
    InternalCis2TokensTransfer(InternalCis2TokensTransferEvent),
}

/// The `NonceEvent` is logged whenever a signature is checked. The event
/// tracks the nonce used by the signer of the message.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct NonceEvent {
    /// Account that signed the message.
    pub public_key: PublicKeyEd25519,
    /// The nonce that was used in the message.
    pub nonce:      u64,
}

/// The `DepositNativeCurrencyEvent` is logged whenever a CCD amount received by
/// the contract is assigned to a public key.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct DepositNativeCurrencyEvent {
    /// The CCD amount assigned to a public key.
    pub ccd_amount: Amount,
    /// The address that invoked the deposit entrypoint.
    pub from:       Address,
    /// The public key that the CCD amount is assigned to.
    pub to:         PublicKeyEd25519,
}

/// The `DepositCis2TokensEvent` is logged whenever a token amount received by
/// the contract is assigned to a public key.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct DepositCis2TokensEvent {
    /// The token amount assigned to a public key.
    pub token_amount: ContractTokenAmount,
    /// The token id of the token deposit.
    pub token_id: ContractTokenId,
    /// The token contract address of the token deposit.
    pub cis2_token_contract_address: ContractAddress,
    /// The address that invoked the deposit entrypoint.
    pub from: Address,
    /// The public key that the CCD amount is assigned to.
    pub to: PublicKeyEd25519,
}

/// The `WithdrawNativeCurrencyEvent` is logged whenever a CCD amount held by a
/// public key is withdrawn to an address.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct WithdrawNativeCurrencyEvent {
    /// The CCD amount withdrawn.
    pub ccd_amount: Amount,
    /// The public key that the CCD amount will be withdrawn from.
    pub from:       PublicKeyEd25519,
    /// The address that the CCD amount is withdrawn to.
    pub to:         Address,
}

/// The `WithdrawCis2TokensEvent` is logged whenever a token amount held by a
/// public key is withdrawn to an address.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct WithdrawCis2TokensEvent {
    /// The token amount withdrawn.
    pub token_amount: ContractTokenAmount,
    /// The token id of the token withdrawn.
    pub token_id: ContractTokenId,
    /// The token contract address of the token withdrawn.
    pub cis2_token_contract_address: ContractAddress,
    /// The public key that the token amount will be withdrawn from.
    pub from: PublicKeyEd25519,
    /// The address that the token amount is withdrawn to.
    pub to: Address,
}

/// The `InternalNativeCurrencyTransferEvent` is logged whenever a CCD amount
/// held by a public key is transferred to another public key within the
/// contract.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct InternalNativeCurrencyTransferEvent {
    /// The CCD amount transferred.
    pub ccd_amount: Amount,
    /// The public key that the CCD amount will be transferred from.
    pub from:       PublicKeyEd25519,
    /// The public key that the CCD amount is transferred to.
    pub to:         PublicKeyEd25519,
}

/// The `InternalCis2TokensTransferEvent` is logged whenever a token amount held
/// by a public key is transferred to another public key within the contract.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct InternalCis2TokensTransferEvent {
    /// The token amount transferred.
    pub token_amount: ContractTokenAmount,
    /// The token id of the token transferred.
    pub token_id: ContractTokenId,
    /// The token contract address of the token transferred.
    pub cis2_token_contract_address: ContractAddress,
    /// The public key that the token amount will be transferred from.
    pub from: PublicKeyEd25519,
    /// The public key that the token amount is transferred to.
    pub to: PublicKeyEd25519,
}

/// The token balances stored in the state for each token id.
#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
#[concordium(transparent)]
struct ContractAddressState<S = StateApi> {
    /// The amount of tokens owned by public keys mapped for each token id.
    balances: StateMap<ContractTokenId, StateMap<PublicKeyEd25519, ContractTokenAmount, S>, S>,
}

// Implementation of the `ContractAddressState`.
impl ContractAddressState {
    // Creates an new `ContractAddressState` with emtpy balances.
    fn empty(state_builder: &mut StateBuilder) -> Self {
        ContractAddressState {
            balances: state_builder.new_map(),
        }
    }
}

/// The contract state.
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S = StateApi> {
    /// The token balances stored in the state.
    token_balances:  StateMap<ContractAddress, ContractAddressState<S>, S>,
    /// The CCD balances stored in the state.
    native_balances: StateMap<PublicKeyEd25519, Amount, S>,
    /// A map with contract addresses providing implementations of additional
    /// standards.
    implementors:    StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
    /// A registry to link a public key to its next nonce. The nonce is used to
    /// prevent replay attacks of the signed message. The nonce is increased
    /// sequentially every time a signed message (corresponding to the
    /// public key) is successfully executed. This
    /// mapping keeps track of the next nonce that needs to be used by the
    /// public key to generate a signature.
    nonces_registry: StateMap<PublicKeyEd25519, u64, S>,
}

// Functions for creating, updating and querying the contract state.
impl State {
    /// Creates a new state with emtpy balances.
    fn empty(state_builder: &mut StateBuilder) -> Self {
        State {
            native_balances: state_builder.new_map(),
            token_balances:  state_builder.new_map(),
            implementors:    state_builder.new_map(),
            nonces_registry: state_builder.new_map(),
        }
    }

    /// Gets the current native currency balance of a given public key.
    /// Returns a balance of 0 if the public key does not exist in the state.
    fn balance_native_currency(&self, public_key: &PublicKeyEd25519) -> Amount {
        self.native_balances.get(public_key).map(|s| *s).unwrap_or_else(Amount::zero)
    }

    /// Gets the current balance of a given token ID, a given token contract,
    /// and a given public key. Returns a balance of 0 if the token
    /// contract, token id or public key does not exist in the state.
    fn balance_tokens(
        &self,
        token_id: &ContractTokenId,
        cis2_token_contract_address: &ContractAddress,
        public_key: &PublicKeyEd25519,
    ) -> ContractTokenAmount {
        self.token_balances
            .get(cis2_token_contract_address)
            .map(|a| {
                a.balances
                    .get(token_id)
                    .map(|b| {
                        b.get(public_key).map(|c| *c).unwrap_or_else(|| TokenAmountU256(0.into()))
                    })
                    .unwrap_or_else(|| TokenAmountU256(0.into()))
            })
            .unwrap_or_else(|| TokenAmountU256(0.into()))
    }

    /// Updates the state with a transfer of CCD amount and logs an
    /// `InternalNativeCurrencyTransfer` event. Results in an error if the
    /// from public key has insufficient balance to do the transfer.
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
                    .occupied_or(CustomContractError::InsufficientFunds)?;

                ensure!(
                    *from_public_key_native_balance >= ccd_amount,
                    CustomContractError::InsufficientFunds.into()
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

    /// Updates the state with a transfer of some tokens and logs an
    /// `InternalCis2TokensTransfer` event. Results in an error if the token
    /// contract, or the token id does not exist in the state or the from public
    /// key has insufficient balance to do the transfer.
    fn transfer_cis2_tokens(
        &mut self,
        from_public_key: PublicKeyEd25519,
        to_public_key: PublicKeyEd25519,
        cis2_token_contract_address: ContractAddress,
        token_id: ContractTokenId,
        token_amount: ContractTokenAmount,
        logger: &mut impl HasLogger,
    ) -> ReceiveResult<()> {
        // A zero transfer does not modify the state.
        if token_amount != TokenAmountU256(0.into()) {
            let mut contract_balances = self
                .token_balances
                .entry(cis2_token_contract_address)
                .occupied_or(CustomContractError::InsufficientFunds)?;

            let mut token_balances = contract_balances
                .balances
                .entry(token_id.clone())
                .occupied_or(CustomContractError::InsufficientFunds)?;

            let mut from_cis2_token_balance = token_balances
                .entry(from_public_key)
                .occupied_or(CustomContractError::InsufficientFunds)?;

            ensure!(
                *from_cis2_token_balance >= token_amount,
                CustomContractError::InsufficientFunds.into()
            );
            *from_cis2_token_balance -= token_amount;

            drop(from_cis2_token_balance);

            let mut to_cis2_token_balance =
                token_balances.entry(to_public_key).or_insert_with(|| TokenAmountU256(0.into()));

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

    /// Checks if the state contains any implementors for a given standard.
    fn have_implementors(&self, std_id: &StandardIdentifierOwned) -> SupportResult {
        if let Some(addresses) = self.implementors.get(std_id) {
            SupportResult::SupportBy(addresses.to_vec())
        } else {
            SupportResult::NoSupport
        }
    }

    /// Sets implementors for a given standard.
    fn set_implementors(
        &mut self,
        std_id: StandardIdentifierOwned,
        implementors: Vec<ContractAddress>,
    ) {
        let _ = self.implementors.insert(std_id, implementors);
    }
}

/// The different errors the contract can produce.
#[derive(Serialize, PartialEq, Eq, Reject, SchemaType)]
pub enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams, // -1
    /// Failed logging: Log is full.
    LogFull, // -2
    /// Failed logging: Log is malformed.
    LogMalformed, // -3
    /// Failed because an account cannot call the entry point.
    OnlyContract, // -4
    /// Failed because the public key has an insufficient balance.
    InsufficientFunds, // -5
    /// Failed because the signature is invalid.
    WrongSignature, // -6
    /// Failed because the nonce is wrong in the message.
    NonceMismatch, // -7
    /// Failed because the signature is expired.
    Expired, // -8
    /// Failed because the message was intended for a different entry point.
    WrongEntryPoint, // -9
    /// Failed because the sender is unauthorized to invoke the entry point.
    UnAuthorized, // -10
    /// Failed because the signed amount type is wrong.
    WrongAmountType, // -11
}

/// ContractResult type.
pub type ContractResult<A> = Result<A, CustomContractError>;

// Contract functions

/// Initializes the contract instance with no balances.
#[init(contract = "smart_contract_wallet", event = "Event", error = "CustomContractError")]
fn contract_init(_ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<State> {
    Ok(State::empty(state_builder))
}

/// The function is payable and deposits/assigns the send CCD amount
/// (native currency) to a public key.
/// Logs a `DepositNativeCurrency` event.
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

    let mut public_key_balance =
        host.state_mut().native_balances.entry(to).or_insert_with(Amount::zero);

    // CHECK: overflow can happen
    *public_key_balance += amount;

    logger.log(&Event::DepositNativeCurrency(DepositNativeCurrencyEvent {
        ccd_amount: amount,
        from: ctx.sender(),
        to,
    }))?;

    Ok(())
}

/// The function should be called through the receive hook mechanism of a CIS-2
/// token contract. The function deposits/assigns the sent CIS-2 tokens to a
/// public key. Logs a `DepositCis2Tokens` event.
/// It rejects if:
/// - the sender is not a contract.
#[receive(
    contract = "smart_contract_wallet",
    name = "depositCis2Tokens",
    parameter = "OnReceivingCis2DataParams<ContractTokenId,ContractTokenAmount,PublicKeyEd25519>",
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

    // Ensures that only contracts can call this hook function.
    let sender_contract_address = match ctx.sender() {
        Address::Contract(sender_contract_address) => sender_contract_address,
        Address::Account(_) => bail!(CustomContractError::OnlyContract.into()),
    };

    let (state, builder) = host.state_and_builder();

    let mut contract_balances = state
        .token_balances
        .entry(sender_contract_address)
        .or_insert_with(|| ContractAddressState::empty(builder));

    let mut contract_token_balances = contract_balances
        .balances
        .entry(cis2_hook_param.token_id.clone())
        .or_insert_with(|| builder.new_map());

    let mut cis2_token_balance = contract_token_balances
        .entry(cis2_hook_param.data)
        .or_insert_with(|| TokenAmountU256(0.into()));

    // CHECK: overflow can happen
    *cis2_token_balance += cis2_hook_param.amount;

    logger.log(&Event::DepositCis2Tokens(DepositCis2TokensEvent {
        token_amount: cis2_hook_param.amount,
        token_id: cis2_hook_param.token_id,
        cis2_token_contract_address: sender_contract_address,
        from: cis2_hook_param.from,
        to: cis2_hook_param.data,
    }))?;

    Ok(())
}

/// The native currency or CIS-2 token amount signed in the message.
#[derive(Serialize, Clone, SchemaType)]
pub enum SigningAmount {
    /// The CCD amount signed in the message.
    CCDAmount(Amount),
    /// The token amount signed in the message.
    TokenAmount(TokenAmount),
}

/// The token amount signed in the message.
#[derive(Serialize, Clone, SchemaType)]
pub struct TokenAmount {
    /// The token amount signed in the message.
    pub token_amount:                ContractTokenAmount,
    /// The token id of the token signed in the message.
    pub token_id:                    ContractTokenId,
    /// The token contract of the token signed in the message.
    pub cis2_token_contract_address: ContractAddress,
}

/// A single withdrawal of native currency or some amount of tokens.
#[derive(Serialize, Clone, SchemaType)]
pub struct Withdraw {
    /// The address receiving the native currency or tokens being withdrawn.
    pub to:              Receiver,
    /// The amount being withdrawn.
    pub withdraw_amount: SigningAmount,
    /// Some additional data for the receive hook function.
    pub data:            AdditionalData,
}

/// The withdraw message that is signed by the signer.
#[derive(Serialize, Clone, SchemaType)]
pub struct WithdrawMessage {
    /// The entry_point that the signature is intended for.
    pub entry_point:           OwnedEntrypointName,
    /// A timestamp to make the signatures expire.
    pub expiry_time:           Timestamp,
    /// A nonce to prevent replay attacks.
    pub nonce:                 u64,
    /// The recipient public key of the service fee.
    pub service_fee_recipient: PublicKeyEd25519,
    /// The amount of native currency or tokens to be received as a service fee.
    pub service_fee_amount:    SigningAmount,
    /// List of withdrawals.
    #[concordium(size_length = 2)]
    pub simple_withdraws:      Vec<Withdraw>,
}

/// A batch of withdrawals signed by a signer.
#[derive(Serialize, SchemaType)]
pub struct WithdrawBatch {
    /// The signer public key.
    pub signer:    PublicKeyEd25519,
    /// The signature.
    pub signature: SignatureEd25519,
    /// The message being signed.
    pub message:   WithdrawMessage,
}

/// The parameter type for the contract functions
/// `withdrawNativeCurrency/withdrawCis2Tokens`.
#[derive(Serialize, SchemaType)]
#[concordium(transparent)]
pub struct WithdrawParameter {
    /// List of withdraw batches.
    #[concordium(size_length = 2)]
    pub withdraws: Vec<WithdrawBatch>,
}

/// The `TransferParameter` type for the `transfer` function in the CIS-2 token
/// contract.
type TransferParameter = TransferParams<ContractTokenId, ContractTokenAmount>;

/// Calculates the message hash from the message bytes.
/// It prepends the message bytes with a context string consisting of the
/// `genesis_hash` and this contract address.
fn calculate_message_hash_from_bytes(
    message_bytes: &[u8],
    crypto_primitives: &impl HasCryptoPrimitives,
    ctx: &ReceiveContext,
) -> ContractResult<[u8; 32]> {
    // We prepend the message with a context string consistent of the genesis_hash
    // and this contract address.
    let mut msg_prepend = [0; 32 + 16];
    msg_prepend[0..32].copy_from_slice(TESTNET_GENESIS_HASH.as_ref());
    msg_prepend[32..40].copy_from_slice(&ctx.self_address().index.to_le_bytes());
    msg_prepend[40..48].copy_from_slice(&ctx.self_address().subindex.to_le_bytes());

    // Calculate the message hash.
    Ok(crypto_primitives.hash_sha2_256(&[&msg_prepend[0..48], &message_bytes].concat()).0)
}

/// Validates the withdraw message signature and increases the public key nonce.
///
/// It rejects if:
/// - the message is expired.
/// - the signature is invalid.
/// - the nonce is wrong.
fn validate_signature_and_increase_nonce_withdraw_message(
    message: WithdrawMessage,
    signer: PublicKeyEd25519,
    signature: SignatureEd25519,
    host: &mut Host<State>,
    crypto_primitives: &impl HasCryptoPrimitives,
    ctx: &ReceiveContext,
) -> ContractResult<()> {
    // Check that the signature is not expired.
    ensure!(message.expiry_time > ctx.metadata().slot_time(), CustomContractError::Expired);

    // Calculate the message hash.
    let message_hash: [u8; 32] =
        calculate_message_hash_from_bytes(&to_bytes(&message), crypto_primitives, ctx)?;

    // Check the signature.
    let valid_signature =
        crypto_primitives.verify_ed25519_signature(signer, signature, &message_hash);
    ensure!(valid_signature, CustomContractError::WrongSignature);

    // Get the nonce.
    let mut entry = host.state_mut().nonces_registry.entry(signer).or_insert_with(|| 0);

    // Check the nonce to prevent replay attacks.
    ensure_eq!(message.nonce, *entry, CustomContractError::NonceMismatch);

    // Bump the nonce.
    *entry += 1;

    Ok(())
}

/// Helper function to calculate the `WithdrawMessageHash`.
#[receive(
    contract = "smart_contract_wallet",
    name = "viewWithdrawMessageHash",
    parameter = "WithdrawMessage",
    return_value = "[u8;32]",
    error = "CustomContractError",
    crypto_primitives,
    mutable
)]
fn contract_view_withdraw_message_hash(
    ctx: &ReceiveContext,
    _host: &mut Host<State>,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<[u8; 32]> {
    // Parse the parameter.
    let param: WithdrawMessage = ctx.parameter_cursor().get()?;

    calculate_message_hash_from_bytes(&to_bytes(&param), crypto_primitives, ctx)
}

/// The function executes a list of CCDs (native currency) withdrawals
/// to native accounts and/or smart contracts.
/// When withdrawing CCD to a contract address, a CCD receive hook function is
/// triggered.
///
/// The function logs `WithdrawNativeCurrency`, `InternalNativeCurrencyTransfer`
/// and `Nonce` events.
///
/// It rejects if:
/// - it fails to parse the parameter.
/// - the message was intended for a different entry point.
/// - the `AmountType` is not CCD for the service fee transfer or for any
///   withdrawal.
/// - the message is expired.
/// - the signature is invalid.
/// - the nonce is wrong.
/// - the `signer` has an insufficient balance.
/// - the CCD receive hook function reverts for any withdrawal.
#[receive(
    contract = "smart_contract_wallet",
    name = "withdrawNativeCurrency",
    parameter = "WithdrawParameter",
    error = "CustomContractError",
    crypto_primitives,
    enable_logger,
    mutable
)]
fn withdraw_native_currency(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ReceiveResult<()> {
    // Parse the parameter.
    let param: WithdrawParameter = ctx.parameter_cursor().get()?;

    for withdraw_batch in param.withdraws {
        let WithdrawBatch {
            signer,
            signature,
            message,
        } = withdraw_batch;

        let WithdrawMessage {
            entry_point,
            expiry_time: _,
            nonce,
            service_fee_recipient,
            service_fee_amount,
            simple_withdraws,
        } = message.clone();

        ensure_eq!(
            entry_point,
            "withdrawNativeCurrency",
            CustomContractError::WrongEntryPoint.into()
        );

        let service_fee_ccd_amount = match service_fee_amount {
            SigningAmount::CCDAmount(ccd_amount) => ccd_amount,
            SigningAmount::TokenAmount(_) => {
                bail!(CustomContractError::WrongAmountType.into())
            }
        };

        validate_signature_and_increase_nonce_withdraw_message(
            message,
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

        for Withdraw {
            to,
            withdraw_amount,
            data,
        } in simple_withdraws
        {
            let ccd_amount = match withdraw_amount {
                SigningAmount::CCDAmount(ccd_amount) => ccd_amount,
                SigningAmount::TokenAmount(_) => {
                    bail!(CustomContractError::WrongAmountType.into())
                }
            };

            // Update the contract state
            {
                let mut from_public_key_native_balance = host
                    .state_mut()
                    .native_balances
                    .entry(signer)
                    .occupied_or(CustomContractError::InsufficientFunds)?;

                ensure!(
                    *from_public_key_native_balance >= ccd_amount,
                    CustomContractError::InsufficientFunds.into()
                );
                *from_public_key_native_balance -= ccd_amount;
            }

            // Withdraw CCD out of the contract.
            let to_address = match to {
                Receiver::Account(account_address) => {
                    host.invoke_transfer(&account_address, ccd_amount)?;
                    Address::Account(account_address)
                }
                Receiver::Contract(contract_address, function) => {
                    // If the receiver is a contract: invoke the receive hook function.
                    host.invoke_contract(
                        &contract_address,
                        &data,
                        function.as_entrypoint_name(),
                        ccd_amount,
                    )?;
                    Address::Contract(contract_address)
                }
            };

            logger.log(&Event::WithdrawNativeCurrency(WithdrawNativeCurrencyEvent {
                ccd_amount,
                from: signer,
                to: to_address,
            }))?;
        }

        logger.log(&Event::Nonce(NonceEvent {
            public_key: signer,
            nonce,
        }))?;
    }

    Ok(())
}

/// The function executes a list of token withdrawals to native accounts and/or
/// smart contracts. This function calls the `transfer` function on the CIS-2
/// token contract for every withdrawal.
///
/// The function logs `WithdrawCis2Tokens`, `InternalCis2TokensTransfer`
/// and `Nonce` events.
///
/// It rejects if:
/// - it fails to parse the parameter.
/// - the message was intended for a different entry point.
/// - the `AmountType` is not a CIS-2 token for the service fee transfer or for
///   any withdrawal.
/// - the message is expired.
/// - the signature is invalid.
/// - the nonce is wrong.
/// - the `signer` has an insufficient balance.
/// - the `transfer` function on the CIS-2 contract reverts for any withdrawal.
#[receive(
    contract = "smart_contract_wallet",
    name = "withdrawCis2Tokens",
    parameter = "WithdrawParameter",
    error = "CustomContractError",
    crypto_primitives,
    enable_logger,
    mutable
)]
fn withdraw_cis2_tokens(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ReceiveResult<()> {
    // Parse the parameter.
    let param: WithdrawParameter = ctx.parameter_cursor().get()?;

    for withdraw_batch in param.withdraws {
        let WithdrawBatch {
            signer,
            signature,
            message,
        } = withdraw_batch;

        let WithdrawMessage {
            entry_point,
            expiry_time: _,
            nonce,
            service_fee_recipient,
            service_fee_amount,
            simple_withdraws,
        } = message.clone();

        ensure_eq!(entry_point, "withdrawCis2Tokens", CustomContractError::WrongEntryPoint.into());

        let service_fee = match service_fee_amount {
            SigningAmount::CCDAmount(_) => {
                bail!(CustomContractError::WrongAmountType.into())
            }
            SigningAmount::TokenAmount(ref token_amount) => token_amount,
        };

        validate_signature_and_increase_nonce_withdraw_message(
            message,
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
            service_fee.token_id.clone(),
            service_fee.token_amount,
            logger,
        )?;

        for Withdraw {
            to,
            withdraw_amount,
            data,
        } in simple_withdraws
        {
            let single_withdraw = match withdraw_amount {
                SigningAmount::CCDAmount(_) => {
                    bail!(CustomContractError::WrongAmountType.into())
                }
                SigningAmount::TokenAmount(ref single_withdraw) => single_withdraw,
            };

            // Update the contract state
            {
                let mut contract_balances = host
                    .state_mut()
                    .token_balances
                    .entry(single_withdraw.cis2_token_contract_address)
                    .occupied_or(CustomContractError::InsufficientFunds)?;

                let mut token_balances = contract_balances
                    .balances
                    .entry(single_withdraw.token_id.clone())
                    .occupied_or(CustomContractError::InsufficientFunds)?;

                let mut from_cis2_token_balance = token_balances
                    .entry(signer)
                    .occupied_or(CustomContractError::InsufficientFunds)?;

                ensure!(
                    *from_cis2_token_balance >= single_withdraw.token_amount,
                    CustomContractError::InsufficientFunds.into()
                );
                *from_cis2_token_balance -= single_withdraw.token_amount;
            }

            // Create Transfer parameter.
            let data: TransferParameter = TransferParams(vec![Transfer {
                token_id: single_withdraw.token_id.clone(),
                amount: single_withdraw.token_amount,
                from: Address::Contract(ctx.self_address()),
                to: to.clone(),
                data,
            }]);

            // Invoke the `transfer` function on the CIS-2 token contract.
            host.invoke_contract(
                &single_withdraw.cis2_token_contract_address,
                &data,
                EntrypointName::new_unchecked("transfer"),
                Amount::zero(),
            )?;

            let to_address = match to {
                Receiver::Account(account_address) => Address::Account(account_address),
                Receiver::Contract(contract_address, _) => Address::Contract(contract_address),
            };

            logger.log(&Event::WithdrawCis2Tokens(WithdrawCis2TokensEvent {
                token_amount: single_withdraw.token_amount,
                token_id: single_withdraw.token_id.clone(),
                cis2_token_contract_address: single_withdraw.cis2_token_contract_address,
                from: signer,
                to: to_address,
            }))?;
        }

        logger.log(&Event::Nonce(NonceEvent {
            public_key: signer,
            nonce,
        }))?;
    }

    Ok(())
}

/// A single transfer of native currency or some amount of tokens.
#[derive(Serialize, Clone, SchemaType)]
pub struct InternalTransfer {
    /// The public key receiving the tokens being transferred.
    pub to:              PublicKeyEd25519,
    /// The amount of tokens being transferred.
    pub transfer_amount: SigningAmount,
}

/// The transfer message that is signed by the signer.
#[derive(Serialize, Clone, SchemaType)]
pub struct InternalTransferMessage {
    /// The entry_point that the signature is intended for.
    pub entry_point:           OwnedEntrypointName,
    /// A timestamp to make the signatures expire.
    pub expiry_time:           Timestamp,
    /// A nonce to prevent replay attacks.
    pub nonce:                 u64,
    /// The recipient public key of the service fee.
    pub service_fee_recipient: PublicKeyEd25519,
    /// The amount of native currency or tokens to be received as a service fee.
    pub service_fee_amount:    SigningAmount,
    /// List of transfers.
    #[concordium(size_length = 2)]
    pub simple_transfers:      Vec<InternalTransfer>,
}

/// A batch of transfers signed by a signer.
#[derive(Serialize, SchemaType)]
pub struct InternalTransferBatch {
    /// The signer public key.
    pub signer:    PublicKeyEd25519,
    /// The signature.
    pub signature: SignatureEd25519,
    /// The message being signed.
    pub message:   InternalTransferMessage,
}

/// The parameter type for the contract functions
/// `internalTransferNativeCurrency/internalTransferCis2Tokens`.
#[derive(Serialize, SchemaType)]
#[concordium(transparent)]
pub struct InternalTransferParameter {
    /// List of transfer batches.
    #[concordium(size_length = 2)]
    pub transfers: Vec<InternalTransferBatch>,
}

/// Validates the transfer message signature and increases the public key nonce.
///
/// It rejects if:
/// - the message is expired.
/// - the signature is invalid.
/// - the nonce is wrong.
fn validate_signature_and_increase_nonce_internal_transfer_message(
    message: InternalTransferMessage,
    signer: PublicKeyEd25519,
    signature: SignatureEd25519,
    host: &mut Host<State>,
    crypto_primitives: &impl HasCryptoPrimitives,
    ctx: &ReceiveContext,
) -> ContractResult<()> {
    // Check that the signature is not expired.
    ensure!(message.expiry_time > ctx.metadata().slot_time(), CustomContractError::Expired);

    // Calculate the message hash.
    let message_hash =
        calculate_message_hash_from_bytes(&to_bytes(&message), crypto_primitives, ctx)?;

    // Check the signature.
    let valid_signature =
        crypto_primitives.verify_ed25519_signature(signer, signature, &message_hash);
    ensure!(valid_signature, CustomContractError::WrongSignature);

    // Get the nonce.
    let mut entry = host.state_mut().nonces_registry.entry(signer).or_insert_with(|| 0);

    // Check the nonce to prevent replay attacks.
    ensure_eq!(message.nonce, *entry, CustomContractError::NonceMismatch);

    // Bump the nonce.
    *entry += 1;

    Ok(())
}

/// Helper function to calculate the `InternalTransferMessageHash`.
#[receive(
    contract = "smart_contract_wallet",
    name = "viewInternalTransferMessageHash",
    parameter = "InternalTransferMessage",
    return_value = "[u8;32]",
    error = "CustomContractError",
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

/// The function executes a list of CCD internal transfers to public keys within
/// the smart contract wallet.
///
/// The function logs `InternalNativeCurrencyTransfer`
/// and `Nonce` events.
///
/// It rejects if:
/// - it fails to parse the parameter.
/// - the message was intended for a different entry point.
/// - the `AmountType` is not CCD for the service fee transfer or for any
///   internal transfer.
/// - the message is expired.
/// - the signature is invalid.
/// - the nonce is wrong.
/// - the `signer` has an insufficient balance.
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

    for transfer_batch in param.transfers {
        let InternalTransferBatch {
            signer,
            signature,
            message,
        } = transfer_batch;

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
                bail!(CustomContractError::WrongAmountType.into())
            }
        };

        validate_signature_and_increase_nonce_internal_transfer_message(
            message,
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

        for InternalTransfer {
            to,
            transfer_amount,
        } in simple_transfers
        {
            let ccd_amount = match transfer_amount {
                SigningAmount::CCDAmount(ccd_amount) => ccd_amount,
                SigningAmount::TokenAmount(_) => {
                    bail!(CustomContractError::WrongAmountType.into())
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

/// The function executes a list of token internal transfers to public keys
/// within the smart contract wallet.
///
/// The function logs `InternalCis2TokensTransfer`
/// and `Nonce` events.
///
/// It rejects:
/// - it fails to parse the parameter.
/// - the message was intended for a different entry point.
/// - the `AmountType` is not a CIS-2 token for the service fee transfer or for
///   any internal transfer.
/// - the message is expired.
/// - the signature is invalid.
/// - the nonce is wrong.
/// - the `signer` has an insufficient balance.
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

    for transfer_batch in param.transfers {
        let InternalTransferBatch {
            signer,
            signature,
            message,
        } = transfer_batch;

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
                bail!(CustomContractError::WrongAmountType.into())
            }
            SigningAmount::TokenAmount(token_amount) => token_amount,
        };

        validate_signature_and_increase_nonce_internal_transfer_message(
            message,
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

        for InternalTransfer {
            to,
            transfer_amount,
        } in simple_transfers
        {
            let single_transfer = match transfer_amount {
                SigningAmount::CCDAmount(_) => {
                    bail!(CustomContractError::WrongAmountType.into())
                }
                SigningAmount::TokenAmount(single_transfer) => single_transfer,
            };

            // Update the contract state
            host.state_mut().transfer_cis2_tokens(
                signer,
                to,
                single_transfer.cis2_token_contract_address,
                single_transfer.token_id,
                single_transfer.token_amount,
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
#[derive(Serialize, SchemaType)]
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
/// - the sender is not the owner of the contract instance.
/// - it fails to parse the parameter.
#[receive(
    contract = "smart_contract_wallet",
    name = "setImplementors",
    parameter = "SetImplementorsParams",
    error = "CustomContractError",
    mutable
)]
fn contract_set_implementor(ctx: &ReceiveContext, host: &mut Host<State>) -> ContractResult<()> {
    // Authorize the sender.
    ensure!(ctx.sender().matches_account(&ctx.owner()), CustomContractError::UnAuthorized);
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
/// - it fails to parse the parameter.
#[receive(
    contract = "smart_contract_wallet",
    name = "supports",
    parameter = "SupportsQueryParams",
    return_value = "SupportsQueryResponse",
    error = "CustomContractError"
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

/// The parameter type for the contract function `balanceOfNativeCurrency`.
#[derive(Serialize, SchemaType)]
#[concordium(transparent)]
pub struct NativeCurrencyBalanceOfParameter {
    /// List of balance queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<PublicKeyEd25519>,
}

/// The response which is sent back when calling the contract function
/// `balanceOfNativeCurrency`.
/// It consists of the list of results corresponding to the list of queries.
#[derive(Serialize, SchemaType, PartialEq, Eq)]
#[concordium(transparent)]
pub struct NativeCurrencyBalanceOfResponse(#[concordium(size_length = 2)] pub Vec<Amount>);

/// Conversion helper function.
impl From<Vec<Amount>> for NativeCurrencyBalanceOfResponse {
    fn from(results: Vec<Amount>) -> Self { NativeCurrencyBalanceOfResponse(results) }
}

/// The function queries the CCD balances of a list of public keys.
///
/// It rejects if:
/// - It fails to parse the parameter.
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
    for public_key in params.queries {
        // Query the state for the balance.
        let amount = host.state().balance_native_currency(&public_key);
        response.push(amount);
    }
    let result = NativeCurrencyBalanceOfResponse::from(response);
    Ok(result)
}

/// A query for the token balance of a given public key.
#[derive(Serialize, SchemaType)]
pub struct Cis2TokensBalanceOfQuery {
    /// The ID of the token.
    pub token_id:                    ContractTokenId,
    /// The token contract address.
    pub cis2_token_contract_address: ContractAddress,
    /// The public key.
    pub public_key:                  PublicKeyEd25519,
}

/// The parameter type for the contract function `balanceOfCis2Tokens`.
#[derive(Serialize, SchemaType)]
#[concordium(transparent)]
pub struct Cis2TokensBalanceOfParameter {
    /// List of balance queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<Cis2TokensBalanceOfQuery>,
}

/// The response which is sent back when calling the contract function
/// `balanceOfCis2Tokens`.
/// It consists of the list of results corresponding to the list of queries.
#[derive(Serialize, SchemaType, PartialEq, Eq)]
#[concordium(transparent)]
pub struct Cis2TokensBalanceOfResponse(#[concordium(size_length = 2)] pub Vec<ContractTokenAmount>);

/// Conversion helper function.
impl From<Vec<ContractTokenAmount>> for Cis2TokensBalanceOfResponse {
    fn from(results: Vec<ContractTokenAmount>) -> Self { Cis2TokensBalanceOfResponse(results) }
}

/// The function queries the token balances of a list of public keys.
///
/// It rejects if:
/// - It fails to parse the parameter.
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
        );
        response.push(amount);
    }
    let result = Cis2TokensBalanceOfResponse::from(response);
    Ok(result)
}
