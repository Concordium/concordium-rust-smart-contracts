//! A smart contract wallet.
//!
//! This contract implements the CIS-5 (Concordium interoperability
//! specification 5) that defines a smart contract wallet that can hold and
//! transfer CCD and CIS-2 tokens.
//! https://proposals.concordium.software/CIS/cis-5.html
//!
//! CCD/CIS-2 tokens can be deposited into the smart contract wallet
//! by specifying to which public key ([PublicKeyEd25519] schema) the deposit
//! should be assigned. Authorization for token and CCD transfers from the
//! smart contract's assigned public key balance is exclusively granted to the
//! holder of the corresponding private key, ensuring self-custodial control
//! over the assets.
//!
//! Transfers of CCD and CIS-2 token balances (meaning the `withdraw` and
//! `transfer` functions) do not require on-chain transaction submissions.
//! Instead, the holder of the corresponding private key can generate a valid
//! signature and identify a third party to submit the transaction on-chain,
//! potentially incentivizing the third-party involvement through a service fee.
//! The message that was signed specifies the amount of service fee and the
//! service fee recipient's public key.
//!
//! Any withdrawal (CCD or CIS-2 tokens) to a smart contract will
//! invoke a `receiveHook` function on that smart contract.
//!
//! The three main actions in the smart contract wallet that can be taken are:
//! - *deposit*: assigns the balance to a public key within the smart contract
//!   wallet.
//! - *transfer*: assigns the balance to a new public key within the smart
//!   contract wallet.
//! - *withdraw*: withdraws the balance out of the smart contract wallet to a
//!   native account or smart contract.
//!
//! The goal of this standard is to simplify the account creation onboarding
//! flow on Concordium. Users can hold/transfer CCD/CIS-2 tokens
//! without a native account as a starting point (no KYC required). Once users
//! are ready to go through the KYC process to create a native account on
//! Concordium, they can withdraw assets out of the smart contract wallet.
//! The public key accounts in this smart contract wallet can't submit the
//! transactions on chain themselves, but rely on someone with a native account
//! (third-party) to do so.
use concordium_cis2::{self as cis2, *};
use concordium_std::*;
#[cfg(feature = "serde")]
use serde::{Deserialize as SerdeDeserialize, Serialize as SerdeSerialize};

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
    /// The event tracks every time a CCD amount received by the contract is
    /// assigned to a public key.
    #[concordium(tag = 249)]
    DepositCcd(DepositCcdEvent),
    /// The event tracks every time a token amount received by the contract is
    /// assigned to a public key.
    #[concordium(tag = 248)]
    DepositCis2Tokens(DepositCis2TokensEvent),
    /// The event tracks every time a CCD amount held by a public key is
    /// withdrawn to an address.
    #[concordium(tag = 247)]
    WithdrawCcd(WithdrawCcdEvent),
    /// The event tracks every time a token amount held by a public key is
    /// withdrawn to an address.
    #[concordium(tag = 246)]
    WithdrawCis2Tokens(WithdrawCis2TokensEvent),
    /// The event tracks every time a CCD amount held by a public key is
    /// transferred to another public key within the contract.
    #[concordium(tag = 245)]
    TransferCcd(TransferCcdEvent),
    /// The event tracks every time a token amount held by a public key is
    /// transferred to another public key within the contract.
    #[concordium(tag = 244)]
    TransferCis2Tokens(TransferCis2TokensEvent),
}

/// The `NonceEvent` is logged whenever a signature is checked. The event
/// tracks the nonce used by the signer of the message.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct NonceEvent {
    /// The nonce that was used in the message.
    pub nonce:      u64,
    /// Account that signed the message.
    pub public_key: PublicKeyEd25519,
}

/// The `DepositCcdEvent` is logged whenever a CCD amount received by
/// the contract is assigned to a public key.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct DepositCcdEvent {
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

/// The `WithdrawCcdEvent` is logged whenever a CCD amount held by a
/// public key is withdrawn to an address.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct WithdrawCcdEvent {
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

/// The `TransferCcdEvent` is logged whenever a CCD amount
/// held by a public key is transferred to another public key within the
/// contract.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct TransferCcdEvent {
    /// The CCD amount transferred.
    pub ccd_amount: Amount,
    /// The public key that the CCD amount will be transferred from.
    pub from:       PublicKeyEd25519,
    /// The public key that the CCD amount is transferred to.
    pub to:         PublicKeyEd25519,
}

/// The `TransferCis2TokensEvent` is logged whenever a token amount held
/// by a public key is transferred to another public key within the contract.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct TransferCis2TokensEvent {
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

/// The contract state.
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S = StateApi> {
    /// The token balances stored in the state.
    token_balances:
        StateMap<(ContractAddress, ContractTokenId, PublicKeyEd25519), ContractTokenAmount, S>,
    /// The CCD balances stored in the state.
    ccd_balances:    StateMap<PublicKeyEd25519, Amount, S>,
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
    /// Creates a new state with empty balances.
    fn empty(state_builder: &mut StateBuilder) -> Self {
        State {
            ccd_balances:    state_builder.new_map(),
            token_balances:  state_builder.new_map(),
            implementors:    state_builder.new_map(),
            nonces_registry: state_builder.new_map(),
        }
    }

    /// Gets the current CCD balance of a given public key.
    /// Returns a balance of 0 if the public key does not exist in the state.
    fn balance_ccd(&self, public_key: &PublicKeyEd25519) -> Amount {
        self.ccd_balances.get(public_key).map(|s| *s).unwrap_or_else(Amount::zero)
    }

    /// Gets the current balance of a given token ID, a given token contract,
    /// and a given public key. Returns a balance of 0 if the token
    /// contract, token id or public key does not exist in the state.
    fn balance_tokens(
        &self,
        token_id: ContractTokenId,
        cis2_token_contract_address: ContractAddress,
        public_key: PublicKeyEd25519,
    ) -> ContractTokenAmount {
        self.token_balances
            .get(&(cis2_token_contract_address, token_id, public_key))
            .map_or_else(|| TokenAmountU256(0.into()), |x| *x)
    }

    /// Updates the state with a transfer of CCD amount and logs an
    /// `TransferCcd` event. Results in an error if the from public key has
    /// insufficient balance to do the transfer.
    fn transfer_ccd(
        &mut self,
        from_public_key: PublicKeyEd25519,
        to_public_key: PublicKeyEd25519,
        ccd_amount: Amount,
        logger: &mut Logger,
    ) -> ReceiveResult<()> {
        // A zero transfer does not modify the state.
        if ccd_amount != Amount::zero() {
            {
                let mut from_public_key_ccd_balance = self
                    .ccd_balances
                    .entry(from_public_key)
                    .occupied_or(CustomContractError::InsufficientFunds)?;

                *from_public_key_ccd_balance = (*from_public_key_ccd_balance)
                    .checked_sub(ccd_amount)
                    .ok_or(CustomContractError::InsufficientFunds)?;
            }

            let mut to_public_key_ccd_balance =
                self.ccd_balances.entry(to_public_key).or_insert_with(Amount::zero);

            *to_public_key_ccd_balance = (*to_public_key_ccd_balance)
                .checked_add(ccd_amount)
                .ok_or(CustomContractError::Overflow)?;
        }

        logger.log(&Event::TransferCcd(TransferCcdEvent {
            ccd_amount,
            from: from_public_key,
            to: to_public_key,
        }))?;

        Ok(())
    }

    /// Updates the state with a transfer of some tokens and logs an
    /// `TransferCis2Tokens` event. Results in an error if the token
    /// contract, or the token id does not exist in the state or the from public
    /// key has insufficient balance to do the transfer.
    fn transfer_cis2_tokens(
        &mut self,
        from_public_key: PublicKeyEd25519,
        to_public_key: PublicKeyEd25519,
        cis2_token_contract_address: ContractAddress,
        token_id: ContractTokenId,
        token_amount: ContractTokenAmount,
        logger: &mut Logger,
    ) -> ReceiveResult<()> {
        // A zero transfer does not modify the state.
        if token_amount != TokenAmountU256(0.into()) {
            {
                let mut from_cis2_token_balance = self
                    .token_balances
                    .entry((cis2_token_contract_address, token_id.clone(), from_public_key))
                    .occupied_or(CustomContractError::InsufficientFunds)?;

                ensure!(
                    *from_cis2_token_balance >= token_amount,
                    CustomContractError::InsufficientFunds.into()
                );
                *from_cis2_token_balance -= token_amount;
            }

            let mut to_cis2_token_balance = self
                .token_balances
                .entry((cis2_token_contract_address, token_id.clone(), to_public_key))
                .or_insert_with(|| TokenAmountU256(0.into()));

            // A well designed CIS-2 token contract should not overflow.
            ensure!(
                *to_cis2_token_balance + token_amount >= *to_cis2_token_balance,
                CustomContractError::Overflow.into()
            );
            *to_cis2_token_balance += token_amount;
        }

        logger.log(&Event::TransferCis2Tokens(TransferCis2TokensEvent {
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
    /// Failed because of an overflow in the token/CCD amount.
    Overflow, // -11
}

/// ContractResult type.
pub type ContractResult<A> = Result<A, CustomContractError>;

/// Trait definition of the `IsMessage`. This trait is implemented for the two
/// types `WithdrawMessage` and `TransferMessage`. The `isMessage` trait is used
/// as an input parameter to the `validate_signature_and_increase_nonce`
/// function so that the function works with both message types.
trait IsMessage {
    fn expiry_time(&self) -> Timestamp;
    fn nonce(&self) -> u64;
}

// Contract functions

/// Initializes the contract instance with no balances.
#[init(contract = "smart_contract_wallet", event = "Event", error = "CustomContractError")]
fn contract_init(_ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<State> {
    Ok(State::empty(state_builder))
}

/// The function is payable and deposits/assigns the send CCD amount to a public
/// key.
///
/// The function logs a `DepositCcd` event.
///
/// It rejects if:
/// - it fails to parse the parameter.
/// - an overflow occurs.
/// - it fails to log the event.
#[receive(
    contract = "smart_contract_wallet",
    name = "depositCcd",
    parameter = "PublicKeyEd25519",
    error = "CustomContractError",
    enable_logger,
    payable,
    mutable
)]
fn deposit_ccd(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    amount: Amount,
    logger: &mut Logger,
) -> ReceiveResult<()> {
    let to: PublicKeyEd25519 = ctx.parameter_cursor().get()?;

    let mut public_key_balance =
        host.state_mut().ccd_balances.entry(to).or_insert_with(Amount::zero);

    *public_key_balance =
        (*public_key_balance).checked_add(amount).ok_or(CustomContractError::Overflow)?;

    logger.log(&Event::DepositCcd(DepositCcdEvent {
        ccd_amount: amount,
        from: ctx.sender(),
        to,
    }))?;

    Ok(())
}

/// The function should be called through the receive hook mechanism of a CIS-2
/// token contract. The function deposits/assigns the sent CIS-2 tokens to a
/// public key.
///
/// The function logs a `DepositCis2Tokens` event.
///
/// It rejects if:
/// - it fails to parse the parameter.
/// - the sender is not a contract.
/// - an overflow occurs.
/// - it fails to log the event.
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
    logger: &mut Logger,
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

    let mut cis2_token_balance = host
        .state_mut()
        .token_balances
        .entry((sender_contract_address, cis2_hook_param.token_id.clone(), cis2_hook_param.data))
        .or_insert_with(|| TokenAmountU256(0.into()));

    // A well designed CIS-2 token contract should not overflow.
    ensure!(
        *cis2_token_balance + cis2_hook_param.amount >= *cis2_token_balance,
        CustomContractError::Overflow.into()
    );

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

/// Trait definition of the `SigningAmount`. This trait is implemented for the
/// two types `Amount` and `TokenAmount`. The `SigningAmount` trait
/// is used as a generic parameter in the `WithdrawParameter` and
/// `TransferParameter` types so that we can use the same parameters in
/// the `withdraw`/`transfer` functions (no matter if the
/// function transfers CCD or CIS-2 tokens).
pub trait SigningAmount: Deserial + Serial {}

/// `SigningAmount` trait definition for `Amount`.
impl SigningAmount for Amount {}
/// `SigningAmount` trait definition for `TokenAmount`.
impl SigningAmount for TokenAmount {}

/// The token amount signed in the message.
#[derive(Serialize, Clone, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
pub struct TokenAmount {
    /// The token amount signed in the message.
    pub token_amount:                ContractTokenAmount,
    /// The token id of the token signed in the message.
    pub token_id:                    ContractTokenId,
    /// The token contract of the token signed in the message.
    pub cis2_token_contract_address: ContractAddress,
}

/// A single withdrawal of CCD or some amount of tokens.
#[derive(Serialize, Clone, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
pub struct Withdraw<T: SigningAmount> {
    /// The address receiving the CCD or tokens being withdrawn.
    pub to:              Receiver,
    /// The amount being withdrawn.
    pub withdraw_amount: T,
    /// Some additional data for the receive hook function.
    pub data:            AdditionalData,
}

/// The withdraw message that is signed by the signer.
#[derive(Serialize, Clone, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
pub struct WithdrawMessage<T: SigningAmount> {
    /// The entry_point that the signature is intended for.
    pub entry_point:           OwnedEntrypointName,
    /// A timestamp to make the signatures expire.
    pub expiry_time:           Timestamp,
    /// A nonce to prevent replay attacks.
    pub nonce:                 u64,
    /// The recipient public key of the service fee.
    pub service_fee_recipient: PublicKeyEd25519,
    /// The amount of CCD or tokens to be received as a service fee.
    pub service_fee_amount:    T,
    /// List of withdrawals.
    #[concordium(size_length = 2)]
    pub simple_withdraws:      Vec<Withdraw<T>>,
}

impl<T: SigningAmount> IsMessage for WithdrawMessage<T> {
    fn expiry_time(&self) -> Timestamp { self.expiry_time }

    fn nonce(&self) -> u64 { self.nonce }
}

/// A batch of withdrawals signed by a signer.
#[derive(Serialize, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
pub struct WithdrawBatch<T: SigningAmount> {
    /// The signer public key.
    pub signer:    PublicKeyEd25519,
    /// The signature.
    pub signature: SignatureEd25519,
    /// The message being signed.
    pub message:   WithdrawMessage<T>,
}

/// The parameter type for the contract functions
/// `withdrawCcd/withdrawCis2Tokens`.
#[derive(Serialize, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
#[concordium(transparent)]
#[repr(transparent)]
pub struct WithdrawParameter<T: SigningAmount> {
    /// List of withdraw batches.
    #[concordium(size_length = 2)]
    pub withdraws: Vec<WithdrawBatch<T>>,
}

/// The `TransferParameter` type for the `transfer` function in the CIS-2 token
/// contract.
type Cis2TransferParameter = TransferParams<ContractTokenId, ContractTokenAmount>;

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

/// Validates the message signature and increases the public key nonce.
///
/// It rejects if:
/// - the message is expired.
/// - the signature is invalid.
/// - the nonce is wrong.
/// - the message hash can not be calculated.
fn validate_signature_and_increase_nonce<T: IsMessage + Serial>(
    message: T,
    signer: PublicKeyEd25519,
    signature: SignatureEd25519,
    host: &mut Host<State>,
    crypto_primitives: &impl HasCryptoPrimitives,
    ctx: &ReceiveContext,
) -> ContractResult<()> {
    // Check that the signature is not expired.
    ensure!(message.expiry_time() > ctx.metadata().slot_time(), CustomContractError::Expired);

    // Calculate the message hash.
    let message_hash: [u8; 32] =
        calculate_message_hash_from_bytes(&to_bytes(&message), crypto_primitives, ctx)?;

    // Get the nonce.
    let mut entry = host.state_mut().nonces_registry.entry(signer).or_insert_with(|| 0);

    // Check the nonce to prevent replay attacks.
    ensure_eq!(message.nonce(), *entry, CustomContractError::NonceMismatch);

    // Bump the nonce.
    *entry += 1;

    // Check the signature.
    let valid_signature =
        crypto_primitives.verify_ed25519_signature(signer, signature, &message_hash);
    ensure!(valid_signature, CustomContractError::WrongSignature);

    Ok(())
}

/// Helper function to calculate the `WithdrawMessageHash` for a CCD amount.
#[receive(
    contract = "smart_contract_wallet",
    name = "getCcdWithdrawMessageHash",
    parameter = "WithdrawMessage<Amount>",
    return_value = "[u8;32]",
    error = "CustomContractError",
    crypto_primitives,
    mutable
)]
fn contract_get_ccd_withdraw_message_hash(
    ctx: &ReceiveContext,
    _host: &mut Host<State>,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<[u8; 32]> {
    // Parse the parameter.
    let param: WithdrawMessage<Amount> = ctx.parameter_cursor().get()?;

    calculate_message_hash_from_bytes(&to_bytes(&param), crypto_primitives, ctx)
}

/// Helper function to calculate the `WithdrawMessageHash` for a token amount.
#[receive(
    contract = "smart_contract_wallet",
    name = "getCis2WithdrawMessageHash",
    parameter = "WithdrawMessage<TokenAmount>",
    return_value = "[u8;32]",
    error = "CustomContractError",
    crypto_primitives,
    mutable
)]
fn contract_get_cis2_withdraw_message_hash(
    ctx: &ReceiveContext,
    _host: &mut Host<State>,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<[u8; 32]> {
    // Parse the parameter.
    let param: WithdrawMessage<TokenAmount> = ctx.parameter_cursor().get()?;

    calculate_message_hash_from_bytes(&to_bytes(&param), crypto_primitives, ctx)
}

/// The function executes a list of CCD withdrawals to native accounts and/or
/// smart contracts. When withdrawing CCD to a contract address, a CCD receive
/// hook function is triggered.
///
/// The function logs `WithdrawCcd`, `TransferCcd`
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
/// - an overflow occurs.
/// - it fails to log any of the events.
#[receive(
    contract = "smart_contract_wallet",
    name = "withdrawCcd",
    parameter = "WithdrawParameter<Amount>",
    error = "CustomContractError",
    crypto_primitives,
    enable_logger,
    mutable
)]
fn withdraw_ccd(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut Logger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ReceiveResult<()> {
    // Parse the parameter.
    let param: WithdrawParameter<Amount> = ctx.parameter_cursor().get()?;

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

        ensure_eq!(entry_point, "withdrawCcd", CustomContractError::WrongEntryPoint.into());

        validate_signature_and_increase_nonce(
            message,
            signer,
            signature,
            host,
            crypto_primitives,
            ctx,
        )?;

        // Transfer service fee
        host.state_mut().transfer_ccd(signer, service_fee_recipient, service_fee_amount, logger)?;

        for Withdraw {
            to,
            withdraw_amount,
            data,
        } in simple_withdraws
        {
            // Update the contract state
            {
                let mut from_public_key_ccd_balance =
                    host.state_mut()
                        .ccd_balances
                        .entry(signer)
                        .occupied_or(CustomContractError::InsufficientFunds)?;

                *from_public_key_ccd_balance = (*from_public_key_ccd_balance)
                    .checked_sub(withdraw_amount)
                    .ok_or(CustomContractError::InsufficientFunds)?;
            }

            // Withdraw CCD out of the contract.
            let to_address = match to {
                Receiver::Account(account_address) => {
                    host.invoke_transfer(&account_address, withdraw_amount)?;
                    Address::Account(account_address)
                }
                Receiver::Contract(contract_address, function) => {
                    // If the receiver is a contract: invoke the receive hook function.
                    host.invoke_contract_raw(
                        &contract_address,
                        Parameter::new_unchecked(data.as_ref()),
                        function.as_entrypoint_name(),
                        withdraw_amount,
                    )?;
                    Address::Contract(contract_address)
                }
            };

            logger.log(&Event::WithdrawCcd(WithdrawCcdEvent {
                ccd_amount: withdraw_amount,
                from:       signer,
                to:         to_address,
            }))?;
        }

        logger.log(&Event::Nonce(NonceEvent {
            nonce,
            public_key: signer,
        }))?;
    }

    Ok(())
}

/// The function executes a list of token withdrawals to native accounts and/or
/// smart contracts. This function calls the `transfer` function on the CIS-2
/// token contract for every withdrawal.
///
/// The function logs `WithdrawCis2Tokens`, `TransferCis2Tokens`
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
/// - an overflow occurs.
/// - it fails to log any of the events.
#[receive(
    contract = "smart_contract_wallet",
    name = "withdrawCis2Tokens",
    parameter = "WithdrawParameter<TokenAmount>",
    error = "CustomContractError",
    crypto_primitives,
    enable_logger,
    mutable
)]
fn withdraw_cis2_tokens(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut Logger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ReceiveResult<()> {
    // Parse the parameter.
    let param: WithdrawParameter<TokenAmount> = ctx.parameter_cursor().get()?;

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

        validate_signature_and_increase_nonce(
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
            service_fee_amount.cis2_token_contract_address,
            service_fee_amount.token_id.clone(),
            service_fee_amount.token_amount,
            logger,
        )?;

        for Withdraw {
            to,
            withdraw_amount,
            data,
        } in simple_withdraws
        {
            // Update the contract state
            {
                let mut from_cis2_token_balance = host
                    .state_mut()
                    .token_balances
                    .entry((
                        withdraw_amount.cis2_token_contract_address,
                        withdraw_amount.token_id.clone(),
                        signer,
                    ))
                    .occupied_or(CustomContractError::InsufficientFunds)?;

                ensure!(
                    *from_cis2_token_balance >= withdraw_amount.token_amount,
                    CustomContractError::InsufficientFunds.into()
                );
                *from_cis2_token_balance -= withdraw_amount.token_amount;
            }

            // Create Transfer parameter.
            let data: Cis2TransferParameter = TransferParams(vec![cis2::Transfer {
                token_id: withdraw_amount.token_id.clone(),
                amount: withdraw_amount.token_amount,
                from: Address::Contract(ctx.self_address()),
                to: to.clone(),
                data,
            }]);

            // Invoke the `transfer` function on the CIS-2 token contract.
            host.invoke_contract(
                &withdraw_amount.cis2_token_contract_address,
                &data,
                EntrypointName::new_unchecked("transfer"),
                Amount::zero(),
            )?;

            let to_address = to.address();

            logger.log(&Event::WithdrawCis2Tokens(WithdrawCis2TokensEvent {
                token_amount: withdraw_amount.token_amount,
                token_id: withdraw_amount.token_id.clone(),
                cis2_token_contract_address: withdraw_amount.cis2_token_contract_address,
                from: signer,
                to: to_address,
            }))?;
        }

        logger.log(&Event::Nonce(NonceEvent {
            nonce,
            public_key: signer,
        }))?;
    }

    Ok(())
}

/// A single transfer of CCD or some amount of tokens.
#[derive(Serialize, Clone, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
pub struct Transfer<T: SigningAmount> {
    /// The public key receiving the tokens being transferred.
    pub to:              PublicKeyEd25519,
    /// The amount of tokens being transferred.
    pub transfer_amount: T,
}

/// The transfer message that is signed by the signer.
#[derive(Serialize, Clone, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
pub struct TransferMessage<T: SigningAmount> {
    /// The entry_point that the signature is intended for.
    pub entry_point:           OwnedEntrypointName,
    /// A timestamp to make the signatures expire.
    pub expiry_time:           Timestamp,
    /// A nonce to prevent replay attacks.
    pub nonce:                 u64,
    /// The recipient public key of the service fee.
    pub service_fee_recipient: PublicKeyEd25519,
    /// The amount of CCD or tokens to be received as a service fee.
    pub service_fee_amount:    T,
    /// List of transfers.
    #[concordium(size_length = 2)]
    pub simple_transfers:      Vec<Transfer<T>>,
}

impl<T: SigningAmount> IsMessage for TransferMessage<T> {
    fn expiry_time(&self) -> Timestamp { self.expiry_time }

    fn nonce(&self) -> u64 { self.nonce }
}

/// A batch of transfers signed by a signer.
#[derive(Serialize, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
pub struct TransferBatch<T: SigningAmount> {
    /// The signer public key.
    pub signer:    PublicKeyEd25519,
    /// The signature.
    pub signature: SignatureEd25519,
    /// The message being signed.
    pub message:   TransferMessage<T>,
}

/// The parameter type for the contract functions
/// `transferCcd/transferCis2Tokens`.
#[derive(Serialize, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
#[concordium(transparent)]
#[repr(transparent)]
pub struct TransferParameter<T: SigningAmount> {
    /// List of transfer batches.
    #[concordium(size_length = 2)]
    pub transfers: Vec<TransferBatch<T>>,
}

/// Helper function to calculate the `TransferMessageHash` for a CCD
/// amount.
#[receive(
    contract = "smart_contract_wallet",
    name = "getCcdTransferMessageHash",
    parameter = "TransferMessage<Amount>",
    return_value = "[u8;32]",
    error = "CustomContractError",
    crypto_primitives,
    mutable
)]
fn contract_get_ccd_transfer_message_hash(
    ctx: &ReceiveContext,
    _host: &mut Host<State>,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<[u8; 32]> {
    // Parse the parameter.
    let param: TransferMessage<Amount> = ctx.parameter_cursor().get()?;

    calculate_message_hash_from_bytes(&to_bytes(&param), crypto_primitives, ctx)
}

/// Helper function to calculate the `TransferMessageHash` for a token
/// amount.
#[receive(
    contract = "smart_contract_wallet",
    name = "getCis2TransferMessageHash",
    parameter = "TransferMessage<TokenAmount>",
    return_value = "[u8;32]",
    error = "CustomContractError",
    crypto_primitives,
    mutable
)]
fn contract_get_cis2_transfer_message_hash(
    ctx: &ReceiveContext,
    _host: &mut Host<State>,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<[u8; 32]> {
    // Parse the parameter.
    let param: TransferMessage<TokenAmount> = ctx.parameter_cursor().get()?;

    calculate_message_hash_from_bytes(&to_bytes(&param), crypto_primitives, ctx)
}

/// The function executes a list of CCD transfers to public keys within the
/// smart contract wallet.
///
/// The function logs `TransferCcd`
/// and `Nonce` events.
///
/// It rejects if:
/// - it fails to parse the parameter.
/// - the message was intended for a different entry point.
/// - the `AmountType` is not CCD for the service fee transfer or for any
///   transfer.
/// - the message is expired.
/// - the signature is invalid.
/// - the nonce is wrong.
/// - the `signer` has an insufficient balance.
/// - an overflow occurs.
/// - it fails to log any of the events.
#[receive(
    contract = "smart_contract_wallet",
    name = "transferCcd",
    parameter = "TransferParameter<Amount>",
    error = "CustomContractError",
    crypto_primitives,
    enable_logger,
    mutable
)]
fn transfer_ccd(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut Logger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ReceiveResult<()> {
    // Parse the parameter.
    let param: TransferParameter<Amount> = ctx.parameter_cursor().get()?;

    for transfer_batch in param.transfers {
        let TransferBatch {
            signer,
            signature,
            message,
        } = transfer_batch;

        let TransferMessage {
            entry_point,
            expiry_time: _,
            nonce,
            service_fee_recipient,
            service_fee_amount,
            simple_transfers,
        } = message.clone();

        ensure_eq!(entry_point, "transferCcd", CustomContractError::WrongEntryPoint.into());

        validate_signature_and_increase_nonce(
            message,
            signer,
            signature,
            host,
            crypto_primitives,
            ctx,
        )?;

        // Transfer service fee
        host.state_mut().transfer_ccd(signer, service_fee_recipient, service_fee_amount, logger)?;

        for Transfer {
            to,
            transfer_amount,
        } in simple_transfers
        {
            // Update the contract state
            host.state_mut().transfer_ccd(signer, to, transfer_amount, logger)?;
        }

        logger.log(&Event::Nonce(NonceEvent {
            nonce,
            public_key: signer,
        }))?;
    }

    Ok(())
}

/// The function executes a list of token transfers to public keys within the
/// smart contract wallet.
///
/// The function logs `TransferCis2Tokens`
/// and `Nonce` events.
///
/// It rejects:
/// - it fails to parse the parameter.
/// - the message was intended for a different entry point.
/// - the `AmountType` is not a CIS-2 token for the service fee transfer or for
///   any transfer.
/// - the message is expired.
/// - the signature is invalid.
/// - the nonce is wrong.
/// - the `signer` has an insufficient balance.
/// - an overflow occurs.
/// - it fails to log any of the events.
#[receive(
    contract = "smart_contract_wallet",
    name = "transferCis2Tokens",
    parameter = "TransferParameter<TokenAmount>",
    error = "CustomContractError",
    crypto_primitives,
    enable_logger,
    mutable
)]
fn transfer_cis2_tokens(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut Logger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ReceiveResult<()> {
    // Parse the parameter.
    let param: TransferParameter<TokenAmount> = ctx.parameter_cursor().get()?;

    for transfer_batch in param.transfers {
        let TransferBatch {
            signer,
            signature,
            message,
        } = transfer_batch;

        let TransferMessage {
            entry_point,
            expiry_time: _,
            nonce,
            service_fee_recipient,
            service_fee_amount,
            simple_transfers,
        } = message.clone();

        ensure_eq!(entry_point, "transferCis2Tokens", CustomContractError::WrongEntryPoint.into());

        validate_signature_and_increase_nonce(
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
            service_fee_amount.cis2_token_contract_address,
            service_fee_amount.token_id,
            service_fee_amount.token_amount,
            logger,
        )?;

        for Transfer {
            to,
            transfer_amount,
        } in simple_transfers
        {
            // Update the contract state
            host.state_mut().transfer_cis2_tokens(
                signer,
                to,
                transfer_amount.cis2_token_contract_address,
                transfer_amount.token_id,
                transfer_amount.token_amount,
                logger,
            )?;
        }

        logger.log(&Event::Nonce(NonceEvent {
            nonce,
            public_key: signer,
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

/// The parameter type for the contract function `ccdBalanceOf`.
#[derive(Serialize, SchemaType)]
#[concordium(transparent)]
#[repr(transparent)]
pub struct CcdBalanceOfParameter {
    /// List of balance queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<PublicKeyEd25519>,
}

/// The response which is sent back when calling the contract function
/// `ccdBalanceOf`.
/// It consists of the list of results corresponding to the list of queries.
#[derive(Serialize, SchemaType, PartialEq, Eq)]
#[concordium(transparent)]
#[repr(transparent)]
pub struct CcdBalanceOfResponse(#[concordium(size_length = 2)] pub Vec<Amount>);

/// Conversion helper function.
impl From<Vec<Amount>> for CcdBalanceOfResponse {
    fn from(results: Vec<Amount>) -> Self { CcdBalanceOfResponse(results) }
}

/// The function queries the CCD balances of a list of public keys.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "smart_contract_wallet",
    name = "ccdBalanceOf",
    parameter = "CcdBalanceOfParameter",
    return_value = "CcdBalanceOfResponse",
    error = "CustomContractError"
)]
fn contract_ccd_balance_of(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<CcdBalanceOfResponse> {
    // Parse the parameter.
    let params: CcdBalanceOfParameter = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for public_key in params.queries {
        // Query the state for the balance.
        let amount = host.state().balance_ccd(&public_key);
        response.push(amount);
    }
    let result = CcdBalanceOfResponse::from(response);
    Ok(result)
}

/// A query for the token balance of a given public key.
#[derive(Serialize, SchemaType)]
pub struct Cis2BalanceOfQuery {
    /// The ID of the token.
    pub token_id:                    ContractTokenId,
    /// The token contract address.
    pub cis2_token_contract_address: ContractAddress,
    /// The public key.
    pub public_key:                  PublicKeyEd25519,
}

/// The parameter type for the contract function `cis2BalanceOf`.
#[derive(Serialize, SchemaType)]
#[concordium(transparent)]
#[repr(transparent)]
pub struct Cis2BalanceOfParameter {
    /// List of balance queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<Cis2BalanceOfQuery>,
}

/// The response which is sent back when calling the contract function
/// `cis2BalanceOf`.
/// It consists of the list of results corresponding to the list of queries.
#[derive(Serialize, SchemaType, PartialEq, Eq)]
#[concordium(transparent)]
#[repr(transparent)]
pub struct Cis2BalanceOfResponse(#[concordium(size_length = 2)] pub Vec<ContractTokenAmount>);

/// Conversion helper function.
impl From<Vec<ContractTokenAmount>> for Cis2BalanceOfResponse {
    fn from(results: Vec<ContractTokenAmount>) -> Self { Cis2BalanceOfResponse(results) }
}

/// The function queries the token balances of a list of public keys.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "smart_contract_wallet",
    name = "cis2BalanceOf",
    parameter = "Cis2BalanceOfParameter",
    return_value = "Cis2BalanceOfResponse",
    error = "CustomContractError"
)]
fn contract_cis2_balance_of(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<Cis2BalanceOfResponse> {
    // Parse the parameter.
    let params: Cis2BalanceOfParameter = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for balance.
        let amount = host.state().balance_tokens(
            query.token_id,
            query.cis2_token_contract_address,
            query.public_key,
        );
        response.push(amount);
    }
    let result = Cis2BalanceOfResponse::from(response);
    Ok(result)
}

/// The parameter type for the contracts `nonceOf` entrypoint which results in a
/// corresponding list of nonces being returned.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct VecOfPublicKeyEd25519 {
    /// List of queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<PublicKeyEd25519>,
}

/// Response type for the function `nonceOf`.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct NonceOfQueryResponse(#[concordium(size_length = 2)] pub Vec<u64>);

impl From<Vec<u64>> for NonceOfQueryResponse {
    fn from(results: concordium_std::Vec<u64>) -> Self { NonceOfQueryResponse(results) }
}

/// Get the nonces of public keys.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "smart_contract_wallet",
    name = "nonceOf",
    parameter = "VecOfPublicKeyEd25519",
    return_value = "NonceOfQueryResponse",
    error = "CustomContractError"
)]
fn contract_nonce_of(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<NonceOfQueryResponse> {
    // Parse the parameter.
    let params: VecOfPublicKeyEd25519 = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response: Vec<u64> = Vec::with_capacity(params.queries.len());
    for public_key in params.queries {
        // Query the next nonce.
        let nonce = host.state().nonces_registry.get(&public_key).map(|nonce| *nonce).unwrap_or(0);

        response.push(nonce);
    }
    Ok(NonceOfQueryResponse::from(response))
}
