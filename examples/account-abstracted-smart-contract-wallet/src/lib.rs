//! #
use concordium_cis2::*;
use concordium_std::*;

#[derive(SchemaType, Serialize)]
pub struct VerificationParameter {
    pub public_key: PublicKeyEd25519,
    pub signature: SignatureEd25519,
    pub message: Vec<u8>,
}

// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct OnReceivingCis2Params<ContractTokenId, A> {
    /// The ID of the token received.
    pub token_id: ContractTokenId,
    /// The amount of tokens received.
    pub amount: A,
    /// The previous owner of the tokens.
    pub from: Address,
    /// Some extra information which was sent as part of the transfer.
    pub data: AdditionalData,
}

/// Part of the parameter type for the contract function `permit`.
/// Specifies the message that is signed.
#[derive(SchemaType, Serialize)]
pub struct PermitMessage {
    /// The contract_address that the signature is intended for.
    pub contract_address: ContractAddress,
    /// A nonce to prevent replay attacks.
    pub nonce: u64,
    /// A timestamp to make signatures expire.
    pub timestamp: Timestamp,
    /// The entry_point that the signature is intended for.
    pub entry_point: OwnedEntrypointName,
    /// The serialized payload that should be forwarded to either the `transfer`
    /// or the `updateOperator` function.
    #[concordium(size_length = 2)]
    pub payload: Vec<u8>,
}

/// The parameter type for the contract function `permit`.
/// Takes a signature, the signer, and the message that was signed.
#[derive(Serialize, SchemaType)]
pub struct PermitParam {
    /// Signature/s. The CIS3 standard supports multi-sig accounts.
    pub signature: AccountSignatures,
    /// Account that created the above signature.
    pub signer: AccountAddress,
    /// Message that was signed.
    pub message: PermitMessage,
}

#[derive(Serialize)]
pub struct PermitParamPartial {
    /// Signature/s. The CIS3 standard supports multi-sig accounts.
    pub signature: AccountSignatures,
    /// Account that created the above signature.
    pub signer: AccountAddress,
}

/// Contract token ID type.
pub type ContractTokenId = TokenIdVec;

/// Contract token amount.
/// Since the tokens are non-fungible the total supply of any token will be at
/// most 1 and it is fine to use a small type for representing token amounts.
pub type ContractTokenAmount = TokenAmountU256;

/// The state for each address.
#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
struct PublicKeyState<S = StateApi> {
    /// The amount of tokens owned by this address.
    token_balances: StateMap<ContractAddress, StateMap<ContractTokenId, ContractTokenAmount, S>, S>,
    ///
    native_balance: Amount,
}

impl PublicKeyState {
    fn empty(state_builder: &mut StateBuilder) -> Self {
        PublicKeyState {
            token_balances: state_builder.new_map(),
            native_balance: Amount::zero(),
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
    balances: StateMap<PublicKeyEd25519, PublicKeyState<S>, S>,
    /// A map with contract addresses providing implementations of additional
    /// standards.
    implementors: StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
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
            balances: state_builder.new_map(),
            implementors: state_builder.new_map(),
            nonces_registry: state_builder.new_map(),
        }
    }

    /// Get the current balance of a given token ID for a given address.
    /// Results in an error if the token ID does not exist in the state.
    /// Since this contract only contains NFTs, the balance will always be
    /// either 1 or 0.
    fn balance(
        &mut self,
        public_key: PublicKeyEd25519,
        contract_address: ContractAddress,
        token_id: ContractTokenId,
    ) -> ContractResult<ContractTokenAmount> {
        let mut public_key_balances =
            self.balances.entry(public_key).occupied_or(CustomContractError::InvalidPublicKey)?;

        let mut contract_token_balances = public_key_balances
            .token_balances
            .entry(contract_address)
            .occupied_or(CustomContractError::InvalidContractAddress)?;

        let cis2_token_balance = contract_token_balances
            .entry(token_id)
            .occupied_or(CustomContractError::InvalidTokenId)?;

        Ok(cis2_token_balance.0.into())
    }

    /// Update the state with a transfer of some token.
    /// Results in an error if the token ID does not exist in the state or if
    /// the from address have insufficient tokens to do the transfer.
    fn transfer(
        &mut self,
        from_public_key: PublicKeyEd25519,
        to_public_key: PublicKeyEd25519,
        contract_address: ContractAddress,
        token_id: ContractTokenId,
        amount: ContractTokenAmount,
    ) -> ContractResult<()> {
        let zero_token_amount = TokenAmountU256 {
            0: 0u8.into(),
        };
        // A zero transfer does not modify the state.
        if amount == zero_token_amount {
            return Ok(());
        }

        {
            let mut from_public_key_balances = self
                .balances
                .entry(from_public_key)
                .occupied_or(CustomContractError::InvalidPublicKey)?;

            let mut from_contract_token_balances = from_public_key_balances
                .token_balances
                .entry(contract_address)
                .occupied_or(CustomContractError::InvalidContractAddress)?;

            let mut from_cis2_token_balance = from_contract_token_balances
                .entry(token_id.clone())
                .occupied_or(CustomContractError::InsufficientFunds)?;

            ensure!(*from_cis2_token_balance >= amount, ContractError::InsufficientFunds);
            *from_cis2_token_balance -= amount;
        }

        let mut to_public_key_balances = self
            .balances
            .entry(to_public_key)
            .occupied_or(CustomContractError::InvalidPublicKey)?;

        let mut to_contract_token_balances = to_public_key_balances
            .token_balances
            .entry(contract_address)
            .occupied_or(CustomContractError::InvalidContractAddress)?;

        let mut to_cis2_token_balance =
            to_contract_token_balances.entry(token_id).or_insert(TokenAmountU256 {
                0: 0u8.into(),
            });

        *to_cis2_token_balance += amount;

        Ok(())
    }

    // /// Check if state contains any implementors for a given standard.
    // fn have_implementors(&self, std_id: &StandardIdentifierOwned) -> SupportResult {
    //     if let Some(addresses) = self.implementors.get(std_id) {
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
    OnlyContract,
    InvalidPublicKey,
    InvalidContractAddress,
    InvalidTokenId,
    InsufficientFunds,
}

pub type ContractError = Cis2Error<CustomContractError>;

pub type ContractResult<A> = Result<A, ContractError>;

/// Mapping CustomContractError to ContractError
impl From<CustomContractError> for ContractError {
    fn from(c: CustomContractError) -> Self {
        Cis2Error::Custom(c)
    }
}

#[init(contract = "account-abstracted-smart-contract-wallet")]
fn contract_init(_ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<State> {
    Ok(State::empty(state_builder))
}

///
#[receive(
    contract = "account-abstracted-smart-contract-wallet",
    name = "depositNativeCurrency",
    parameter = "PublicKeyEd25519",
    payable,
    mutable
)]
fn deposit_native_currency(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    amount: Amount,
) -> ReceiveResult<()> {
    let beneficiary: PublicKeyEd25519 = ctx.parameter_cursor().get()?;

    let (state, builder) = host.state_and_builder();

    let mut public_key_balances =
        state.balances.entry(beneficiary).or_insert_with(|| PublicKeyState::empty(builder));

    public_key_balances.native_balance = amount;

    Ok(())
}

///
#[receive(
    contract = "account-abstracted-smart-contract-wallet",
    name = "depositCis2Tokens",
    parameter = "PublicKeyEd25519",
    mutable
)]
fn deposit_cis2_tokens(ctx: &ReceiveContext, host: &mut Host<State>) -> ReceiveResult<()> {
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

    let mut public_key_balances = state
        .balances
        .entry(cis2_hook_param.data)
        .or_insert_with(|| PublicKeyState::empty(builder));

    let mut contract_token_balances = public_key_balances
        .token_balances
        .entry(contract_sender_address)
        .or_insert_with(|| builder.new_map());

    let mut cis2_token_balance = contract_token_balances
        .entry(cis2_hook_param.token_id)
        .or_insert_with(|| TokenAmountU256 {
            0: 0u8.into(),
        });

    *cis2_token_balance += cis2_hook_param.amount;
    
    Ok(())
}

///
#[receive(
    contract = "account-abstracted-smart-contract-wallet",
    name = "internalTransferNativeCurrency",
    parameter = "PublicKeyEd25519",
    payable,
    mutable
)]
fn internal_transfer_native_currency(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    amount: Amount,
) -> ReceiveResult<()> {
    let beneficiary: PublicKeyEd25519 = ctx.parameter_cursor().get()?;

    let (state, builder) = host.state_and_builder();

    let mut public_key_balances =
        state.balances.entry(beneficiary).or_insert_with(|| PublicKeyState::empty(builder));

    public_key_balances.native_balance = amount;

    Ok(())
}

/// The parameter type for the contract function `transfer`.
#[derive(Debug, Serialize, Clone, SchemaType)]
#[concordium(transparent)]
pub struct TransferParameter(#[concordium(size_length = 2)] pub Vec<Transfer>);

/// A single transfer of some amount of a token.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, Clone, SchemaType)]
pub struct Transfer {
    /// The address owning the tokens being transferred.
    pub from_public_key: PublicKeyEd25519,
    /// The address receiving the tokens being transferred.
    pub to_public_key: PublicKeyEd25519,
    ///
    pub contract_address: ContractAddress,
    /// The ID of the token being transferred.
    pub token_id: ContractTokenId,
    /// The amount of tokens being transferred.
    pub amount: ContractTokenAmount,
}

///
#[receive(
    contract = "account-abstracted-smart-contract-wallet",
    name = "internalTransferCis2Token",
    parameter = "PublicKeyEd25519",
    mutable
)]
fn internal_transfer_cis2_token(ctx: &ReceiveContext, host: &mut Host<State>) -> ReceiveResult<()> {
    // Parse the parameter.
    let TransferParameter(transfers): TransferParameter = ctx.parameter_cursor().get()?;

    for Transfer {
        from_public_key,
        to_public_key,
        contract_address,
        token_id,
        amount,
    } in transfers
    {
        // TODO: this needs to be authorized by the singer instead.
        // Authenticate the sender for this transfer
        // Get the sender who invoked this contract function.
        // let sender = ctx.sender();
        // ensure!(from == sender || state.is_operator(&sender, &from), ContractError::Unauthorized);

        // Update the contract state
        host.state_mut().transfer(
            from_public_key,
            to_public_key,
            contract_address,
            token_id,
            amount,
        )?;

        // TODO: add events
        // // Log transfer event
        // logger.log(&WccdEvent::Cis2Event(Cis2Event::Transfer(TransferEvent {
        //     token_id,
        //     amount,
        //     from,
        //     to: to_address,
        // })))?;
    }

    Ok(())
}
