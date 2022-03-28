//! Example of a listing smart contract for CIS-1 Non-fungible token (NFT)
//! contracts. It exposes a function for listing NFTs and a function for buying
//! one of the listed NFTs.
#![cfg_attr(not(feature = "std"), no_std)]
use concordium_cis1::*;
use concordium_std::*;

// Types

/// Supported Contract token ID type.
type ContractTokenId = TokenIdVec;

/// Token
#[derive(Serialize, SchemaType, Hash, PartialEq, Eq)]
struct Token {
    contract: ContractAddress,
    id:       ContractTokenId,
}

/// The contract state.
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S> {
    /// Map of 'CIS1-singleNFT' contract addresses to a listing price
    listings: StateMap<Token, (AccountAddress, Amount), S>,
}

/// The custom errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject)]
enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Failed logging: Log is full.
    LogFull,
    /// Failed logging: Log is malformed.
    LogMalformed,
    /// Unknown token.
    UnknownToken,
    /// The amount is insufficient to buy the token.
    InsufficientAmount,
    /// Only account addresses can buy tokens.
    OnlyAccountAddress,
    /// Only the contract owner can list tokens.
    OnlyOwner,
    /// Failed to invoke a contract.
    InvokeContractError,
    /// Failed to invoke a transfer.
    InvokeTransferError,
}

/// Wrapping the custom errors in a type with CIS1 errors.
type ContractError = Cis1Error<CustomContractError>;

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

/// Mapping errors related to transfer invocations to CustomContractError.
impl From<TransferError> for CustomContractError {
    fn from(_te: TransferError) -> Self { Self::InvokeTransferError }
}

/// Mapping CustomContractError to ContractError
impl From<CustomContractError> for ContractError {
    fn from(c: CustomContractError) -> Self { Cis1Error::Custom(c) }
}

// Functions for creating and updating the contract state.
impl<S: HasStateApi> State<S> {
    /// Creates a new state with no listings.
    fn empty(state_builder: &mut StateBuilder<S>) -> Self {
        State {
            listings: state_builder.new_map(),
        }
    }

    /// Add/update the state with the new listing price.
    fn list(&mut self, token: Token, owner: AccountAddress, price: Amount) {
        self.listings.insert(token, (owner, price));
    }

    /// Remove a listing and fails with UnknownToken, if token is not listed.
    /// Returns the listing price and owner if successful.
    fn unlist(&mut self, token: &Token) -> ContractResult<(AccountAddress, Amount)> {
        self.listings.remove_and_get(token).ok_or_else(|| CustomContractError::UnknownToken.into())
    }
}

#[derive(SchemaType, Serialize)]
struct Listing {
    token: Token,
    owner: AccountAddress,
    price: Amount,
}

#[derive(SchemaType, Serialize)]
struct ListParams {
    #[concordium(size_length = 1)]
    listings: Vec<Listing>,
}

// Contract functions

/// Initialize the listing contract with an empty list of listings.
#[init(contract = "listing-CIS1-singleNFT")]
fn contract_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    Ok(State::empty(state_builder))
}

/// List or update the price of a list of NFTs.
/// Will reject if not send by the contract owner or if it fails to parse the
/// parameter.
///
/// IMPORTANT: Does not validate the listing is from the actual owner. This is
/// meant to be checked by the contract owner before calling.
#[receive(contract = "listing-CIS1-singleNFT", name = "list", parameter = "ListParams", mutable)]
fn contract_list<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    let sender = ctx.sender();
    let contract_owner = ctx.owner();
    ensure!(sender.matches_account(&contract_owner), CustomContractError::OnlyOwner.into());

    let params: ListParams = ctx.parameter_cursor().get()?;
    for listing in params.listings {
        host.state_mut().list(listing.token, listing.owner, listing.price);
    }
    Ok(())
}

#[derive(SchemaType, Serialize)]
struct UnlistParams {
    #[concordium(size_length = 1)]
    tokens: Vec<Token>,
}

/// Remove NFTs from the listing.
///
/// Rejects if
/// - Not send by the contract owner.
/// - it fails to parse the parameter.
/// - Any of the tokens are not listed.
#[receive(
    contract = "listing-CIS1-singleNFT",
    name = "unlist",
    parameter = "UnlistParams",
    mutable
)]
fn contract_unlist<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    let sender = ctx.sender();
    let contract_owner = ctx.owner();
    ensure!(sender.matches_account(&contract_owner), CustomContractError::OnlyOwner.into());

    let params: UnlistParams = ctx.parameter_cursor().get()?;
    for token in params.tokens {
        host.state_mut().unlist(&token)?;
    }
    Ok(())
}

/// Buy one of the listed NFTs.
///
/// Rejects if:
/// - Sender is a contract address.
/// - It fails to parse the parameter.
/// - The token is not listed
/// - The amount is less then the listed price.
/// - The NFT contract transfer rejects.
#[receive(contract = "listing-CIS1-singleNFT", name = "buy", parameter = "Token", mutable, payable)]
fn contract_buy<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    amount: Amount,
) -> ContractResult<()> {
    let sender = match ctx.sender() {
        Address::Account(addr) => addr,
        Address::Contract(_) => bail!(CustomContractError::OnlyAccountAddress.into()),
    };
    let token: Token = ctx.parameter_cursor().get()?;
    let (owner, price) = host.state_mut().unlist(&token)?;
    ensure!(price <= amount, CustomContractError::InsufficientAmount.into());
    let transfer = Transfer {
        token_id: token.id,
        amount:   1,
        from:     Address::Account(owner),
        to:       Receiver::Account(sender),
        data:     AdditionalData::empty(),
    };
    let parameter = TransferParams(vec![transfer]);
    let receive_name = ReceiveName::new_unchecked("CIS1-singleNFT.transfer");
    host.invoke_contract_raw(
        &token.contract,
        Parameter(&to_bytes(&parameter)),
        receive_name.entrypoint_name(),
        Amount::zero(),
    )?;
    host.invoke_transfer(&owner, amount)?;
    Ok(())
}
