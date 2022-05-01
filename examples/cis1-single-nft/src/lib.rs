//! A NFT smart contract example using the Concordium Token Standard CIS-1.
//!
//! # Description
//! An instance of this smart contract can contain a single NFT token with the
//! token ID of 0.
//!
//! The token is minted when the contract is instantiated.
//!
//! As follows from the CIS1 specification, the contract has a `transfer`
//! function for transferring an amount of a specific token type from one
//! address to another address. An address can enable and disable one or more
//! addresses as operators. An operator of some address is allowed to transfer
//! any tokens owned by this address.

#![cfg_attr(not(feature = "std"), no_std)]
use concordium_cis1::*;
use concordium_std::*;

const TOKEN_ID: ContractTokenId = TokenIdUnit();

// Types

/// Contract token ID type.
/// To save bytes we use a small token ID type, but is limited to be represented
/// by a `u8`.
type ContractTokenId = TokenIdUnit;

/// The state for each address.
#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
struct AddressState<S> {
    /// The address which are currently enabled as operators for this address.
    operators: StateSet<Address, S>,
}

impl<S: HasStateApi> AddressState<S> {
    fn empty(state_builder: &mut StateBuilder<S>) -> Self {
        AddressState {
            operators: state_builder.new_set(),
        }
    }
}

/// The contract state.
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S> {
    /// The owner of the NFT
    owner:         Address,
    /// Url for the metadata
    metadata_url:  MetadataUrl,
    /// The state for each address.
    address_state: StateMap<Address, AddressState<S>, S>,
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
    /// Failed to invoke a contract.
    InvokeContractError,
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

/// Mapping CustomContractError to ContractError
impl From<CustomContractError> for ContractError {
    fn from(c: CustomContractError) -> Self { Cis1Error::Custom(c) }
}

// Functions for creating, updating and querying the contract state.
impl<S: HasStateApi> State<S> {
    /// Creates a new state with no tokens.
    fn new(owner: Address, metadata_url: MetadataUrl, state_builder: &mut StateBuilder<S>) -> Self {
        State {
            owner,
            metadata_url,
            address_state: state_builder.new_map(),
        }
    }

    /// Get the current balance of a given token ID for a given address.
    /// Results in an error if the token ID does not exist in the state.
    /// Since this contract only contains NFTs, the balance will always be
    /// either 1 or 0.
    fn balance(
        &self,
        _token_id: &ContractTokenId,
        address: &Address,
    ) -> ContractResult<TokenAmount> {
        if &self.owner == address {
            Ok(1)
        } else {
            Ok(0)
        }
    }

    /// Check if a given address is an operator of a given owner address.
    fn is_operator(&self, address: &Address, owner: &Address) -> bool {
        self.address_state
            .get(owner)
            .map(|state| state.operators.contains(address))
            .unwrap_or(false)
    }

    /// Update the state with a transfer of some token.
    /// Results in an error if the token ID does not exist in the state or if
    /// the from address has insufficient tokens to do the transfer.
    fn transfer(
        &mut self,
        _token_id: &ContractTokenId,
        amount: TokenAmount,
        from: &Address,
        to: &Address,
    ) -> ContractResult<()> {
        // A zero transfer does not modify the state.
        if amount == 0 {
            return Ok(());
        }
        // Since this contract only contains NFTs, no one will have an amount greater
        // than 1. And since the amount cannot be the zero at this point, the
        // address must have insufficient funds for any amount other than 1.
        ensure_eq!(amount, 1, ContractError::InsufficientFunds);
        ensure_eq!(from, &self.owner, ContractError::InsufficientFunds);

        self.owner = *to;
        Ok(())
    }

    /// Update the state adding a new operator for a given address.
    /// Succeeds even if the `operator` is already an operator for the
    /// `address`.
    fn add_operator(
        &mut self,
        owner: Address,
        operator: Address,
        state_builder: &mut StateBuilder<S>,
    ) {
        let mut owner_state =
            self.address_state.entry(owner).or_insert_with(|| AddressState::empty(state_builder));
        owner_state.operators.insert(operator);
    }

    /// Update the state removing an operator for a given address.
    /// Succeeds even if the `operator` is _not_ an operator for the `address`.
    fn remove_operator(&mut self, owner: &Address, operator: &Address) {
        self.address_state.entry(*owner).and_modify(|owner_address| {
            owner_address.operators.remove(operator);
        });
    }
}

// Contract functions

/// Initialize contract instance with the one NFT.
#[init(contract = "CIS1-singleNFT", parameter = "MetadataUrl", enable_logger)]
fn contract_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
    logger: &mut impl HasLogger,
) -> InitResult<State<S>> {
    let metadata_url: MetadataUrl = ctx.parameter_cursor().get()?;
    let owner = Address::Account(ctx.init_origin());

    // Event for minted NFT.
    logger.log(&Cis1Event::Mint(MintEvent {
        token_id: TOKEN_ID,
        amount: 1,
        owner,
    }))?;

    // Metadata URL for the NFT.
    logger.log(&Cis1Event::TokenMetadata(TokenMetadataEvent {
        token_id:     TOKEN_ID,
        metadata_url: metadata_url.clone(),
    }))?;

    // Construct the initial contract state.
    Ok(State::new(owner, metadata_url, state_builder))
}

type TransferParameter = TransferParams<ContractTokenId>;

/// Execute a list of token transfers, in the order of the list.
///
/// Logs a `Transfer` event for each transfer in the list.
/// Produces an action which sends a message to each contract which are the
/// receiver of a transfer.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the transfers fail to be executed, which could be if:
///     - The sender is not the owner of the token, or an operator for the
///       `from` address.
///     - The token is not owned by the `from`.
/// - Fails to log event.
/// - Any of the messages sent to contracts receiving a transfer choose to
///   reject.
#[receive(
    contract = "CIS1-singleNFT",
    name = "transfer",
    parameter = "TransferParameter",
    mutable,
    enable_logger
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
    for Transfer {
        token_id,
        amount,
        from,
        to,
        data,
    } in transfers
    {
        let state = host.state_mut();
        // Authenticate the sender for this transfer
        ensure!(from == sender || state.is_operator(&sender, &from), ContractError::Unauthorized);
        let to_address = to.address();
        // Update the contract state
        state.transfer(&token_id, amount, &from, &to_address)?;

        // Log transfer event
        logger.log(&Cis1Event::Transfer(TransferEvent {
            token_id,
            amount,
            from,
            to: to_address,
        }))?;

        // If the receiver is a contract we call it.
        if let Receiver::Contract(address, function) = to {
            let parameter = OnReceivingCis1Params {
                token_id,
                amount,
                from,
                contract_name: OwnedContractName::new_unchecked(String::from(
                    "init_CIS1-singleNFT",
                )),
                data,
            };

            host.invoke_contract(
                &address,
                &parameter,
                function.as_receive_name().entrypoint_name(),
                Amount::from_micro_ccd(amount),
            )?;
        }
    }
    Ok(())
}

/// Enable or disable addresses as operators of the sender address.
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Fails to log event.
#[receive(
    contract = "CIS1-singleNFT",
    name = "updateOperator",
    parameter = "UpdateOperatorParams",
    mutable,
    enable_logger
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
    let (state, state_builder) = host.state_and_builder();
    for param in params {
        // Update the operator in the state.
        match param.update {
            OperatorUpdate::Add => state.add_operator(sender, param.operator, state_builder),
            OperatorUpdate::Remove => state.remove_operator(&sender, &param.operator),
        }

        // Log the appropriate event
        logger.log(&Cis1Event::<ContractTokenId>::UpdateOperator(UpdateOperatorEvent {
            owner:    sender,
            operator: param.operator,
            update:   param.update,
        }))?;
    }

    Ok(())
}

/// Takes a list of queries. Each query is an owner address and some address to
/// check as an operator of the owner address. It takes a contract address plus
/// contract function to invoke with the result.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Message sent back with the result rejects.
#[receive(
    contract = "CIS1-singleNFT",
    name = "operatorOf",
    parameter = "OperatorOfQueryParams",
    mutable
)]
fn contract_operator_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>>,
) -> ContractResult<()> {
    // Parse the parameter.
    let params: OperatorOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    let state = host.state();
    for query in params.queries {
        // Query the state for address being an operator of owner.
        let is_operator = state.is_operator(&query.owner, &query.address);
        response.push((query, is_operator));
    }
    host.invoke_contract(
        &params.result_contract,
        &OperatorOfQueryResponse::from(response),
        params.result_function.as_receive_name().entrypoint_name(),
        Amount::zero(),
    )?;

    Ok(())
}

/// Parameter type for the CIS-1 function `balanceOf` specialized to the subset
/// of TokenIDs used by this contract.
type ContractBalanceOfQueryParams = BalanceOfQueryParams<ContractTokenId>;

/// Get the balance of given token IDs and addresses. It takes a contract
/// address plus contract function to invoke with the result.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Message sent back with the result rejects.
#[receive(
    contract = "CIS1-singleNFT",
    name = "balanceOf",
    parameter = "ContractBalanceOfQueryParams",
    mutable
)]
fn contract_balance_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>>,
) -> ContractResult<()> {
    // Parse the parameter.
    let params: ContractBalanceOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    let state = host.state();
    for query in params.queries {
        // Query the state for balance.
        let amount = state.balance(&query.token_id, &query.address)?;
        response.push((query, amount));
    }
    // Send back the response.
    host.invoke_contract(
        &params.result_contract,
        &BalanceOfQueryResponse::from(response),
        params.result_function.as_receive_name().entrypoint_name(),
        Amount::zero(),
    )?;
    Ok(())
}

/// Parameter type for the CIS-1 function `tokenMetadata` specialized to the
/// subset of TokenIDs used by this contract.
type ContractTokenMetadataQueryParams = TokenMetadataQueryParams<ContractTokenId>;

/// Get the token metadata URLs and checksums given a list of token IDs. It
/// takes a contract address plus contract function to invoke with the result.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
/// - Message sent back with the result rejects.
#[receive(
    contract = "CIS1-singleNFT",
    name = "tokenMetadata",
    parameter = "ContractTokenMetadataQueryParams",
    mutable
)]
fn contract_token_metadata<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>>,
) -> ContractResult<()> {
    // Parse the parameter.
    let params: ContractTokenMetadataQueryParams = ctx.parameter_cursor().get()?;
    let state = host.state();
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for token_id in params.queries {
        response.push((token_id, state.metadata_url.clone()));
    }
    // Send back the response.
    host.invoke_contract(
        &params.result_contract,
        &TokenMetadataQueryResponse::from(response),
        params.result_function.as_receive_name().entrypoint_name(),
        Amount::zero(),
    )?;
    Ok(())
}
