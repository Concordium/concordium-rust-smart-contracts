//! wCCD: An example implementation of CIS1 for a single fungible token.
//!
//! # Description
//! The token in this contract is a wrapped CCD (wCCD), meaning it holds a one
//! to one correspondence with the CCD.
//!
//! Note: The word 'address' refers to either an account address or a
//! contract address.
//!
//! As follows from the CIS1 specification, the contract has a `transfer`
//! function for transferring an amount of a specific token type from one
//! address to another address. An address can enable and disable one or more
//! addresses as operators. An operator of some token owner address is allowed
//! to transfer any tokens of the owner.
//!
//! Besides the contract functions required CIS1, this contract implements a
//! function `wrap` for converting CCD into wCCD tokens. It accepts an amount of
//! CCD and mints this amount of wCCD. The function takes a receiving address as
//! the parameter and transfers the amount of tokens.
//!
//! The contract also implements a contract function `unwrap` for converting
//! wCCD back into CCD. The function takes the amount of tokens to unwrap, the
//! address owning these wCCD and a receiver for the CCD. If the sender is the
//! owner or an operator of the owner, the wCCD are burned and the amount of
//! CCD is sent to the receiver.

#![cfg_attr(not(feature = "std"), no_std)]
use concordium_cis1::*;
use concordium_std::{
    collections::{HashMap as Map, HashSet as Set},
    *,
};

/// The id of the wCCD token in this contract.
const TOKEN_ID_WCCD: ContractTokenId = TokenIdUnit();

/// The metadata url for the wCCD token.
const TOKEN_METADATA_URL: &str = "https://some.example/token/wccd";

// Types

/// Contract token ID type.
/// Since this contract will only ever contain this one token type, we use the
/// smallest possible token ID.
type ContractTokenId = TokenIdUnit;

/// The state tracked for each address.
#[derive(Serialize, SchemaType)]
struct AddressState {
    /// The number of tokens owned by this address.
    balance:   TokenAmount,
    /// The address which are currently enabled as operators for this token and
    /// this address.
    #[concordium(size_length = 1)]
    operators: Set<Address>,
}

/// The contract state,
#[contract_state(contract = "CIS1-wCCD")]
#[derive(Serialize, SchemaType)]
struct State {
    /// The state the one token.
    token: Map<Address, AddressState>,
}

/// The parameter type for the contract function `unwrap`.
/// Takes an amount of tokens and unwrap the CCD and send it to a receiver.
#[derive(Serialize, SchemaType)]
struct UnwrapParams {
    /// The amount of tokens to unwrap.
    amount:   TokenAmount,
    /// The owner of the tokens.
    owner:    Address,
    /// The address to receive these unwrapped CCD.
    receiver: Receiver,
    /// Some additional bytes to include in the transfer.
    data:     AdditionalData,
}

/// The parameter type for the contract function `wrap`.
///
/// The receiver for the wrapped CCD tokens.
#[derive(Serialize, SchemaType)]
struct WrapParams {
    /// The address to receive these tokens.
    /// If the receiver is the sender of the message wrapping the tokens, it
    /// will not log a transfer.
    to:   Receiver,
    /// Some additional bytes to include in a transfer.
    data: AdditionalData,
}

/// The different errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject)]
enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Failed logging: Log is full.
    LogFull,
    /// Failed logging: Log is malformed.
    LogMalformed,
}

type ContractError = Cis1Error<CustomContractError>;

type ContractResult<A> = Result<A, ContractError>;

/// Mapping the logging errors to ContractError.
impl From<LogError> for CustomContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

/// Mapping CustomContractError to ContractError
impl From<CustomContractError> for ContractError {
    fn from(c: CustomContractError) -> Self { Cis1Error::Custom(c) }
}

impl State {
    /// Creates a new state with no one owning any tokens by default.
    fn new() -> Self {
        State {
            token: Map::default(),
        }
    }

    /// Get the current balance of a given token id for a given address.
    /// Results in an error if the token id does not exist in the state.
    fn balance(
        &self,
        token_id: &ContractTokenId,
        address: &Address,
    ) -> ContractResult<TokenAmount> {
        ensure_eq!(token_id, &TOKEN_ID_WCCD, ContractError::InvalidTokenId);
        Ok(self.token.get(address).map(|s| s.balance).unwrap_or(0))
    }

    /// Check is an address is an operator of a specific owner address.
    /// Results in an error if the token id does not exist in the state.
    fn is_operator(&self, address: &Address, owner: &Address) -> bool {
        self.token
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
        amount: TokenAmount,
        from: &Address,
        to: &Address,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID_WCCD, ContractError::InvalidTokenId);
        if amount == 0 {
            return Ok(());
        }
        let from_state = self.token.get_mut(from).ok_or(ContractError::InsufficientFunds)?;
        ensure!(from_state.balance >= amount, ContractError::InsufficientFunds);
        from_state.balance -= amount;
        let to_state = self.token.entry(*to).or_insert_with(|| AddressState {
            balance:   0,
            operators: Set::default(),
        });
        to_state.balance += amount;
        Ok(())
    }

    /// Update the state adding a new operator for a given token id and address.
    /// Results in an error if the token id does not exist in the state.
    /// Succeeds even if the `operator` is already an operator for this
    /// `token_id` and `address`.
    fn add_operator(&mut self, owner: &Address, operator: &Address) {
        let address_state = self.token.entry(*owner).or_insert_with(|| AddressState {
            balance:   0,
            operators: Set::default(),
        });
        address_state.operators.insert(*operator);
    }

    /// Update the state removing an operator for a given token id and address.
    /// Results in an error if the token id does not exist in the state.
    /// Succeeds even if the `operator` is not an operator for this `token_id`
    /// and `address`.
    fn remove_operator(&mut self, owner: &Address, operator: &Address) {
        self.token.get_mut(owner).map(|address_state| address_state.operators.remove(operator));
    }

    fn mint(
        &mut self,
        token_id: &ContractTokenId,
        amount: TokenAmount,
        owner: &Address,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID_WCCD, ContractError::InvalidTokenId);
        let address_state = self.token.entry(*owner).or_insert_with(|| AddressState {
            balance:   0,
            operators: Set::default(),
        });
        address_state.balance += amount;
        Ok(())
    }

    fn burn(
        &mut self,
        token_id: &ContractTokenId,
        amount: TokenAmount,
        owner: &Address,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID_WCCD, ContractError::InvalidTokenId);
        if amount == 0 {
            return Ok(());
        }
        let from_state = self.token.get_mut(owner).ok_or(ContractError::InsufficientFunds)?;
        ensure!(from_state.balance >= amount, ContractError::InsufficientFunds);
        from_state.balance -= amount;
        Ok(())
    }
}

// Contract functions

/// Initialize contract instance with no initial tokens.
/// Logs a `Mint` event for the single token id with no amounts.
#[init(contract = "CIS1-wCCD", enable_logger)]
fn contract_init(ctx: &impl HasInitContext, logger: &mut impl HasLogger) -> InitResult<State> {
    // Construct the initial contract state.
    let state = State::new();
    // Get the instantiater of this contract instance.
    let invoker = Address::Account(ctx.init_origin());
    // Log event for the newly minted token.
    logger.log(&Cis1Event::Mint(MintEvent {
        token_id: TOKEN_ID_WCCD,
        amount:   0,
        owner:    invoker,
    }))?;

    // Log event for where to find metadata for the token
    logger.log(&Cis1Event::TokenMetadata(TokenMetadataEvent {
        token_id:     TOKEN_ID_WCCD,
        metadata_url: MetadataUrl {
            url:  String::from(TOKEN_METADATA_URL),
            hash: None,
        },
    }))?;

    Ok(state)
}

/// Wrap an amount of CCD into wCCD tokens and transfer the tokens if the sender
/// is not the receiver.
#[receive(contract = "CIS1-wCCD", name = "wrap", parameter = "WrapParams", enable_logger, payable)]
fn contract_wrap<A: HasActions>(
    ctx: &impl HasReceiveContext,
    amount: Amount,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ContractResult<A> {
    let params: WrapParams = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    let receive_address = params.to.address();

    // Update the state.
    state.mint(&TOKEN_ID_WCCD, amount.micro_ccd, &receive_address)?;

    // Log the newly minted tokens.
    logger.log(&Cis1Event::Mint(MintEvent {
        token_id: TOKEN_ID_WCCD,
        amount:   amount.micro_ccd,
        owner:    sender,
    }))?;

    // Only log a transfer event if receiver is not the one who payed for this.
    if sender != receive_address {
        logger.log(&Cis1Event::Transfer(TransferEvent {
            token_id: TOKEN_ID_WCCD,
            amount:   amount.micro_ccd,
            from:     sender,
            to:       receive_address,
        }))?;
    }

    // Send message to the receiver of the tokens.
    if let Receiver::Contract(address, function) = params.to {
        let parameter = OnReceivingCis1Params {
            token_id:      TOKEN_ID_WCCD,
            amount:        amount.micro_ccd,
            from:          sender,
            contract_name: OwnedContractName::new_unchecked(String::from("init_CIS1-wCCD")),
            data:          params.data,
        };
        Ok(send(&address, function.as_ref(), Amount::zero(), &parameter))
    } else {
        Ok(A::accept())
    }
}

/// Unwrap an amount of wCCD tokens into CCD
#[receive(contract = "CIS1-wCCD", name = "unwrap", parameter = "UnwrapParams", enable_logger)]
fn contract_unwrap<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ContractResult<A> {
    let params: UnwrapParams = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();
    ensure!(
        sender == params.owner || state.is_operator(&sender, &params.owner),
        ContractError::Unauthorized
    );

    // Update the state.
    state.burn(&TOKEN_ID_WCCD, params.amount, &params.owner)?;

    // Log the burning of tokens.
    logger.log(&Cis1Event::Burn(BurnEvent {
        token_id: TOKEN_ID_WCCD,
        amount:   params.amount,
        owner:    params.owner,
    }))?;

    let unwrapped_amount = Amount::from_micro_ccd(params.amount);

    let action = match params.receiver {
        Receiver::Account(address) => A::simple_transfer(&address, unwrapped_amount),
        Receiver::Contract(address, function) => {
            send(&address, function.as_ref(), unwrapped_amount, &params.data)
        }
    };

    Ok(action)
}

// Contract functions required by CIS1

#[allow(dead_code)]
type TransferParameter = TransferParams<ContractTokenId>;

/// Execute a list of token transfers, in the order of the list.
///
/// Logs a `Transfer` event for each transfer in the list.
/// Produces an action which sends a message to each contract which was the
/// receiver of a transfer.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the transfers fail to be executed, which could be if:
///     - The `token_id` does not exist.
///     - The sender is not the owner of the token, or an operator for this
///       specific `token_id` and `from` address.
///     - The token is not owned by the `from`.
/// - Fails to log event.
/// - Any of the messages sent to contracts receiving a transfer choose to
///   reject.
#[receive(
    contract = "CIS1-wCCD",
    name = "transfer",
    parameter = "TransferParameter",
    enable_logger
)]
fn contract_transfer<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ContractResult<A> {
    let mut cursor = ctx.parameter_cursor();
    // Parse the number of transfers.
    let transfers_length: u8 = cursor.get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    let mut actions = A::accept();
    // Loop over the number of transfers.
    for _ in 0..transfers_length {
        // Parse one of the transfers.
        let Transfer {
            token_id,
            amount,
            from,
            to,
            data,
        } = cursor.get()?;
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

        // If the receiver is a contract, we add sending it a message to the list of
        // actions.
        if let Receiver::Contract(address, function) = to {
            let parameter = OnReceivingCis1Params {
                token_id,
                amount,
                from,
                contract_name: OwnedContractName::new_unchecked(String::from("init_CIS1-Multi")),
                data,
            };
            let action = send(&address, function.as_ref(), Amount::zero(), &parameter);
            actions = actions.and_then(action);
        }
    }
    Ok(actions)
}

/// Enable or disable addresses as operators of the sender address.
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The operator address is the same as the sender address.
/// - Fails to log event.
#[receive(
    contract = "CIS1-wCCD",
    name = "updateOperator",
    parameter = "UpdateOperatorParams",
    enable_logger
)]
fn contract_update_operator<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ContractResult<A> {
    // Parse the parameter.
    let UpdateOperatorParams(params) = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    for param in params {
        // Update the operator in the state.
        match param.update {
            OperatorUpdate::Add => state.add_operator(&sender, &param.operator),
            OperatorUpdate::Remove => state.remove_operator(&sender, &param.operator),
        }

        // Log the appropriate event
        logger.log(&Cis1Event::<ContractTokenId>::UpdateOperator(UpdateOperatorEvent {
            owner:    sender,
            operator: param.operator,
            update:   param.update,
        }))?;
    }

    Ok(A::accept())
}

/// Parameter type for the CIS-1 function `balanceOf` specialized to the subset
/// of TokenIDs used by this contract.
// This type is pub to silence the dead_code warning, as this type is only used
// for when generating the schema.
pub type ContractBalanceOfQueryParams = BalanceOfQueryParams<ContractTokenId>;

/// Get the balance of given token IDs and addresses. It takes a contract
/// address plus contract function to invoke with the result.
///
/// It rejects if:
/// - Sender is not a contract.
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
/// - Message sent back with the result rejects.
#[receive(contract = "CIS1-wCCD", name = "balanceOf", parameter = "ContractBalanceOfQueryParams")]
fn contract_balance_of<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut State,
) -> ContractResult<A> {
    let mut cursor = ctx.parameter_cursor();
    // Parse the contract address to receive the result.
    let result_contract: ContractAddress = cursor.get()?;
    // Parse the contract function name to call with the result.
    let result_hook: OwnedReceiveName = cursor.get()?;
    // Parse the number of queries.
    let queries_length: u8 = cursor.get()?;

    // Build the response.
    let mut response = Vec::with_capacity(queries_length.into());
    for _ in 0..queries_length {
        // Parse one of the queries.
        let query: BalanceOfQuery<ContractTokenId> = ctx.parameter_cursor().get()?;
        // Query the state for balance.
        let amount = state.balance(&query.token_id, &query.address)?;
        response.push((query, amount));
    }
    // Send back the response.
    Ok(send(
        &result_contract,
        result_hook.as_ref(),
        Amount::zero(),
        &BalanceOfQueryResponse::from(response),
    ))
}

/// Takes a list of queries. Each query is an owner address and some address to
/// check as an operator of the owner address. It takes a contract address plus
/// contract function to invoke with the result.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Message sent back with the result rejects.
#[receive(contract = "CIS1-wCCD", name = "operatorOf", parameter = "OperatorOfQueryParams")]
fn contract_operator_of<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut State,
) -> ContractResult<A> {
    // Parse the parameter.
    let params: OperatorOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for address being an operator of owner.
        let is_operator = state.is_operator(&query.owner, &query.address);
        response.push((query, is_operator));
    }
    // Send back the response.
    Ok(send(
        &params.result_contract,
        params.result_function.as_ref(),
        Amount::zero(),
        &OperatorOfQueryResponse::from(response),
    ))
}

/// Parameter type for the CIS-1 function `tokenMetadata` specialized to the
/// subset of TokenIDs used by this contract.
// This type is pub to silence the dead_code warning, as this type is only used
// for when generating the schema.
pub type ContractTokenMetadataQueryParams = TokenMetadataQueryParams<ContractTokenId>;

/// Get the token metadata URLs and checksums given a list of token IDs. It
/// takes a contract address plus contract function to invoke with the result.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
/// - Message sent back with the result rejects.
#[receive(
    contract = "CIS1-wCCD",
    name = "tokenMetadata",
    parameter = "ContractTokenMetadataQueryParams"
)]
fn contract_token_metadata<A: HasActions>(
    ctx: &impl HasReceiveContext,
    _state: &mut State,
) -> ContractResult<A> {
    let mut cursor = ctx.parameter_cursor();
    // Parse the contract address to receive the result.
    let result_contract: ContractAddress = cursor.get()?;
    // Parse the contract function name to call with the result.
    let result_hook: OwnedReceiveName = cursor.get()?;
    // Parse the number of queries.
    let queries_length: u8 = cursor.get()?;

    // Build the response.
    let mut response = Vec::with_capacity(queries_length.into());
    for _ in 0..queries_length {
        let token_id: ContractTokenId = cursor.get()?;
        // Check the token exists.
        ensure_eq!(token_id, TOKEN_ID_WCCD, ContractError::InvalidTokenId);

        let metadata_url = MetadataUrl {
            url:  TOKEN_METADATA_URL.to_string(),
            hash: None,
        };
        response.push((token_id, metadata_url));
    }
    // Send back the response.
    Ok(send(
        &result_contract,
        result_hook.as_ref(),
        Amount::zero(),
        &TokenMetadataQueryResponse::from(response),
    ))
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

    /// Test helper function which creates a contract state where ADDRESS_0 owns
    /// 400 tokens.
    fn initial_state() -> State {
        let mut state = State::new();
        state.mint(&TOKEN_ID_WCCD, 400, &ADDRESS_0).expect_report("Failed to setup state");
        state
    }

    /// Test initialization succeeds and the tokens are owned by the contract
    /// instantiater and the appropriate events are logged.
    #[concordium_test]
    fn test_init() {
        // Setup the context
        let mut ctx = InitContextTest::empty();
        ctx.set_init_origin(ACCOUNT_0);

        let mut logger = LogRecorder::init();

        // Call the contract function.
        let result = contract_init(&ctx, &mut logger);

        // Check the result
        let state = result.expect_report("Contract initialization failed");

        // Check the state
        claim_eq!(state.token.len(), 0, "Only one token is initialized");
        let balance0 =
            state.balance(&TOKEN_ID_WCCD, &ADDRESS_0).expect_report("Token is expected to exist");
        claim_eq!(balance0, 0, "No initial tokens are owned by the contract instantiater");

        // Check the logs
        claim_eq!(logger.logs.len(), 2, "Exactly one event should be logged");
        claim!(
            logger.logs.contains(&to_bytes(&Cis1Event::Mint(MintEvent {
                owner:    ADDRESS_0,
                token_id: TOKEN_ID_WCCD,
                amount:   0,
            }))),
            "Missing event for minting the token"
        );
        claim!(
            logger.logs.contains(&to_bytes(&Cis1Event::TokenMetadata(TokenMetadataEvent {
                token_id:     TOKEN_ID_WCCD,
                metadata_url: MetadataUrl {
                    url:  String::from(TOKEN_METADATA_URL),
                    hash: None,
                },
            }))),
            "Missing event with metadata for the token"
        );
    }

    /// Test transfer succeeds, when `from` is the sender.
    #[concordium_test]
    fn test_transfer_account() {
        // Setup the context
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(ADDRESS_0);

        // and parameter.
        let transfer = Transfer {
            token_id: TOKEN_ID_WCCD,
            amount:   100,
            from:     ADDRESS_0,
            to:       Receiver::from_account(ACCOUNT_1),
            data:     AdditionalData::empty(),
        };
        let parameter = TransferParams::from(vec![transfer]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();
        let mut state = State::new();
        state.mint(&TOKEN_ID_WCCD, 400, &ADDRESS_0).expect_report("Failed to setup state");

        // Call the contract function.
        let result: ContractResult<ActionsTree> = contract_transfer(&ctx, &mut logger, &mut state);
        // Check the result.
        let actions = result.expect_report("Results in rejection");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        // Check the state.
        let balance0 =
            state.balance(&TOKEN_ID_WCCD, &ADDRESS_0).expect_report("Token is expected to exist");
        let balance1 =
            state.balance(&TOKEN_ID_WCCD, &ADDRESS_1).expect_report("Token is expected to exist");
        claim_eq!(
            balance0,
            300,
            "Token owner balance should be decreased by the transferred amount"
        );
        claim_eq!(
            balance1,
            100,
            "Token receiver balance should be increased by the transferred amount"
        );

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "Only one event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Cis1Event::Transfer(TransferEvent {
                from:     ADDRESS_0,
                to:       ADDRESS_1,
                token_id: TOKEN_ID_WCCD,
                amount:   100,
            })),
            "Incorrect event emitted"
        )
    }

    /// Test transfer token fails, when sender is neither the owner or an
    /// operator of the owner.
    #[concordium_test]
    fn test_transfer_not_authorized() {
        // Setup the context
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(ADDRESS_1);

        // and parameter.
        let transfer = Transfer {
            from:     ADDRESS_0,
            to:       Receiver::from_account(ACCOUNT_1),
            token_id: TOKEN_ID_WCCD,
            amount:   100,
            data:     AdditionalData::empty(),
        };
        let parameter = TransferParams::from(vec![transfer]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();
        let mut state = initial_state();

        // Call the contract function.
        let result: ContractResult<ActionsTree> = contract_transfer(&ctx, &mut logger, &mut state);
        // Check the result.
        let err = result.expect_err_report("Expected to fail");
        claim_eq!(err, ContractError::Unauthorized, "Error is expected to be Unauthorized")
    }

    /// Test transfer succeeds when sender is not the owner, but is an operator
    /// of the owner.
    #[concordium_test]
    fn test_operator_transfer() {
        // Setup the context
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(ADDRESS_1);

        // and parameter.
        let transfer = Transfer {
            from:     ADDRESS_0,
            to:       Receiver::from_account(ACCOUNT_1),
            token_id: TOKEN_ID_WCCD,
            amount:   100,
            data:     AdditionalData::empty(),
        };
        let parameter = TransferParams::from(vec![transfer]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();
        let mut state = initial_state();
        state.add_operator(&ADDRESS_0, &ADDRESS_1);

        // Call the contract function.
        let result: ContractResult<ActionsTree> = contract_transfer(&ctx, &mut logger, &mut state);

        // Check the result.
        let actions: ActionsTree = result.expect_report("Results in rejection");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        // Check the state.
        let balance0 =
            state.balance(&TOKEN_ID_WCCD, &ADDRESS_0).expect_report("Token is expected to exist");
        let balance1 =
            state.balance(&TOKEN_ID_WCCD, &ADDRESS_1).expect_report("Token is expected to exist");
        claim_eq!(balance0, 300); //, "Token owner balance should be decreased by the transferred amount");
        claim_eq!(
            balance1,
            100,
            "Token receiver balance should be increased by the transferred amount"
        );

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "Only one event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Cis1Event::Transfer(TransferEvent {
                from:     ADDRESS_0,
                to:       ADDRESS_1,
                token_id: TOKEN_ID_WCCD,
                amount:   100,
            })),
            "Incorrect event emitted"
        )
    }

    /// Test adding an operator succeeds and the appropriate event is logged.
    #[concordium_test]
    fn test_add_operator() {
        // Setup the context
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(ADDRESS_0);

        // and parameter.
        let update = UpdateOperator {
            operator: ADDRESS_1,
            update:   OperatorUpdate::Add,
        };
        let parameter = UpdateOperatorParams(vec![update]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();
        let mut state = initial_state();

        // Call the contract function.
        let result: ContractResult<ActionsTree> =
            contract_update_operator(&ctx, &mut logger, &mut state);

        // Check the result.
        let actions: ActionsTree = result.expect_report("Results in rejection");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        // Check the state.
        claim!(state.is_operator(&ADDRESS_1, &ADDRESS_0), "Account should be an operator");

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Cis1Event::<ContractTokenId>::UpdateOperator(UpdateOperatorEvent {
                owner:    ADDRESS_0,
                operator: ADDRESS_1,
                update:   OperatorUpdate::Add,
            })),
            "Incorrect event emitted"
        )
    }
}
