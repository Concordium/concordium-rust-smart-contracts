//! wGTU: An example implementation of CTS1 for a single fungible token.
//!
//! # Description
//! The token in this contract is a wrapped GTU (wGTU), meaning it holds a one
//! to one correspondence with the uGTU.
//!
//! Note: When we use the word 'address' is referring to either an account
//! address or a contract address.
//!
//! As according to the CTS1 specification, the contract have a `transfer`
//! function for transferring an amount of a specific token id from one
//! address to another address. Likewise an address can enable and/or disable
//! one or more addresses as operators per token. An operator of some address
//! and token id is allowed to transfer any amount of this token on behalf of
//! the owner.
//!
//! Besides the contract functions required CTS1, this contract implements a
//! function `wrap` for converting GTU into wGTU tokens. It accepts an amount of
//! GTU and mints this amount of wGTU. The function takes a receiving address as
//! the parameter and transfers the amount of tokens.
//!
//! The contract also implements a contract function `unwrap` for converting
//! wGTU back into GTU. The function takes the amount of tokens to unwrap, the
//! address owning these wGTU and a receiver for the GTU. If the sender is the
//! owner or an operator of the owner, the wGTU are burned and the amount of
//! GTU is send to the receiver.

#![cfg_attr(not(feature = "std"), no_std)]
use concordium_cts::*;
use concordium_std::{
    collections::{HashMap as Map, HashSet as Set},
    *,
};

// Types

/// The state tracked for each address.
#[derive(Serialize, SchemaType)]
struct AddressState {
    /// The number of tokens owned by this address.
    balance:   TokenAmount,
    /// The address which are currently enabled as operators for this token and
    /// this address.
    operators: Set<Address>,
}

type TokenState = Map<Address, AddressState>;

/// The contract state,
#[contract_state(contract = "CTS1-wGTU")]
#[derive(Serialize, SchemaType)]
struct State {
    /// The state the one token.
    token: TokenState,
}

/// Event to be printed in the log.
///
/// Note: For the serialization to be derived according to the CTS1
/// specification, the order of these events and the order of their fields
/// cannot be changed. However new custom events can safely be appended.
#[derive(Serialize)]
enum Event {
    /// A transfer between two addresses of some amount of tokens.
    Transfer(TransferEvent),
    /// Updates to an operator for a specific address and token id.
    UpdateOperator(UpdateOperatorEvent),
    /// Creation of new tokens, could be both adding some amounts to an existing
    /// token or a entirely new token.
    Mint(MintEvent),
    /// Destruction of tokens removing some amounts of a token.
    Burn(BurnEvent),
    /// Setting the metadata for a token.
    TokenMetadata(TokenMetadataEvent),
}

/// The parameter type for the contract function `unwrap`.
/// Takes an amount of tokens and unwrap the GTU and send it to a receiver.
#[derive(Serialize, SchemaType)]
struct UnwrapParams {
    /// The amount of tokens to unwrap.
    amount:   TokenAmount,
    /// The owner of the tokens.
    owner:    Address,
    /// The address to receive these unwrapped GTU.
    receiver: Receiver,
}

/// The parameter type for the contract function `wrap`.
///
/// The receiver for the wrapped GTU tokens.
#[allow(dead_code)]
type WrapParams = Receiver;

/// The different errors the contract can produce.
///
/// Note: For the error code to be derived according to the CTS1
/// specification (derived by Reject), the order of these errors cannot be
/// changed. However new custom errors can safely be appended.
#[derive(Serialize, Debug, PartialEq, Eq, Reject)]
enum ContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Failed logging: Log is full.
    LogFull,
    /// Failed logging: Log is malformed.
    LogMalformed,
    /// Invalid token id
    InvalidTokenId,
    /// The balance of the token owner is insufficient for the transfer.
    InsufficientFunds,
    /// Sender is neither the token owner or an operator of the owner for this
    /// token.
    Unauthorized,
    /// Make the sender an operator of the sender is invalid.
    OperatorIsSender,
    /// Only contracts can send to this function.
    ContractOnly,
}

type ContractResult<A> = Result<A, ContractError>;

/// The id of the wGTU token in this contract.
const TOKEN_ID_WGTU: TokenId = 0;

/// The metadata url for the wGTU token.
const TOKEN_METADATA_URL: &str = "https://some.example/token/wgtu";

/// Mapping the logging errors to ContractError.
impl From<LogError> for ContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
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
    fn balance(&self, token_id: &TokenId, address: &Address) -> ContractResult<TokenAmount> {
        ensure_eq!(token_id, &TOKEN_ID_WGTU, ContractError::InvalidTokenId);
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
        token_id: &TokenId,
        amount: TokenAmount,
        from: &Address,
        to: &Address,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID_WGTU, ContractError::InvalidTokenId);
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
        token_id: &TokenId,
        amount: TokenAmount,
        owner: &Address,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID_WGTU, ContractError::InvalidTokenId);
        let address_state = self.token.entry(*owner).or_insert_with(|| AddressState {
            balance:   0,
            operators: Set::default(),
        });
        address_state.balance += amount;
        Ok(())
    }

    fn burn(
        &mut self,
        token_id: &TokenId,
        amount: TokenAmount,
        owner: &Address,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID_WGTU, ContractError::InvalidTokenId);
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
#[init(contract = "CTS1-wGTU", enable_logger)]
fn contract_init(ctx: &impl HasInitContext, logger: &mut impl HasLogger) -> InitResult<State> {
    // Construct the initial contract state.
    let state = State::new();
    // Get the instantiater of this contract instance.
    let invoker = Address::Account(ctx.init_origin());
    // Log event for the newly minted token.
    logger.log(&Event::Mint(MintEvent {
        token_id: TOKEN_ID_WGTU,
        amount:   0,
        owner:    invoker,
    }))?;

    // Log event for where to find metadata for the token
    logger.log(&Event::TokenMetadata(TokenMetadataEvent {
        token_id:     TOKEN_ID_WGTU,
        metadata_url: MetadataUrl {
            url:  String::from(TOKEN_METADATA_URL),
            hash: None,
        },
    }))?;

    Ok(state)
}

/// Wrap an amount of GTU into wGTU tokens and transfer the tokens if the sender
/// is not the receiver.
#[receive(contract = "CTS1-wGTU", name = "wrap", parameter = "WrapParams", enable_logger, payable)]
fn contract_wrap<A: HasActions>(
    ctx: &impl HasReceiveContext,
    amount: Amount,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ContractResult<A> {
    let params: Receiver = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    let receive_address = params.address();

    // Update the state.
    state.mint(&TOKEN_ID_WGTU, amount.micro_gtu, &receive_address)?;

    // Log the newly minted tokens.
    logger.log(&Event::Mint(MintEvent {
        token_id: TOKEN_ID_WGTU,
        amount:   amount.micro_gtu,
        owner:    sender,
    }))?;

    // Only log a transfer event if receiver is not the one who payed for this.
    if sender != receive_address {
        logger.log(&Event::Transfer(TransferEvent {
            token_id: TOKEN_ID_WGTU,
            amount:   amount.micro_gtu,
            from:     sender,
            to:       receive_address,
        }))?;
    }

    // Send message to the receiver of the tokens.
    if let Receiver::Contract {
        address,
        data,
        function,
    } = params
    {
        let parameter = OnReceivingCTS1Params {
            token_id: TOKEN_ID_WGTU,
            amount: amount.micro_gtu,
            from: sender,
            contract_name: OwnedContractName::new_unchecked(String::from("init_CTS1-wGTU")),
            data,
        };
        Ok(send(&address, function.as_ref(), Amount::zero(), &parameter))
    } else {
        Ok(A::accept())
    }
}

/// Unwrap an amount of wGTU tokens into GTU
#[receive(contract = "CTS1-wGTU", name = "unwrap", parameter = "UnwrapParams", enable_logger)]
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
    state.burn(&TOKEN_ID_WGTU, params.amount, &params.owner)?;

    // Log the burning of tokens.
    logger.log(&Event::Burn(BurnEvent {
        token_id: TOKEN_ID_WGTU,
        amount:   params.amount,
        owner:    params.owner,
    }))?;

    let unwrapped_amount = Amount::from_micro_gtu(params.amount);

    let action = match params.receiver {
        Receiver::Account(address) => A::simple_transfer(&address, unwrapped_amount),
        Receiver::Contract {
            address,
            data,
            function,
        } => send(&address, function.as_ref(), unwrapped_amount, &data),
    };

    Ok(action)
}

// Contract functions required by CTS1

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
#[receive(contract = "CTS1-wGTU", name = "transfer", parameter = "TransferParams", enable_logger)]
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
        } = cursor.get()?;
        // Authenticate the sender for this transfer
        ensure!(from == sender || state.is_operator(&sender, &from), ContractError::Unauthorized);
        let to_address = to.address();
        // Update the contract state
        state.transfer(&token_id, amount, &from, &to_address)?;

        // Log transfer event
        logger.log(&Event::Transfer(TransferEvent {
            token_id,
            amount,
            from,
            to: to_address,
        }))?;

        // If the receiver is a contract, we add sending it a message to the list of
        // actions.
        if let Receiver::Contract {
            address,
            data,
            function,
        } = to
        {
            let parameter = OnReceivingCTS1Params {
                token_id,
                amount,
                from,
                contract_name: OwnedContractName::new_unchecked(String::from("init_CTS1-Multi")),
                data,
            };
            let action = send(&address, function.as_ref(), Amount::zero(), &parameter);
            actions = actions.and_then(action);
        }
    }
    Ok(actions)
}

/// Enable or disable some address as an operator of the sender address.
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The operator address is the same as the sender address.
/// - Fails to log event.
#[receive(
    contract = "CTS1-wGTU",
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
    let param: UpdateOperatorParams = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    // No reason to be an operator yourself.
    ensure!(param.operator != sender, ContractError::OperatorIsSender);

    // Update the operator in the state.
    match param.update {
        OperatorUpdate::Add => state.add_operator(&sender, &param.operator),
        OperatorUpdate::Remove => state.remove_operator(&sender, &param.operator),
    }

    // Log the appropriate event
    logger.log(&Event::UpdateOperator(UpdateOperatorEvent {
        owner:    sender,
        operator: param.operator,
        update:   param.update,
    }))?;

    Ok(A::accept())
}

/// Get the balance of a given token id for a given address and callback
/// contract function on sender with the result.
/// Will only succeed if called a smart contracts.
///
/// It rejects if:
/// - Sender is not a contract.
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
/// - Message sent back with the result rejects.
#[receive(contract = "CTS1-wGTU", name = "balanceOf")]
fn contract_balance_of<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut State,
) -> ContractResult<A> {
    // Ensure the sender is a contract.
    let sender = if let Address::Contract(contract) = ctx.sender() {
        contract
    } else {
        bail!(ContractError::ContractOnly)
    };
    let mut cursor = ctx.parameter_cursor();
    // Parse the callback function.
    let callback: OwnedReceiveName = cursor.get()?;
    // Parse the number of queries.
    let queries_length: u8 = cursor.get()?;

    // Build the response.
    let mut response = Vec::with_capacity(queries_length.into());
    for _ in 0..queries_length {
        // Parse one of the queries.
        let query: BalanceOfQuery = ctx.parameter_cursor().get()?;
        // Query the state for balance.
        let amount = state.balance(&query.token_id, &query.address)?;
        response.push((query, amount));
    }
    // Send back the response.
    Ok(send(&sender, callback.as_ref(), Amount::zero(), &BalanceOfQueryResponse(response)))
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
        state.mint(&TOKEN_ID_WGTU, 400, &ADDRESS_0).expect_report("Failed to setup state");
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
            state.balance(&TOKEN_ID_WGTU, &ADDRESS_0).expect_report("Token is expected to exist");
        claim_eq!(balance0, 0, "No initial tokens are owned by the contract instantiater");

        // Check the logs
        claim_eq!(logger.logs.len(), 2, "Exactly one event should be logged");
        claim!(
            logger.logs.contains(&to_bytes(&Event::Mint(MintEvent {
                owner:    ADDRESS_0,
                token_id: TOKEN_ID_WGTU,
                amount:   0,
            }))),
            "Missing event for minting the token"
        );
        claim!(
            logger.logs.contains(&to_bytes(&Event::TokenMetadata(TokenMetadataEvent {
                token_id:     TOKEN_ID_WGTU,
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
            token_id: TOKEN_ID_WGTU,
            amount:   100,
            from:     ADDRESS_0,
            to:       Receiver::Account(ACCOUNT_1),
        };
        let parameter = TransferParams(vec![transfer]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();
        let mut state = State::new();
        state.mint(&TOKEN_ID_WGTU, 400, &ADDRESS_0).expect_report("Failed to setup state");

        // Call the contract function.
        let result: ContractResult<ActionsTree> = contract_transfer(&ctx, &mut logger, &mut state);
        // Check the result.
        let actions = result.expect_report("Results in rejection");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        // Check the state.
        let balance0 =
            state.balance(&TOKEN_ID_WGTU, &ADDRESS_0).expect_report("Token is expected to exist");
        let balance1 =
            state.balance(&TOKEN_ID_WGTU, &ADDRESS_1).expect_report("Token is expected to exist");
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
            to_bytes(&Event::Transfer(TransferEvent {
                from:     ADDRESS_0,
                to:       ADDRESS_1,
                token_id: TOKEN_ID_WGTU,
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
            to:       Receiver::Account(ACCOUNT_1),
            token_id: TOKEN_ID_WGTU,
            amount:   100,
        };
        let parameter = TransferParams(vec![transfer]);
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
            to:       Receiver::Account(ACCOUNT_1),
            token_id: TOKEN_ID_WGTU,
            amount:   100,
        };
        let parameter = TransferParams(vec![transfer]);
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
            state.balance(&TOKEN_ID_WGTU, &ADDRESS_0).expect_report("Token is expected to exist");
        let balance1 =
            state.balance(&TOKEN_ID_WGTU, &ADDRESS_1).expect_report("Token is expected to exist");
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
            to_bytes(&Event::Transfer(TransferEvent {
                from:     ADDRESS_0,
                to:       ADDRESS_1,
                token_id: TOKEN_ID_WGTU,
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
        let parameter = UpdateOperatorParams {
            operator: ADDRESS_1,
            update:   OperatorUpdate::Add,
        };
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
            to_bytes(&Event::UpdateOperator(UpdateOperatorEvent {
                owner:    ADDRESS_0,
                operator: ADDRESS_1,
                update:   OperatorUpdate::Add,
            })),
            "Incorrect event emitted"
        )
    }
}
