//! A multi token example implementation of the Concordium Token Standard CTS1.
//!
//! # Description
//! An instance of this smart contract can contain a number of different token
//! types each identified by a token ID. A token type is then globally
//! identified by the contract address together with the token ID.
//!
//! In this example the contract takes a list of token IDs and amounts, and
//! each token is then minted at instantiation with this specific amount and
//! they are all owned by the account instantiating initially.
//! No other minting or burning functionality is defined in this example.
//!
//! Note: The word 'address' is referring to either an account address or a
//! contract address.
//!
//! As according to the CTS1 specification, the contract have a `transfer`
//! function for transferring an amount of a specific token id from one
//! address to another address. Likewise an address can enable and/or disable
//! one or more addresses as operators. An operator of some address is allowed
//! to transfer and approve any tokens of the owner.
//!
//! This contract also contains an example of a function to be called when
//! receiving tokens. In which case the contract will forward the tokens to
//! the contract owner.
//! This function is not very useful and is only there to showcase a simple
//! implementation.

#![cfg_attr(not(feature = "std"), no_std)]
use concordium_cts::*;
use concordium_std::{
    collections::{HashMap as Map, HashSet as Set},
    *,
};
#[cfg(not(feature = "std"))]
extern crate alloc;
#[cfg(not(feature = "std"))]
use alloc::string::ToString;

/// The baseurl for the token metadata, gets appended with the token id before
/// emitted in the TokenMetadata event.
const TOKEN_METADATA_BASE_URL: &str = "https://some.example/token/";

// Types

/// Tokens and their amounts to be minted at contract instantiation.
type NewTokens = Map<TokenId, TokenAmount>;

/// The state for each address.
#[derive(Serialize, SchemaType, Default)]
struct AddressState {
    /// The amount of tokens owned by this address.
    balances:  Map<TokenId, TokenAmount>,
    /// The address which are currently enabled as operators for this address.
    operators: Set<Address>,
}

/// The contract state,
///
/// Note: The specification does not specify how to structure the contract state
/// and this could be structured in a more space efficient way.
#[contract_state(contract = "CTS1-Multi")]
#[derive(Serialize, SchemaType)]
struct State {
    /// The state of addresses.
    state:  Map<Address, AddressState>,
    /// All of the token IDs
    tokens: Set<TokenId>,
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
    /// Invalid contract name.
    /// Note this one is only used by "onReceivingCTS1".
    InvalidContractName,
}

type ContractError = Cts1Error<CustomContractError>;

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
    fn from(c: CustomContractError) -> Self { Cts1Error::Custom(c) }
}

impl State {
    /// Creates a new state with a number of tokens all with the same owner.
    fn new(new_tokens: NewTokens, owner: Address) -> Self {
        let mut tokens = Set::default();
        for &token_id in new_tokens.keys() {
            tokens.insert(token_id);
        }

        let address_state = AddressState {
            balances:  new_tokens,
            operators: Set::default(),
        };

        let mut state = Map::default();
        state.insert(owner, address_state);
        State {
            state,
            tokens,
        }
    }

    /// Get the current balance of a given token id for a given address.
    /// Results in an error if the token id does not exist in the state.
    fn balance(&self, token_id: &TokenId, address: &Address) -> ContractResult<TokenAmount> {
        ensure!(self.tokens.contains(token_id), ContractError::InvalidTokenId);
        let balance = self
            .state
            .get(address)
            .and_then(|address_state| address_state.balances.get(token_id))
            .unwrap_or(&0);
        Ok(*balance)
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
        token_id: &TokenId,
        amount: TokenAmount,
        from: &Address,
        to: &Address,
    ) -> ContractResult<()> {
        ensure!(self.tokens.contains(token_id), ContractError::InvalidTokenId);
        if amount == 0 {
            return Ok(());
        }
        let from_address_state =
            self.state.get_mut(from).ok_or(ContractError::InsufficientFunds)?;
        let from_balance = from_address_state
            .balances
            .get_mut(token_id)
            .ok_or(ContractError::InsufficientFunds)?;
        ensure!(*from_balance >= amount, ContractError::InsufficientFunds);
        *from_balance -= amount;
        let to_address_state = self.state.entry(*to).or_insert_with(|| AddressState::default());
        let to_balance = to_address_state.balances.entry(*token_id).or_insert(0);
        *to_balance += amount;
        Ok(())
    }

    /// Update the state adding a new operator for a given token id and address.
    /// Results in an error if the token id does not exist in the state.
    /// Succeeds even if the `operator` is already an operator for this
    /// `token_id` and `address`.
    fn add_operator(&mut self, owner: &Address, operator: &Address) {
        let owner_address_state =
            self.state.entry(*owner).or_insert_with(|| AddressState::default());
        owner_address_state.operators.insert(*operator);
    }

    /// Update the state removing an operator for a given token id and address.
    /// Results in an error if the token id does not exist in the state.
    /// Succeeds even if the `operator` is not an operator for this `token_id`
    /// and `address`.
    fn remove_operator(&mut self, owner: &Address, operator: &Address) {
        self.state.get_mut(owner).map(|address_state| address_state.operators.remove(operator));
    }
}

// Contract functions

/// Initialize contract instance with a number of token types and some amount of
/// tokens all owned by the invoker.
/// Logs a `Mint` event for each token.
#[init(contract = "CTS1-Multi", parameter = "NewTokens", enable_logger)]
fn contract_init(ctx: &impl HasInitContext, logger: &mut impl HasLogger) -> InitResult<State> {
    // Parse the parameter.
    let tokens: NewTokens = ctx.parameter_cursor().get()?;
    // Get the instantiater of this contract instance.
    let invoker = Address::Account(ctx.init_origin());

    // Log events for every newly minted token.
    for (&token_id, &amount) in tokens.iter() {
        // Event for minted NFT.
        logger.log(&Event::Mint(MintEvent {
            token_id,
            amount,
            owner: invoker,
        }))?;

        // Metadata URL for the token.
        let mut token_metadata_url = String::from(TOKEN_METADATA_BASE_URL);
        token_metadata_url.push_str(&token_id.to_string());
        logger.log(&Event::TokenMetadata(TokenMetadataEvent {
            token_id,
            metadata_url: MetadataUrl {
                url:  token_metadata_url,
                hash: None,
            },
        }))?;
    }
    // Construct the initial contract state.
    let state = State::new(tokens, invoker);

    Ok(state)
}

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
#[receive(contract = "CTS1-Multi", name = "transfer", parameter = "TransferParams", enable_logger)]
fn contract_transfer<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ContractResult<A> {
    // Parse the parameter.
    let TransferParams(transfers) = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    let mut actions = A::accept();
    for Transfer {
        token_id,
        amount,
        from,
        to,
    } in transfers
    {
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
/// - The `token_id` does not exist.
/// - Fails to log event.
#[receive(
    contract = "CTS1-Multi",
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
    let params: UpdateOperatorParams = ctx.parameter_cursor().get()?;

    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    // No reason to be an operator yourself.
    ensure!(params.operator != sender, ContractError::OperatorIsSender);

    // Update the operator in the state.
    match params.update {
        OperatorUpdate::Add => state.add_operator(&sender, &params.operator),
        OperatorUpdate::Remove => state.remove_operator(&sender, &params.operator),
    }

    // Log the appropriate event
    logger.log(&Event::UpdateOperator(UpdateOperatorEvent {
        owner:    sender,
        operator: params.operator,
        update:   params.update,
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
#[receive(contract = "CTS1-Multi", name = "balanceOf")]
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
    // Parse the parameter.
    let params: BalanceOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for balance.
        let amount = state.balance(&query.token_id, &query.address)?;
        response.push((query, amount));
    }
    // Send back the response.
    Ok(send(&sender, params.callback.as_ref(), Amount::zero(), &BalanceOfQueryResponse(response)))
}

/// Example of implementing a function for receiving transfers.
/// It is not required to be implemented by the token contract, but is required
/// to implement such a function by any contract which should receive CTS1
/// tokens.
///
/// This contract function is called when a token is transferred to an instance
/// of this contract and should only be called by a contract implementing CTS1.
/// The parameter include a `data` field which can be used to
/// implement some arbitrary functionality. In this example we choose not to use
/// it, and define the function to forward any transfers to the owner of the
/// contract instance.
///
/// Note: The name of this function is not part the CTS1, and a contract can
/// have multiple functions for receiving tokens.
///
/// It rejects if:
/// - Sender is not a contract.
/// - It fails to parse the parameter.
/// - Contract name part of the parameter is invalid.
/// - Calling back `transfer` to sender contract rejects.
#[receive(contract = "CTS1-Multi", name = "onReceivingCTS1")]
fn contract_on_cts1_received<A: HasActions>(
    ctx: &impl HasReceiveContext,
    _state: &mut State,
) -> ContractResult<A> {
    // Ensure the sender is a contract.
    let sender = if let Address::Contract(contract) = ctx.sender() {
        contract
    } else {
        bail!(ContractError::ContractOnly)
    };

    // Parse the parameter.
    let params: OnReceivingCTS1Params = ctx.parameter_cursor().get()?;

    // Build the transfer from this contract to the contract owner.
    let transfer = Transfer {
        token_id: params.token_id,
        amount:   params.amount,
        from:     Address::Contract(ctx.self_address()),
        to:       Receiver::Account(ctx.owner()),
    };

    let mut transfers = Vec::new();
    transfers.push(transfer);
    let parameter = TransferParams(transfers);

    // Construct the CTS1 function name for transfer.
    let mut receive_name_string = String::from(
        params.contract_name.contract_name().ok_or(CustomContractError::InvalidContractName)?,
    );
    receive_name_string.push_str(".transfer");
    let receive_name = ReceiveName::new_unchecked(&receive_name_string);

    // Send back a transfer
    Ok(send(&sender, receive_name, Amount::zero(), &parameter))
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
    const TOKEN_0: TokenId = 0;
    const TOKEN_1: TokenId = 42;

    /// Test helper function which creates a contract state with two tokens with
    /// id `TOKEN_0` and id `TOKEN_1` owned by `ADDRESS_0`
    fn initial_state() -> State {
        let mut tokens: NewTokens = Map::default();
        tokens.insert(TOKEN_0, 400);
        tokens.insert(TOKEN_1, 1);
        State::new(tokens, ADDRESS_0)
    }

    /// Test initialization succeeds and the tokens are owned by the contract
    /// instantiater and the appropriate events are logged.
    #[concordium_test]
    fn test_init() {
        // Setup the context
        let mut ctx = InitContextTest::empty();
        ctx.set_init_origin(ACCOUNT_0);

        // and parameter.
        let mut tokens: NewTokens = Map::default();
        tokens.insert(TOKEN_0, 400);
        tokens.insert(TOKEN_1, 1);
        let parameter_bytes = to_bytes(&tokens);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();

        // Call the contract function.
        let result = contract_init(&ctx, &mut logger);

        // Check the result
        let state = result.expect_report("Contract initialization failed");

        // Check the state
        claim_eq!(state.tokens.len(), 2, "Only one token is initialized");
        let balance0 =
            state.balance(&TOKEN_0, &ADDRESS_0).expect_report("Token is expected to exist");
        claim_eq!(balance0, 400, "Initial tokens are owned by the contract instantiater");

        let balance1 =
            state.balance(&TOKEN_1, &ADDRESS_0).expect_report("Token is expected to exist");
        claim_eq!(balance1, 1, "Initial tokens are owned by the contract instantiater");

        // Check the logs
        claim_eq!(logger.logs.len(), 4, "Exactly four events should be logged");
        claim!(
            logger.logs.contains(&to_bytes(&Event::Mint(MintEvent {
                owner:    ADDRESS_0,
                token_id: TOKEN_0,
                amount:   400,
            }))),
            "Expected an event for minting TOKEN_0"
        );
        claim!(
            logger.logs.contains(&to_bytes(&Event::Mint(MintEvent {
                owner:    ADDRESS_0,
                token_id: TOKEN_1,
                amount:   1,
            }))),
            "Expected an event for minting TOKEN_1"
        );
        claim!(
            logger.logs.contains(&to_bytes(&Event::TokenMetadata(TokenMetadataEvent {
                token_id:     TOKEN_0,
                metadata_url: MetadataUrl {
                    url:  String::from("https://some.example/token/0"),
                    hash: None,
                },
            }))),
            "Expected an event for token metadata for TOKEN_0"
        );
        claim!(
            logger.logs.contains(&to_bytes(&Event::TokenMetadata(TokenMetadataEvent {
                token_id:     TOKEN_1,
                metadata_url: MetadataUrl {
                    url:  String::from("https://some.example/token/42"),
                    hash: None,
                },
            }))),
            "Expected an event for token metadata for TOKEN_1"
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
            token_id: TOKEN_0,
            amount:   100,
            from:     ADDRESS_0,
            to:       Receiver::Account(ACCOUNT_1),
        };
        let parameter = TransferParams(vec![transfer]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();
        let mut state = initial_state();

        // Call the contract function.
        let result: ContractResult<ActionsTree> = contract_transfer(&ctx, &mut logger, &mut state);
        // Check the result.
        let actions = result.expect_report("Results in rejection");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        // Check the state.
        let balance0 =
            state.balance(&TOKEN_0, &ADDRESS_0).expect_report("Token is expected to exist");
        let balance1 =
            state.balance(&TOKEN_0, &ADDRESS_1).expect_report("Token is expected to exist");
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
                token_id: TOKEN_0,
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
            token_id: TOKEN_0,
            amount:   100,
        };
        let parameter = vec![transfer];
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
            token_id: TOKEN_0,
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
            state.balance(&TOKEN_0, &ADDRESS_0).expect_report("Token is expected to exist");
        let balance1 =
            state.balance(&TOKEN_0, &ADDRESS_1).expect_report("Token is expected to exist");
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
                token_id: TOKEN_0,
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
        let is_operator = state.is_operator(&ADDRESS_1, &ADDRESS_0);
        claim!(is_operator, "Account should be an operator");

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
