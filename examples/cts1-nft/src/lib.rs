//! A NFT smart contract example using the Concordium Token Standard CTS1.
//!
//! # Description
//! An instance of this smart contract can contain a number of different token
//! each identified by a token ID. A token is then globally identified by the
//! contract address together with the token ID.
//!
//! In this example the contract is initialized with no tokens, and tokens can
//! be minted through a `mint` contract function, which will only succeed for
//! the contract owner. No functionality to burn token is defined in this
//! example.
//!
//! Note: When we use the word 'address' is referring to either an account
//! address or a contract address.
//!
//! As according to the CTS1 specification, the contract have a `transfer`
//! function for transferring an amount of a specific token type from one
//! address to another address. An address can enable and disable one or more
//! addresses as operators. An operator of some address is allowed to transfer
//! any tokens owned by this address.

#![cfg_attr(not(feature = "std"), no_std)]
use concordium_cts1::*;
use concordium_std::{
    collections::{HashMap as Map, HashSet as Set},
    *,
};

/// The baseurl for the token metadata, gets appended with the token ID as hex
/// encoding before emitted in the TokenMetadata event.
const TOKEN_METADATA_BASE_URL: &str = "https://some.example/token/";

// Types

/// Contract token ID type.
/// To save bytes we use a small token ID type, but is limited to be represented
/// by a `u8`.
type ContractTokenId = TokenIdU8;

/// The parameter for the contract function `mint` which mints a number of
/// tokens to a given address.
#[derive(Serialize, SchemaType)]
struct MintParams {
    /// Owner of the newly minted tokens.
    owner:  Address,
    /// A collection of tokens to mint.
    #[concordium(size_length = 1)]
    tokens: Set<ContractTokenId>,
}

/// The state for each address.
#[derive(Serialize, SchemaType, Default)]
struct AddressState {
    /// The tokens owned by this address.
    #[concordium(size_length = 2)]
    owned_tokens: Set<ContractTokenId>,
    /// The address which are currently enabled as operators for this address.
    #[concordium(size_length = 1)]
    operators:    Set<Address>,
}

/// The contract state.
// Note: The specification does not specify how to structure the contract state
// and this could be structured in a more space efficient way depending on the use case.
#[contract_state(contract = "CTS1-NFT")]
#[derive(Serialize, SchemaType)]
struct State {
    /// The state for each address.
    state:      Map<Address, AddressState>,
    /// All of the token IDs
    all_tokens: Set<ContractTokenId>,
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
    /// Failing to mint new tokens because one of the token IDs already exists
    /// in this contract.
    TokenIdAlreadyExists,
}

/// Wrapping the custom errors in a type with CTS1 errors.
type ContractError = Cts1Error<CustomContractError>;

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

/// Mapping CustomContractError to ContractError
impl From<CustomContractError> for ContractError {
    fn from(c: CustomContractError) -> Self { Cts1Error::Custom(c) }
}

// Functions for creating, updating and querying the contract state.
impl State {
    /// Creates a new state with no tokens.
    fn empty() -> Self {
        State {
            state:      Map::default(),
            all_tokens: Set::default(),
        }
    }

    /// Mint a new token with a given address as the owner
    fn mint(&mut self, token: ContractTokenId, owner: &Address) -> ContractResult<()> {
        ensure!(self.all_tokens.insert(token), CustomContractError::TokenIdAlreadyExists.into());
        let owner_address = self.state.entry(*owner).or_insert_with(AddressState::default);
        owner_address.owned_tokens.insert(token);
        Ok(())
    }

    /// Get the current balance of a given token ID for a given address.
    /// Results in an error if the token ID does not exist in the state.
    /// Since this contract only contains NFTs, the balance will always be
    /// either 1 or 0.
    fn balance(
        &self,
        token_id: &ContractTokenId,
        address: &Address,
    ) -> ContractResult<TokenAmount> {
        ensure!(self.all_tokens.contains(token_id), ContractError::InvalidTokenId);
        let balance = self
            .state
            .get(address)
            .map(|address_state| {
                if address_state.owned_tokens.contains(token_id) {
                    1
                } else {
                    0
                }
            })
            .unwrap_or(0);
        Ok(balance)
    }

    /// Check if a given address is an operator of a given owner address.
    fn is_operator(&self, address: &Address, owner: &Address) -> bool {
        self.state
            .get(owner)
            .map(|address_state| address_state.operators.contains(address))
            .unwrap_or(false)
    }

    /// Update the state with a transfer of some token.
    /// Results in an error if the token ID does not exist in the state or if
    /// the from address have insufficient tokens to do the transfer.
    fn transfer(
        &mut self,
        token_id: &ContractTokenId,
        amount: TokenAmount,
        from: &Address,
        to: &Address,
    ) -> ContractResult<()> {
        ensure!(self.all_tokens.contains(token_id), ContractError::InvalidTokenId);
        // A zero transfer does not modify the state.
        if amount == 0 {
            return Ok(());
        }
        // Since this contract only contains NFTs, no one will have an amount greater
        // than 1. And since the amount cannot be the zero at this point, the
        // address must have insufficient funds for any amount other than 1.
        ensure_eq!(amount, 1, ContractError::InsufficientFunds);

        let from_address_state =
            self.state.get_mut(from).ok_or(ContractError::InsufficientFunds)?;

        // Find and remove the token from the owner, if nothing is removed, we know the
        // address did not own the token.
        let from_had_the_token = from_address_state.owned_tokens.remove(token_id);
        ensure!(from_had_the_token, ContractError::InsufficientFunds);

        // Add the token to the new owner.
        let to_address_state = self.state.entry(*to).or_insert_with(AddressState::default);
        to_address_state.owned_tokens.insert(*token_id);
        Ok(())
    }

    /// Update the state adding a new operator for a given address.
    /// Succeeds even if the `operator` is already an operator for the
    /// `address`.
    fn add_operator(&mut self, owner: &Address, operator: &Address) {
        let owner_address_state = self.state.entry(*owner).or_insert_with(AddressState::default);
        owner_address_state.operators.insert(*operator);
    }

    /// Update the state removing an operator for a given address.
    /// Succeeds even if the `operator` is _not_ an operator for the `address`.
    fn remove_operator(&mut self, owner: &Address, operator: &Address) {
        self.state.get_mut(owner).map(|address_state| address_state.operators.remove(operator));
    }
}

// Contract functions

/// Initialize contract instance with no token types initially.
#[init(contract = "CTS1-NFT")]
fn contract_init(_ctx: &impl HasInitContext) -> InitResult<State> {
    // Construct the initial contract state.
    Ok(State::empty())
}

/// Mint new tokens with a given address as the owner of these tokens.
/// Can only be called by the contract owner.
/// Logs a `Mint` and a `TokenMetadata` event for each token.
/// The url for the token metadata is the token ID encoded in hex, appended on
/// the `TOKEN_METADATA_BASE_URL`.
///
/// It rejects if:
/// - The sender is not the contract instance owner.
/// - Fails to parse parameter.
/// - Any of the tokens fails to be minted, which could be if:
///     - The minted token ID already exists.
///     - Fails to log Mint event
///     - Fails to log TokenMetadata event
///
/// Note: Can at most mint 32 token types in one call due to the limit on the
/// number of logs a smart contract can produce on each function call.
#[receive(contract = "CTS1-NFT", name = "mint", parameter = "MintParams", enable_logger)]
fn contract_mint<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ContractResult<A> {
    // Get the contract owner
    let owner = ctx.owner();
    // Get the sender of the transaction
    let sender = ctx.sender();

    ensure!(sender.matches_account(&owner), ContractError::Unauthorized);

    // Parse the parameter.
    let params: MintParams = ctx.parameter_cursor().get()?;

    for token_id in params.tokens {
        // Mint the token in the state.
        state.mint(token_id, &params.owner)?;

        // Event for minted NFT.
        logger.log(&Event::Mint(MintEvent {
            token_id,
            amount: 1,
            owner: params.owner,
        }))?;

        // Metadata URL for the NFT.
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
    Ok(A::accept())
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
///     - The `token_id` does not exist.
///     - The sender is not the owner of the token, or an operator for this
///       specific `token_id` and `from` address.
///     - The token is not owned by the `from`.
/// - Fails to log event.
/// - Any of the messages sent to contracts receiving a transfer choose to
///   reject.
#[receive(contract = "CTS1-NFT", name = "transfer", parameter = "TransferParameter", enable_logger)]
fn contract_transfer<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ContractResult<A> {
    // Parse the parameter.
    let TransferParams(transfers): TransferParameter = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    let mut actions = A::accept();
    for Transfer {
        token_id,
        amount,
        from,
        to,
        data,
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
            function,
        } = to
        {
            let parameter = OnReceivingCTS1Params {
                token_id,
                amount,
                from,
                contract_name: OwnedContractName::new_unchecked(String::from("init_CTS1-NFT")),
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
    contract = "CTS1-NFT",
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
    logger.log(&Event::<ContractTokenId>::UpdateOperator(UpdateOperatorEvent {
        owner:    sender,
        operator: params.operator,
        update:   params.update,
    }))?;

    Ok(A::accept())
}

/// Get the balance of given token IDs and addresses and callback contract
/// function on sender with the result. Will only succeed if sender is a smart
/// contract.
///
/// It rejects if:
/// - Sender is not a contract.
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
/// - Message sent back with the result rejects.
#[receive(contract = "CTS1-NFT", name = "balanceOf")]
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
    let params: BalanceOfQueryParams<ContractTokenId> = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for balance.
        let amount = state.balance(&query.token_id, &query.address)?;
        response.push((query, amount));
    }
    // Send back the response.
    Ok(send(
        &sender,
        params.callback.as_ref(),
        Amount::zero(),
        &BalanceOfQueryResponse::from(response),
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
    const TOKEN_0: ContractTokenId = TokenIdU8(0);
    const TOKEN_1: ContractTokenId = TokenIdU8(42);

    /// Test helper function which creates a contract state with two tokens with
    /// id `TOKEN_0` and id `TOKEN_1` owned by `ADDRESS_0`
    fn initial_state() -> State {
        let mut state = State::empty();
        state.mint(TOKEN_0, &ADDRESS_0).expect_report("Failed to mint TOKEN_0");
        state.mint(TOKEN_1, &ADDRESS_0).expect_report("Failed to mint TOKEN_0");
        state
    }

    /// Test initialization succeeds.
    #[concordium_test]
    fn test_init() {
        // Setup the context
        let ctx = InitContextTest::empty();

        // Call the contract function.
        let result = contract_init(&ctx);

        // Check the result
        let state = result.expect_report("Contract initialization failed");

        // Check the state
        claim_eq!(state.all_tokens.len(), 0, "No token should be initialized");
    }

    /// Test minting, ensuring the new tokens are owned by the given address and
    /// the appropriate events are logged.
    #[concordium_test]
    fn test_mint() {
        // Setup the context
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(ADDRESS_0);
        ctx.set_owner(ACCOUNT_0);

        // and parameter.
        let mut tokens = Set::default();
        tokens.insert(TOKEN_0);
        tokens.insert(TOKEN_1);
        let parameter = MintParams {
            tokens,
            owner: ADDRESS_0,
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();
        let mut state = State::empty();

        // Call the contract function.
        let result: ContractResult<ActionsTree> = contract_mint(&ctx, &mut logger, &mut state);

        // Check the result
        let actions = result.expect_report("Results in rejection");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        // Check the state
        claim_eq!(state.all_tokens.len(), 2, "Expected two tokens in the state.");
        let balance0 =
            state.balance(&TOKEN_0, &ADDRESS_0).expect_report("Token is expected to exist");
        claim_eq!(balance0, 1, "Tokens should be owned by the given address");

        let balance1 =
            state.balance(&TOKEN_1, &ADDRESS_0).expect_report("Token is expected to exist");
        claim_eq!(balance1, 1, "Tokens should be owned by the given address");

        // Check the logs
        claim!(
            logger.logs.contains(&to_bytes(&Event::Mint(MintEvent {
                owner:    ADDRESS_0,
                token_id: TOKEN_0,
                amount:   1,
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
                    url:  "https://some.example/token/00".to_string(),
                    hash: None,
                },
            }))),
            "Expected an event for token metadata for TOKEN_0"
        );
        claim!(
            logger.logs.contains(&to_bytes(&Event::TokenMetadata(TokenMetadataEvent {
                token_id:     TOKEN_1,
                metadata_url: MetadataUrl {
                    url:  "https://some.example/token/2A".to_string(),
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
            amount:   1,
            from:     ADDRESS_0,
            to:       Receiver::from_account(ACCOUNT_1),
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
        let actions = result.expect_report("Results in rejection");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        // Check the state.
        let balance0 =
            state.balance(&TOKEN_0, &ADDRESS_0).expect_report("Token is expected to exist");
        let balance1 =
            state.balance(&TOKEN_0, &ADDRESS_1).expect_report("Token is expected to exist");
        claim_eq!(balance0, 0, "Token owner balance should be decreased by the transferred amount");
        claim_eq!(
            balance1,
            1,
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
                amount:   1,
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
            token_id: TOKEN_0,
            amount:   1,
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
            token_id: TOKEN_0,
            amount:   1,
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
            state.balance(&TOKEN_0, &ADDRESS_0).expect_report("Token is expected to exist");
        let balance1 =
            state.balance(&TOKEN_0, &ADDRESS_1).expect_report("Token is expected to exist");
        claim_eq!(balance0, 0, "Token owner balance should be decreased by the transferred amount");
        claim_eq!(
            balance1,
            1,
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
                amount:   1,
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
            to_bytes(&Event::<ContractTokenId>::UpdateOperator(UpdateOperatorEvent {
                owner:    ADDRESS_0,
                operator: ADDRESS_1,
                update:   OperatorUpdate::Add,
            })),
            "Incorrect event emitted"
        )
    }
}
