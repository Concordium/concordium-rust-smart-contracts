/*
 * TODO:
 *
 * # Description
 *
 * Note: When we use the word 'address' is referring to either an account
 * address or a contract address.
 *
 * As according to the CTS1 specification, the contract have a `transfer`
 * function for transferring an amount of a specific token id from one
 * address to another address. Likewise an address can enable and/or disable
 * one or more addresses as operators. An operator of some address is allowed
 * to transfer and approve any tokens of the owner.
 *
 */

#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::{
    collections::{HashMap as Map, HashSet as Set},
    *,
};

// Types

/// Token Identifier, which combined with the address of the contract instance,
/// forms the unique identifier of a token.
/// Note: Other token specifications (such as ERC721) use u256 for this, but for
/// efficiency we instead use u64, which is expected to be large enough for all
/// realistic use cases.
type TokenId = u64;

/// An amount of a specific token.
/// Note: Other token specifications (such as ERC20) use u256 for this, but for
/// efficiency we instead use u64, which is expected to be large enough for all
/// realistic use cases.
type TokenAmount = u64;


/// The state of an address.
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
#[contract_state(contract = "CTS1-uGTUt")]
#[derive(Serialize, SchemaType)]
struct State {
    /// The state of each address.
    token: TokenState
}

/// Event to be printed in the log.
///
/// Note: For the serialization to be derived according to the CTS1
/// specification, the order of these events and the order of their fields
/// cannot be changed. However new custom events can safely be appended.
#[derive(Serialize)]
enum Event {
    /// A transfer between two addresses of some amount of tokens.
    Transfer {
        /// The ID of the token being transferred.
        token_id: TokenId,
        /// The amount of tokens being transferred.
        amount:   TokenAmount,
        /// The address owning these tokens before the transfer.
        from:     Address,
        /// The address to receive these tokens after the transfer.
        to:       Address,
    },
    /// Updates to an operator for a specific address and token id.
    UpdateOperator {
        /// The ID of the token where the operator is updated.
        token_id: TokenId,
        /// The address for whom, the operator is updated.
        owner:    Address,
        /// The address who is the operator being updated.
        operator: Address,
        /// The update to the operator.
        update:   OperatorUpdate,
    },
    /// Creation of new tokens, could be both adding some amounts to an existing
    /// token or a entirely new token.
    Minting {
        /// The ID of the token being minted, (possibly a new token ID).
        token_id: TokenId,
        /// The number of tokens being minted, this is allowed to be 0 as well.
        amount:   TokenAmount,
        /// The initial owner of these newly minted amount of tokens.
        owner:    Address,
    },
    /// Destruction of tokens removing some amounts of a token.
    Burning {
        /// The ID of the token where an amount is being burned.
        token_id: TokenId,
        /// The amount of tokens being burned.
        amount:   TokenAmount,
        /// The owner of the tokens being burned.
        owner:    Address,
    },
}

/// The receiving address for a transfer, similar to the Address type, but
/// contains extra information when the receiver address is a contract.
///
/// Note: For the serialization to be derived according to the CTS1
/// specification, the order of the variants and the order of their fields
/// cannot be changed.
#[derive(Serialize, SchemaType)]
enum Receiver {
    /// The receiver is an account address.
    Account(AccountAddress),
    /// The receiver is a contract address.
    Contract {
        /// The receiving address.
        address:  ContractAddress,
        /// The function to call on the receiving contract.
        function: OwnedReceiveName,
        /// Some additional bytes to send with the function.
        data:     Vec<u8>,
    },
}

/// A single transfer of some amount of a token.
///
/// Note: For the serialization to be derived according to the CTS1
/// specification, the order of the fields cannot be changed.
#[derive(Serialize, SchemaType)]
struct Transfer {
    /// The ID of the token being transferred.
    token_id: TokenId,
    /// The amount of tokens being transferred.
    amount:   TokenAmount,
    /// The address owning the tokens being transferred.
    from:     Address,
    /// The address receiving the tokens being transferred.
    to:       Receiver,
}

/// The parameter type for the contract function `transfer`.
type TransferParams = Vec<Transfer>;

/// The update to an the operator.
///
/// Note: For the serialization to be derived according to the CTS1
/// specification, the order of the variants cannot be changed.
#[derive(Serialize, SchemaType)]
enum OperatorUpdate {
    /// Remove the operator.
    Remove,
    /// Add an address as an operator.
    Add,
}

/// The parameter type for the contract function `updateOperator`.
///
/// Note: For the serialization to be derived according to the CTS1
/// specification, the order of the fields cannot be changed.
#[derive(Serialize, SchemaType)]
struct UpdateOperatorParams {
    /// The ID of the token for which an operator is being updated.
    token_id: TokenId,
    /// The address which is either added or removed as an operator.
    /// Note: The address for whom this will become an operator is the sender of
    /// the contract transaction.
    operator: Address,
    /// The update for this operator.
    update:   OperatorUpdate,
}

/// A query for the balance of a given address for a given token.
///
/// Note: For the serialization to be derived according to the CTS1
/// specification, the order of the fields cannot be changed.
#[derive(Serialize)]
struct BalanceOfQuery {
    /// The ID of the token for which to query the balance of.
    token_id: TokenId,
    /// The address for which to query the balance of.
    address:  Address,
}

/// The parameter type for the contract function `balanceOf`.
/// This is contract function can only be called by another contract instance,
/// and there is no reason to derive a SchemaType for this example.
///
/// Note: For the serialization to be derived according to the CTS1
/// specification, the order of the fields cannot be changed.
#[derive(Serialize)]
struct BalanceOfQueryParams {
    /// List of balance queries.
    queries:  Vec<BalanceOfQuery>,
    /// The contract function to trigger with the results of the queries.
    callback: OwnedReceiveName,
}

/// The response which is sent back when calling the contract function
/// `balanceOf`.
/// It consists of the list of queries paired with their corresponding result.
type BalanceOfQueryResponse = Vec<(BalanceOfQuery, TokenAmount)>;

/// The parameter type for the contract function `onReceivingCTS1`.
/// This is contract function can only be called by another contract instance,
/// and there is no reason to derive a SchemaType for this example.
///
/// Note: For the serialization to be derived according to the CTS1
/// specification, the order of the fields cannot be changed.
#[derive(Serialize)]
struct OnReceivingCTS1Params {
    /// The ID of the token received.
    token_id:      TokenId,
    /// The amount of tokens received.
    amount:        TokenAmount,
    /// The previous owner of the tokens being received.
    from:          Address,
    /// The name of the token contract which is tracking the tokens.
    contract_name: OwnedContractName,
    /// Some extra information which where sent as part of the transfer.
    data:          Vec<u8>,
}

#[derive(Serialize, SchemaType)]
struct SellParams {
    amount: TokenAmount,
    receiver: Receiver,
}

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
    /// Invalid contract name.
    /// Note this one is only used by "onReceivingCTS1".
    InvalidContractName,
}

type ContractResult<A> = Result<A, ContractError>;

const TOKEN_ID_WGTU: TokenId = 0;

/// Mapping the logging errors to ContractError.
impl From<LogError> for ContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

impl Receiver {
    /// Get the Address of the receiver.
    fn address(&self) -> Address {
        match self {
            Receiver::Account(address) => Address::Account(*address),
            Receiver::Contract {
                address,
                ..
            } => Address::Contract(*address),
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
    fn is_operator(
        &self,
        token_id: &TokenId,
        address: &Address,
        owner: &Address,
    ) -> ContractResult<bool> {
        ensure_eq!(token_id, &TOKEN_ID_WGTU, ContractError::InvalidTokenId);
        Ok(self.token
            .get(owner)
            .map(|address_state| address_state.operators.contains(address))
            .unwrap_or(false))
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
    fn add_operator(
        &mut self,
        token_id: &TokenId,
        owner: &Address,
        operator: &Address,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID_WGTU, ContractError::InvalidTokenId);
        let address_state = self.token.entry(*owner).or_insert_with(|| AddressState {
            balance:   0,
            operators: Set::default(),
        });
        address_state.operators.insert(*operator);
        Ok(())
    }

    /// Update the state removing an operator for a given token id and address.
    /// Results in an error if the token id does not exist in the state.
    /// Succeeds even if the `operator` is not an operator for this `token_id`
    /// and `address`.
    fn remove_operator(
        &mut self,
        token_id: &TokenId,
        owner: &Address,
        operator: &Address,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID_WGTU, ContractError::InvalidTokenId);
        self.token.get_mut(owner).map(|address_state| address_state.operators.remove(operator));
        Ok(())
    }

    fn mint(&mut self,
        token_id: &TokenId,
        owner: &Address,
        amount: TokenAmount
    )-> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID_WGTU, ContractError::InvalidTokenId);
        let address_state = self.token.entry(*owner).or_insert_with(|| AddressState {
            balance:   0,
            operators: Set::default(),
        });
        address_state.balance += amount;
        Ok(())
    }

    fn burn(&mut self,
        token_id: &TokenId,
        owner: &Address,
        amount: TokenAmount
    )-> ContractResult<()> {
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

/// Initialize contract instance with a number of token types and some amount of
/// tokens all owned by the invoker.
/// Logs a `Minting` event for the single token id with no amounts.
#[init(contract = "CTS1-uGTUt", enable_logger)]
fn contract_init(ctx: &impl HasInitContext, logger: &mut impl HasLogger) -> InitResult<State> {
    // Construct the initial contract state.
    let state = State::new();
    // Get the instantiater of this contract instance.
    let invoker = Address::Account(ctx.init_origin());
    // Log event for every newly minted token.
    logger.log(&Event::Minting {
            token_id: TOKEN_ID_WGTU,
            amount: 0,
            owner: invoker,
    })?;
    Ok(state)
}

#[receive(contract = "CTS1-uGTUt", name = "buy", parameter = "Receiver", enable_logger, payable)]
fn contract_buy<A: HasActions>(
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
    state.mint(&TOKEN_ID_WGTU, &receive_address, amount.micro_gtu)?;

    // Log the newly minted tokens.
    logger.log(&Event::Minting {
        token_id: TOKEN_ID_WGTU,
        amount: amount.micro_gtu,
        owner: sender,
    })?;


    // Only log the transfer event if receiver is not the one who payed for this.
    if sender != receive_address {
        logger.log(&Event::Transfer {
            token_id: TOKEN_ID_WGTU,
            amount: amount.micro_gtu,
            from: sender,
            to: receive_address
        })?;
    }

    // Send message to the receiver of the tokens.
    if let Receiver::Contract{
        address,
        data,
        function,
    } = params {
        let parameter = OnReceivingCTS1Params {
            token_id: TOKEN_ID_WGTU,
            amount: amount.micro_gtu,
            from: sender,
            contract_name: OwnedContractName::new_unchecked("init_CTS1-uGTUt".to_string()),
            data,
        };
        Ok(send(&address, function.as_ref(), Amount::zero(), &parameter))
    } else {
        Ok(A::accept())
    }
}

#[receive(contract = "CTS1-uGTUt", name = "sell", parameter = "SellParams", enable_logger)]
fn contract_sell<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ContractResult<A> {
    let params: SellParams = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    // Update the state.
    state.burn(&TOKEN_ID_WGTU, &sender, params.amount)?;

    // Log the newly minted tokens.
    logger.log(&Event::Burning {
        token_id: TOKEN_ID_WGTU,
        amount: params.amount,
        owner: sender,
    })?;

    let sell_amount = Amount::from_micro_gtu(params.amount);

    let action = match params.receiver {
        Receiver::Account(address) => A::simple_transfer(&address, sell_amount),
        Receiver::Contract{
            address,
            data,
            function,
        } => send(&address, function.as_ref(), sell_amount, &data)
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
#[receive(contract = "CTS1-uGTUt", name = "transfer", parameter = "TransferParams", enable_logger)]
fn contract_transfer<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ContractResult<A> {
    // Parse the parameter.
    let params: TransferParams = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    let mut actions = A::accept();
    for Transfer {
        token_id,
        amount,
        from,
        to,
    } in params
    {
        // Authenticate the sender for this transfer
        ensure!(
            from == sender || state.is_operator(&token_id, &sender, &from)?,
            ContractError::Unauthorized
        );
        let to_address = to.address();
        // Update the contract state
        state.transfer(&token_id, amount, &from, &to_address)?;

        // Log transfer event
        logger.log(&Event::Transfer {
            token_id,
            amount,
            from,
            to: to_address,
        })?;

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
                contract_name: OwnedContractName::new_unchecked("init_CTS1-Multi".to_string()),
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
    contract = "CTS1-uGTUt",
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
        OperatorUpdate::Add => state.add_operator(&params.token_id, &sender, &params.operator)?,
        OperatorUpdate::Remove => {
            state.remove_operator(&params.token_id, &sender, &params.operator)?
        }
    }

    // Log the appropriate event
    logger.log(&Event::UpdateOperator {
        token_id: params.token_id,
        owner:    sender,
        operator: params.operator,
        update:   params.update,
    })?;

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
#[receive(contract = "CTS1-uGTUt", name = "balanceOf")]
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
    let mut response: BalanceOfQueryResponse = Vec::new();
    for query in params.queries {
        // Query the state for balance.
        let amount = state.balance(&query.token_id, &query.address)?;
        response.push((query, amount));
    }
    // Send back the response.
    Ok(send(&sender, params.callback.as_ref(), Amount::zero(), &response))
}

// TODO: Tests
