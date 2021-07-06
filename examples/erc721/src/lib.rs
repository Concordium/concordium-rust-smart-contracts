/*
 * An implementation of the "ERC-721 Non-Fungible Token(NFT) Standard"
 * specification popular on the Ethereum blockchain.
 *
 * https://eips.ethereum.org/EIPS/eip-721
 *
 * # Description
 * A smart contract instance represents a number of NFTs and tracks
 * ownership of each. The globally unique id of an NFT is formed by the
 * address of the contract instance and some token_id unique to the instance.
 *
 * A token can be transferred to an address (either an account and a contract
 * instance). Each token can be approved to be transferred by one other
 * address than the owner. Approvals can be done by either the token
 * owner or an "operator" of the owner.
 *
 * An address can enable one or more addresses as operators.
 * An operator of some address is allowed to transfer and approve any tokens
 * of the owner.
 * Note: This can be used to implement 'atomic swap' in another contract.
 *
 * ## Differences from the specification
 *
 * Since the specification is written to target the Ethereum blockchain, some
 * details are implemented differently.
 *
 * - The specification lists a number of "view" functions, which queries for
 *   the current state of the contract and since the Concordium Blockchain
 *   uses message passing for inter-contract communication, these query
 *   functions must also take a name of the callback function to receive the
 *   result of the query.
 * - The specification uses a "zero address" (which is a special address used
 *   as a null-address) which is not a thing on Concordium blockchain,
 *   instead when relevant a byte is used to represent whether the address is
 *   the "zero address" and if not the address is followed, which in a Rust
 *   smart contract corresponds to the serialization of `Option<Address>`.
 *
 */

#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::{
    collections::{HashMap as Map, HashSet as Set},
    *,
};

// Types

/// Token Identifier, which combined with the address of the contract instance,
/// forms the unique identifier of an NFT.
/// Note: The ERC721 specification requires a u256 here, but for efficiency we
/// instead use u64, which is expected to be large enough for all realistic use
/// cases.
type TokenId = u64;

/// Information of which tokens included in this instance.
/// Note: To add the ERC721 metadata extension, change this to a Map from
/// TokenId to some Metadata struct.
type Tokens = Set<TokenId>;

#[derive(Serialize, SchemaType)]
struct State {
    /// Map from a token id to the owning account address.
    /// Every token must be an entry in this map.
    token_owners:    Map<TokenId, Address>,
    /// Map from a token id to an account which are allowed to transfer this
    /// token on the owners behalf.
    /// Only tokens with approvals have entries in this map.
    token_approvals: Map<TokenId, Address>,
    /// Map from an account to operator accounts, which can transfer any token
    /// on their behalf.
    /// Only accounts with operators have entries in this map.
    owner_operators: Map<Address, Set<Address>>,
}

/// Event to be printed in the log.
#[derive(Serialize)]
enum Event {
    /// Ownership of NFT changed.
    /// Note: To add minting and burning the `from` and `to` should be Options,
    /// where `to` is None when burning, and `from` is None when minting.
    Transfer {
        from:     Address,
        to:       Address,
        token_id: TokenId,
    },
    /// Approved transfer of NFT, where `approved` = None means no one is
    /// approved.
    Approval {
        owner:    Address,
        approved: Option<Address>,
        token_id: TokenId,
    },
    /// Change to whether an operator can manage all NFTs of the owner.
    ApprovalForAll {
        owner:    Address,
        operator: Address,
        approved: bool,
    },
}

// Contract Function Parameters

/// Parameter for `safeTransferFrom` and `transferFrom` contract functions.
#[derive(Serialize, SchemaType)]
struct SafeTransferFromParams {
    /// The id of the token to be transferred.
    token_id:     TokenId,
    /// Current owner of the token.
    from:         Address,
    /// The new owner of the token.
    to:           Address,
    /// Contract receive name only used when transferring to a contract
    /// instance.
    receive_name: Option<OwnedReceiveName>,
    /// Optional message, which is sent to the new owner if it is a contract
    /// instance. Only used by `safeTransferFrom` and not by `transferFrom`.
    data:         Vec<u8>,
}

/// Parameter for the `approve` contract function.
#[derive(Serialize, SchemaType)]
struct ApproveParams {
    /// Address approved to transfer a token.
    /// If None: Remove previous approvals to control this token.
    approved: Option<Address>,
    /// The token that the address is approved to transfer.
    token_id: TokenId,
}

/// Parameter for the `approveForAll` contract function.
#[derive(Serialize, SchemaType)]
struct ApproveForAllParams {
    /// Address to act as an operator for the sender of this message.
    operator: Address,
    /// Whether to enable or disable the operator.
    approved: bool,
}

/// Parameter for the optional `onERC721Receive` contract function, is only
/// intended to be used by other ERC721 contracts.
#[derive(Serialize, SchemaType)]
struct OnERC721ReceivedParams {
    /// The token which is transferred to this contract.
    token_id:      TokenId,
    /// Previous owner of the token.
    from:          Address,
    /// Name of the contract implementing erc721
    contract_name: OwnedContractName,
    /// Optional message sent as part of the `safeTransferFrom` which would
    /// trigger this.
    data:          Vec<u8>,
}

/// Parameter for the `balanceOf` function.
/// Only intended to be used by other smart contracts.
#[derive(Serialize)]
struct BalanceOfParams {
    /// The address for whom to query the balance.
    owner:    Address,
    /// The smart contract function to callback with the result.
    callback: OwnedReceiveName,
}

/// The parameter provided to the callback of `balanceOf`.
pub type BalanceOfResponse = u64;

/// Parameter for the `ownerOf` function.
/// Only intended to be used by other smart contracts.
#[derive(Serialize)]
struct OwnerOfParams {
    /// The token id to query the ownership of.
    token_id: TokenId,
    /// The smart contract function to callback with the result.
    callback: OwnedReceiveName,
}

/// The parameter provided to the callback of `ownerOf`.
pub type OwnerOfResponse = Address;

/// Parameter for the `getApproved` function.
/// Only intended to be used by other smart contracts.
#[derive(Serialize)]
struct GetApprovedParams {
    /// The token id to query who is approved.
    token_id: TokenId,
    /// The smart contract function to callback with the result.
    callback: OwnedReceiveName,
}

/// The parameter provided to the callback of `getApproved`.
pub type GetApprovedResponse = Option<Address>;

/// Parameter for the `isApprovedForAll` function.
/// Only intended to be used by other smart contracts.
#[derive(Serialize)]
struct IsApprovedForAllParams {
    /// The address that could be owning tokens.
    owner:    Address,
    /// The address to query for being enabled as operator.
    operator: Address,
    /// The smart contract function to callback with the result.
    callback: OwnedReceiveName,
}

/// The parameter provided to the callback of `isApprovedForAll`.
pub type IsApprovedForAllResponse = bool;

/// Contract error type
#[derive(Debug, PartialEq, Eq, Reject)]
enum ContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Failed logging: Log is full.
    LogFull,
    /// Failed logging: Log is malformed.
    LogMalformed,
    /// Invalid token id: No token with this id.
    NoTokenWithThisId,
    /// The transfer is not from the current owner of the token.
    FromIsNotTheOwner,
    /// Sender is not authorized.
    Unauthorized,
    /// Approving the owner of the token is invalid.
    ApprovedIsOwner,
    /// Make the sender an operator of the sender is invalid.
    OperatorIsSender,
    /// Only contracts can send to this function.
    ContractOnly,
    /// Transferring to a contract instance requires a receive name.
    MissingContractReceiveName,
    /// Invalid contract name.
    /// Note this one is optional since it is only used by "onERC721Received".
    InvalidContractName,
}

type ContractResult<A> = Result<A, ContractError>;

impl From<LogError> for ContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

impl State {
    /// Creates a new state with a number of tokens all with the same owner.
    fn new(tokens: Tokens, owner: Address) -> Self {
        let mut token_owners = Map::default();
        for token_id in tokens {
            token_owners.insert(token_id, owner);
        }

        State {
            token_owners,
            token_approvals: Map::default(),
            owner_operators: Map::default(),
        }
    }

    /// Count the number of tokens owned by a given address.
    fn balance(&self, address: &Address) -> u64 {
        let mut count = 0;
        for owner in self.token_owners.values() {
            if owner == address {
                count += 1;
            }
        }
        return count;
    }

    /// Get the current owner of a token.
    fn get_owner(&self, token_id: &TokenId) -> ContractResult<&Address> {
        self.token_owners.get(token_id).ok_or(ContractError::NoTokenWithThisId)
    }

    /// Check if an address is the current owner of a token, results in an error
    /// if no token exists with `token_id`.
    fn is_owner(&self, address: &Address, token_id: &TokenId) -> ContractResult<bool> {
        let owner = self.get_owner(token_id)?;
        Ok(address == owner)
    }

    /// Get the approve of a token.
    fn get_approved(&self, token_id: &TokenId) -> Option<&Address> {
        self.token_approvals.get(token_id)
    }

    /// Check is an address is approved to transfer a specific token.
    fn is_approved(&self, address: &Address, token_id: &TokenId) -> bool {
        if let Some(approval) = self.token_approvals.get(token_id) {
            address == approval
        } else {
            false
        }
    }

    /// Check is an address is an operator of a specific owner address.
    fn is_operator(&self, address: &Address, owner: &Address) -> bool {
        if let Some(operators) = self.owner_operators.get(owner) {
            operators.contains(address)
        } else {
            false
        }
    }

    /// Transfer ownership of a token from one address to another, failing if
    /// token does not exist or if the `from` address is not the current owner.
    /// Removes any approvals on this specific token.
    fn transfer(&mut self, from: &Address, to: &Address, token_id: &TokenId) -> ContractResult<()> {
        if let Some(previous_owner) = self.token_owners.insert(*token_id, *to) {
            ensure!(previous_owner == *from, ContractError::FromIsNotTheOwner)
        } else {
            bail!(ContractError::NoTokenWithThisId)
        }
        self.token_approvals.remove(token_id);
        Ok(())
    }

    /// Approve an address to transfer a specific token on the owners behalf.
    /// If `approved` is None: Remove a previously approved address.
    fn approve(&mut self, approved: &Option<Address>, token_id: &TokenId) {
        if let Some(approved) = approved {
            self.token_approvals.insert(*token_id, *approved);
        } else {
            self.token_approvals.remove(token_id);
        }
    }

    /// Enable/Disable an address as an operator of the owner address
    fn approval_for_all(&mut self, owner: &Address, operator: &Address, approved: bool) {
        if let Some(operators) = self.owner_operators.get_mut(owner) {
            if approved {
                operators.insert(*operator);
            } else {
                operators.remove(operator);
            }
        } else if approved {
            let mut operators = Set::default();
            operators.insert(*operator);
            self.owner_operators.insert(*owner, operators);
        }
    }
}

// Contract functions

/// Initialize contract instance with a number of tokens all owned by the
/// invoker.
/// Note: Does not produce any `Transfer` events
#[init(contract = "erc721", parameter = "Tokens")]
fn contract_init(ctx: &impl HasInitContext) -> InitResult<State> {
    let tokens: Tokens = ctx.parameter_cursor().get()?;
    let invoker = ctx.init_origin();
    let state = State::new(tokens, Address::Account(invoker));
    Ok(state)
}

/// Transfer a token from one address to another and logs a `Transfer` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The sender is not: the owner of the token, or approved for this specific
///   token or an operator for the owner.
/// - The `token_id` does not exist.
/// - The token is not owned by the `from`.
///
/// Note: It differs from `transferFrom` only when transferring to a contract
/// instance, where it will ensure to call the contract function specified as
/// part of the parameter on the receiving instance and reject if the receiving
/// instance rejects.
#[receive(
    contract = "erc721",
    name = "safeTransferFrom",
    parameter = "SafeTransferFromParams",
    enable_logger
)]
fn contract_safe_transfer_from<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ContractResult<A> {
    // Does the actual transfer, checks the sender is authorized, mutates the state
    // and logs the Transfer event.
    let params = transfer_from(ctx, logger, state)?;

    if let Address::Contract(receiving_contract) = params.to {
        let parameter = OnERC721ReceivedParams {
            from:          params.from,
            token_id:      params.token_id,
            contract_name: OwnedContractName::new_unchecked("init_erc721".to_string()),
            data:          params.data,
        };
        let receive_name = params.receive_name.ok_or(ContractError::MissingContractReceiveName)?;

        Ok(send(&receiving_contract, receive_name.as_ref(), Amount::zero(), &parameter))
    } else {
        Ok(A::accept())
    }
}

/// Transfer a token from one address to another, but without triggering
/// `erc721.onERC721Received` on contract instances. See the contract function
/// `safeTransferFrom` for more.
#[receive(
    contract = "erc721",
    name = "transferFrom",
    parameter = "SafeTransferFromParams",
    enable_logger
)]
fn contract_transfer_from<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ContractResult<A> {
    // Does the actual transfer, checks the sender is authorized, mutates the state
    // and logs the Transfer event.
    transfer_from(ctx, logger, state)?;
    Ok(A::accept())
}

/// Helper function, ensures the sender is authorized, then transfers ownership
/// of a token and logs the transfer event.
fn transfer_from(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ContractResult<SafeTransferFromParams> {
    let params: SafeTransferFromParams = ctx.parameter_cursor().get()?;
    let sender = ctx.sender();
    ensure!(
        state.is_owner(&sender, &params.token_id)?
            || state.is_approved(&sender, &params.token_id)
            || state.is_operator(&sender, &params.from),
        ContractError::Unauthorized
    );
    state.transfer(&params.from, &params.to, &params.token_id)?;
    logger.log(&Event::Transfer {
        from:     params.from,
        to:       params.to,
        token_id: params.token_id,
    })?;
    Ok(params)
}

/// Approve some optional address to transfer a specified token. If no address
/// is sent, the previously approved address is removed if any.
/// Only one address per token can be approved.
/// An approval is removed if the token is transferred.
/// Logs an `Approve` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The sender is not: the owner of the token or an operator for the owner.
/// - The `token_id` does not exist.
#[receive(contract = "erc721", name = "approve", parameter = "ApproveParams", enable_logger)]
fn contract_approve<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ContractResult<A> {
    let params: ApproveParams = ctx.parameter_cursor().get()?;
    let sender = ctx.sender();
    let owner = *state.get_owner(&params.token_id)?;

    if let Some(approved) = params.approved {
        ensure!(owner != approved, ContractError::ApprovedIsOwner);
    }
    ensure!(sender == owner || state.is_operator(&sender, &owner), ContractError::Unauthorized);

    state.approve(&params.approved, &params.token_id);

    logger.log(&Event::Approval {
        owner,
        approved: params.approved,
        token_id: params.token_id,
    })?;

    Ok(A::accept())
}

/// Enable or disable some address as an operator of the address of the sender.
/// Logs an `ApproveForAll` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - The operator address is the same as the sender address.
#[receive(
    contract = "erc721",
    name = "setApprovalForAll",
    parameter = "ApproveForAllParams",
    enable_logger
)]
fn contract_set_approval_for_all<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ContractResult<A> {
    let params: ApproveForAllParams = ctx.parameter_cursor().get()?;

    let sender = ctx.sender();

    // No reason to be an operator yourself
    ensure!(params.operator != sender, ContractError::OperatorIsSender);

    state.approval_for_all(&sender, &params.operator, params.approved);

    logger.log(&Event::ApprovalForAll {
        owner:    sender,
        operator: params.operator,
        approved: params.approved,
    })?;

    Ok(A::accept())
}

/// Optional contract function called when a token is transferred to an instance
/// of this contract. The parameter include a `data` field which can be used to
/// implement some arbitrary functionality. In this example we choose not to use
/// it, and define the function to forward any transfers to the owner of the
/// contract instance.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Sender is not a contract.
/// - `safeTransferFrom` to instance owner rejects
#[receive(contract = "erc721", name = "onERC721Received")]
fn contract_on_erc721_received<A: HasActions>(
    ctx: &impl HasReceiveContext,
    _state: &mut State,
) -> ContractResult<A> {
    let params: OnERC721ReceivedParams = ctx.parameter_cursor().get()?;

    let sender = if let Address::Contract(contract) = ctx.sender() {
        contract
    } else {
        bail!(ContractError::ContractOnly)
    };

    let parameter = SafeTransferFromParams {
        from:         Address::Contract(ctx.self_address()),
        to:           Address::Account(ctx.invoker()),
        token_id:     params.token_id,
        receive_name: None,
        data:         vec![],
    };

    let mut receive_name_string =
        params.contract_name.contract_name().ok_or(ContractError::InvalidContractName)?.to_owned();
    receive_name_string.push_str(".safeTransferFrom");
    let receive_name = ReceiveName::new_unchecked(&receive_name_string);

    let action = send(&sender, receive_name, Amount::zero(), &parameter);

    Ok(action)
}

/// Get the number of tokens owned by a given address and callback contract
/// function on sender with the result. Should only be called by other smart
/// contracts.
///
/// It rejects if:
/// - Sender is not a contract.
/// - It fails to parse the parameter.
/// - Callback with result rejects.
#[receive(contract = "erc721", name = "balanceOf")]
fn contract_balance_of<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &State,
) -> ContractResult<A> {
    let sender = if let Address::Contract(contract) = ctx.sender() {
        contract
    } else {
        bail!(ContractError::ContractOnly)
    };

    let params: BalanceOfParams = ctx.parameter_cursor().get()?;
    let balance = state.balance(&params.owner);

    Ok(send(&sender, params.callback.as_ref(), Amount::zero(), &balance))
}

/// Get the address of the current owner of a given tokenId and callback with
/// the result to the sender. Should only be called by other smart contracts.
///
/// It rejects if:
/// - Sender is not a contract.
/// - It fails to parse the parameter.
/// - The token id does not exist.
/// - Callback with result rejects.
#[receive(contract = "erc721", name = "ownerOf")]
fn contract_owner_of<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &State,
) -> ContractResult<A> {
    let sender = if let Address::Contract(contract) = ctx.sender() {
        contract
    } else {
        bail!(ContractError::ContractOnly)
    };

    let params: OwnerOfParams = ctx.parameter_cursor().get()?;
    let owner = state.get_owner(&params.token_id)?;

    Ok(send(&sender, params.callback.as_ref(), Amount::zero(), owner))
}

/// Get the address of the current address approved for a given tokenId and
/// callback with the result to the sender. The result is 0u8 (None) if no
/// address is approved for this token or if the tokenid does not exist. The
/// result is 1u8 followed by the address approved for the token ID. Should only
/// be called by other smart contracts.
///
/// It rejects if:
/// - Sender is not a contract.
/// - It fails to parse the parameter.
/// - Callback with result rejects.
#[receive(contract = "erc721", name = "getApproved")]
fn contract_get_approved<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &State,
) -> ContractResult<A> {
    let sender = if let Address::Contract(contract) = ctx.sender() {
        contract
    } else {
        bail!(ContractError::ContractOnly)
    };

    let params: GetApprovedParams = ctx.parameter_cursor().get()?;
    let approved = state.get_approved(&params.token_id).map(|n| n.to_owned());

    Ok(send(&sender, params.callback.as_ref(), Amount::zero(), &approved))
}

/// Check if a given address is enabled as an operator for another given address
/// and callback with the result to the sender. The result is 0u8 (false) if the
/// address is not an operator otherwise it will result in 1u8 (true).
/// Should only be called by other smart contracts.
///
/// It rejects if:
/// - Sender is not a contract.
/// - It fails to parse the parameter.
/// - Callback with result rejects.
#[receive(contract = "erc721", name = "isApprovedForAll")]
fn contract_is_approved_for_all<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &State,
) -> ContractResult<A> {
    let sender = if let Address::Contract(contract) = ctx.sender() {
        contract
    } else {
        bail!(ContractError::ContractOnly)
    };

    let params: IsApprovedForAllParams = ctx.parameter_cursor().get()?;
    let is_operator = state.is_operator(&params.operator, &params.owner);

    Ok(send(&sender, params.callback.as_ref(), Amount::zero(), &is_operator))
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
    const TOKEN_ID: TokenId = 0;

    /// Test helper function which creates a contract state with one token with
    /// id `TOKEN_ID` owned by `ADDRESS_0`
    fn initial_state() -> State {
        let mut tokens: Tokens = Set::default();
        tokens.insert(TOKEN_ID);
        State::new(tokens, ADDRESS_0)
    }

    /// Test initialization succeeds, with no one approved and no operators from
    /// start.
    /// The initial tokens are owned by the sender.
    #[concordium_test]
    fn test_init() {
        let mut ctx = InitContextTest::empty();
        ctx.set_init_origin(ACCOUNT_0);

        let mut tokens: Tokens = Set::default();
        tokens.insert(TOKEN_ID);

        let parameter_bytes = to_bytes(&tokens);
        ctx.set_parameter(&parameter_bytes);

        let result = contract_init(&ctx);

        let state = result.expect_report("Contract initialization failed");

        claim_eq!(state.token_approvals.len(), 0, "No token approvals at initialization");
        claim_eq!(state.owner_operators.len(), 0, "No operators at initialization");
        claim_eq!(state.token_owners.len(), 1, "Initial tokens are stored in the state");
        let token_owner =
            *state.token_owners.get(&TOKEN_ID).expect_report("Token is expected to exist");
        claim_eq!(token_owner, ADDRESS_0, "Initial token is owned by the sender");
    }

    /// Test transfer succeeds when sender owns token.
    #[concordium_test]
    fn test_transfer() {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(ADDRESS_0);

        let mut state = initial_state();

        let parameter = SafeTransferFromParams {
            from:         ADDRESS_0,
            to:           ADDRESS_1,
            token_id:     TOKEN_ID,
            receive_name: None,
            data:         vec![],
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();

        let actions: ActionsTree = contract_safe_transfer_from(&ctx, &mut logger, &mut state)
            .expect_report("Failed NFT transfer");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        let owner = state.get_owner(&TOKEN_ID).expect_report("No token with id");
        claim_eq!(owner, &ADDRESS_1, "Ownership should be transferred");

        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Event::Transfer {
                from:     ADDRESS_0,
                to:       ADDRESS_1,
                token_id: TOKEN_ID,
            }),
            "Incorrect event emitted"
        )
    }

    /// Test transfer token fails, when sender is not the owner, not approved
    /// and not an operator of the owner.
    #[concordium_test]
    fn test_transfer_not_authorized() {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(ADDRESS_1);

        let mut state = initial_state();

        let parameter = SafeTransferFromParams {
            from:         ADDRESS_0,
            to:           ADDRESS_1,
            token_id:     TOKEN_ID,
            receive_name: None,
            data:         vec![],
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();

        let result: ContractResult<ActionsTree> =
            contract_safe_transfer_from(&ctx, &mut logger, &mut state);
        let err = result.expect_err_report("Expected to fail");
        claim_eq!(err, ContractError::Unauthorized, "Error is expected to be Unauthorized")
    }

    /// Test transfer succeeds when sender is not the owner, but is approved by
    /// the owner.
    #[concordium_test]
    fn test_approved_transfer() {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(ADDRESS_1);

        let mut state = initial_state();
        state.approve(&Some(ADDRESS_1), &TOKEN_ID);

        let parameter = SafeTransferFromParams {
            from:         ADDRESS_0,
            to:           ADDRESS_1,
            token_id:     TOKEN_ID,
            receive_name: None,
            data:         vec![],
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();

        let actions: ActionsTree = contract_safe_transfer_from(&ctx, &mut logger, &mut state)
            .expect_report("Failed NFT transfer");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        let owner = state.get_owner(&TOKEN_ID).expect_report("No token with id");
        claim_eq!(owner, &ADDRESS_1, "Ownership should be transferred");
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Event::Transfer {
                from:     ADDRESS_0,
                to:       ADDRESS_1,
                token_id: TOKEN_ID,
            }),
            "Incorrect event emitted"
        )
    }

    /// Test transfer succeeds when sender is not the owner, but is an operator
    /// of the owner.
    #[concordium_test]
    fn test_operator_transfer() {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(ADDRESS_1);

        let mut state = initial_state();
        state.approval_for_all(&ADDRESS_0, &ADDRESS_1, true);

        let parameter = SafeTransferFromParams {
            from:         ADDRESS_0,
            to:           ADDRESS_1,
            token_id:     TOKEN_ID,
            receive_name: None,
            data:         vec![],
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();

        let actions: ActionsTree = contract_safe_transfer_from(&ctx, &mut logger, &mut state)
            .expect_report("Failed NFT transfer");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        let owner = state.get_owner(&TOKEN_ID).expect_report("No token with id");
        claim_eq!(owner, &ADDRESS_1, "Ownership should be transferred");
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Event::Transfer {
                from:     ADDRESS_0,
                to:       ADDRESS_1,
                token_id: TOKEN_ID,
            }),
            "Incorrect event emitted"
        )
    }

    /// Test approve succeeds when sender is owner
    #[concordium_test]
    fn test_approve() {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(ADDRESS_0);

        let mut state = initial_state();

        let parameter = ApproveParams {
            approved: Some(ADDRESS_1),
            token_id: TOKEN_ID,
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();

        let actions: ActionsTree = contract_approve(&ctx, &mut logger, &mut state)
            .expect_report("Failed valid approve call");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        let owner = state.get_owner(&TOKEN_ID).expect_report("No token with id");
        claim_eq!(owner, &ADDRESS_0, "Ownership should not be transferred");
        claim!(state.is_approved(&ADDRESS_1, &TOKEN_ID), "Account should be approved");
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Event::Approval {
                owner:    ADDRESS_0,
                approved: Some(ADDRESS_1),
                token_id: TOKEN_ID,
            }),
            "Incorrect event emitted"
        )
    }

    /// Test approve fails when sender is not the owner and not an operator of
    /// the owner.
    #[concordium_test]
    fn test_approve_unauthorized() {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(ADDRESS_1);

        let mut state = initial_state();

        let parameter = ApproveParams {
            approved: Some(ADDRESS_1),
            token_id: TOKEN_ID,
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();

        let result: ContractResult<ActionsTree> = contract_approve(&ctx, &mut logger, &mut state);
        let err = result.expect_err_report("Expected to fail");
        claim_eq!(err, ContractError::Unauthorized, "Error is expected to be Unauthorized");
    }

    /// Test approve succeeds when sender is not the owner, but is an operator
    /// of the owner.
    #[concordium_test]
    fn test_operator_approve() {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(ADDRESS_1);

        let mut state = initial_state();
        state.approval_for_all(&ADDRESS_0, &ADDRESS_1, true);

        let parameter = ApproveParams {
            approved: Some(ADDRESS_1),
            token_id: TOKEN_ID,
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();

        let actions: ActionsTree = contract_approve(&ctx, &mut logger, &mut state)
            .expect_report("Failed valid approve call");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        let owner = state.get_owner(&TOKEN_ID).expect_report("No token with id");
        claim_eq!(owner, &ADDRESS_0, "Ownership should not be transferred");
        claim!(state.is_approved(&ADDRESS_1, &TOKEN_ID), "Account should be approved");
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Event::Approval {
                owner:    ADDRESS_0,
                approved: Some(ADDRESS_1),
                token_id: TOKEN_ID,
            }),
            "Incorrect event emitted"
        )
    }

    /// Test approve_for_all succeeds
    #[concordium_test]
    fn test_set_approve_for_all() {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(ADDRESS_0);

        let mut state = initial_state();

        let parameter = ApproveForAllParams {
            operator: ADDRESS_1,
            approved: true,
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();

        let actions: ActionsTree = contract_set_approval_for_all(&ctx, &mut logger, &mut state)
            .expect_report("Failed valid approve call");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        let owner = state.get_owner(&TOKEN_ID).expect_report("No token with id");
        claim_eq!(owner, &ADDRESS_0, "Ownership should not be transferred");
        claim!(state.is_operator(&ADDRESS_1, &ADDRESS_0), "Account should be approved");
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Event::ApprovalForAll {
                owner:    ADDRESS_0,
                operator: ADDRESS_1,
                approved: true,
            }),
            "Incorrect event emitted"
        )
    }
}
