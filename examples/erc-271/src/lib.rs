#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::{collections::*, *};

/*
 * An implementation of the ERC-271 Non-Fungible Token(NFT) Standard popular
 * on the Ethereum blockchain.
 *
 * An smart contract instance represents a number of NFTs and tracks
 * ownership of each. It allows other accounts to transfer a certain amount
 * from ones account.
 *
 * https://eips.ethereum.org/EIPS/eip-721
 *
 * Instead of getter functions the information can be read directly from the
 * contract state directly. Events can be tracked in the log.
 */

// Types

/// Token Identifier, which combine with the address of the contract instance,
/// forms the unique identifier of an NFT. The specification requires a u256,
/// but for efficiency we use u64, which is expected to be sufficient for most
/// cases.
type TokenId = u64;

/// Token metadata
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
struct TokenMetadata {
    /// Name of the token, encoded as UTF8
    name:   Vec<u8>,
    /// Symbol of the token, encoded as UTF8
    symbol: Vec<u8>,
}

type Tokens = BTreeMap<TokenId, TokenMetadata>;

#[contract_state(contract = "erc271")]
#[derive(Debug, Serialize, SchemaType)]
pub struct State {
    tokens:          Tokens,
    /// Map from a token id to the owning account address
    /// Every token must be an entry in this map.
    token_owners:    BTreeMap<TokenId, AccountAddress>,
    /// Map from a token id to an account which are allowed to transfer this
    /// token on the owners behalf
    /// Only tokens with approvals have entries in this map.
    token_approvals: BTreeMap<TokenId, AccountAddress>,
    /// Map from an account to operator accounts, which can transfer any token
    /// on their behalf.
    /// Only accounts with operators have entries in this map.
    owner_operators: BTreeMap<AccountAddress, BTreeSet<AccountAddress>>,
}

// Event printed in the log
#[derive(Debug, Serialize)]
enum Event {
    /// Ownership of NFT changed
    Transfer {
        from:     AccountAddress,
        to:       AccountAddress,
        token_id: TokenId,
    },
    /// Approved transfer of NFT, where `approved` = None means no one is
    /// approved.
    Approval {
        owner:    AccountAddress,
        approved: Option<AccountAddress>,
        token_id: TokenId,
    },
    /// Change to whether an operator can manage all NFTs of the owner
    ApprovalForAll {
        owner:    AccountAddress,
        operator: AccountAddress,
        approved: bool,
    },
}

// Contract Function Parameters

#[derive(Serialize, SchemaType)]
struct SafeTransferFromParams {
    from:     AccountAddress,
    to:       AccountAddress,
    token_id: TokenId,
}

#[derive(Serialize, SchemaType)]
struct ApproveParams {
    approved: Option<AccountAddress>,
    token_id: TokenId,
}

#[derive(Serialize, SchemaType)]
struct ApproveForAllParams {
    operator: AccountAddress,
    approved: bool,
}

#[derive(Debug, PartialEq, Eq, Reject)]
enum ContractError {
    /// Failed parsing the parameter
    ParseParams,
    LogFull,
    LogMalformed,
    NoTokenWithThisId,
    InvalidTransfer,
    Unauthorized,
    AccountSenderOnly,
    ApprovedIsOwner,
    OperatorIsSender,
}

impl From<LogError> for ContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

impl From<ParseError> for ContractError {
    fn from(_: ParseError) -> Self { ContractError::ParseParams }
}

impl State {
    /// Creates a new state with a number of tokens, all owned by the invoker.
    fn new(tokens: Tokens, owner: AccountAddress) -> Self {
        let mut token_owners = BTreeMap::new();
        for &token_id in tokens.keys() {
            token_owners.insert(token_id, owner);
        }

        State {
            tokens,
            token_owners,
            token_approvals: BTreeMap::new(),
            owner_operators: BTreeMap::new(),
        }
    }

    /// Get the current owner of a token
    fn get_owner(&self, token_id: &TokenId) -> Result<&AccountAddress, ContractError> {
        self.token_owners.get(token_id).ok_or(ContractError::NoTokenWithThisId)
    }

    fn is_owner(&self, sender: &AccountAddress, token_id: &TokenId) -> bool {
        if let Some(owner) = self.token_owners.get(token_id) {
            return sender == owner;
        }
        false
    }

    fn is_approved(&self, sender: &AccountAddress, token_id: &TokenId) -> bool {
        if let Some(approval) = self.token_approvals.get(token_id) {
            return sender == approval;
        }
        false
    }

    fn is_operator(&self, sender: &AccountAddress, owner: &AccountAddress) -> bool {
        if let Some(operators) = self.owner_operators.get(owner) {
            return operators.contains(sender);
        }
        false
    }

    fn transfer(
        &mut self,
        token_id: &TokenId,
        from: &AccountAddress,
        to: &AccountAddress,
    ) -> Result<(), ContractError> {
        if let Some(previous_owner) = self.token_owners.insert(*token_id, *to) {
            ensure!(previous_owner == *from, ContractError::InvalidTransfer)
        } else {
            bail!(ContractError::NoTokenWithThisId)
        }
        self.token_approvals.remove(token_id);
        Ok(())
    }

    fn approve(&mut self, token_id: &TokenId, approved: &Option<AccountAddress>) {
        if let Some(approved) = approved {
            self.token_approvals.insert(*token_id, *approved);
        } else {
            self.token_approvals.remove(token_id);
        }
    }

    fn approval_for_all(
        &mut self,
        owner: &AccountAddress,
        operator: &AccountAddress,
        approved: bool,
    ) {
        if let Some(operators) = self.owner_operators.get_mut(owner) {
            if approved {
                operators.insert(*operator);
            } else {
                operators.remove(operator);
            }
        } else {
            if approved {
                let mut operators = BTreeSet::new();
                operators.insert(*operator);
                self.owner_operators.insert(*owner, operators);
            }
        }
    }
}

// Contract

#[init(contract = "erc271", parameter = "Tokens")]
fn contract_init(ctx: &impl HasInitContext) -> InitResult<State> {
    let tokens: Tokens = ctx.parameter_cursor().get()?;
    let invoker = ctx.init_origin();
    Ok(State::new(tokens, invoker))
}

#[receive(
    contract = "erc271",
    name = "safeTransferFrom",
    parameters = "SafeTransferFromParams",
    enable_logger
)]
fn contract_safe_transfer_from<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> Result<A, ContractError> {
    let params: SafeTransferFromParams = ctx.parameter_cursor().get()?;
    let sender = if let Address::Account(account) = ctx.sender() {
        account
    } else {
        bail!(ContractError::AccountSenderOnly)
    };

    ensure!(
        state.is_owner(&sender, &params.token_id)
            || state.is_approved(&sender, &params.token_id)
            || state.is_operator(&sender, &params.from),
        ContractError::Unauthorized
    );
    state.transfer(&params.token_id, &params.from, &params.to)?;
    logger.log(&Event::Transfer {
        from:     params.from,
        to:       params.to,
        token_id: params.token_id,
    })?;

    Ok(A::accept())
}

#[receive(contract = "erc271", name = "transferFrom", enable_logger)]
fn contract_transfer_from<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> Result<A, ContractError> {
    contract_safe_transfer_from(ctx, logger, state)
}

#[receive(contract = "erc271", name = "approve", enable_logger)]
fn contract_approve<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> Result<A, ContractError> {
    let params: ApproveParams = ctx.parameter_cursor().get()?;

    let sender = if let Address::Account(account) = ctx.sender() {
        account
    } else {
        bail!(ContractError::AccountSenderOnly)
    };

    let owner = *state.get_owner(&params.token_id)?;

    if let Some(approved) = params.approved {
        ensure!(owner != approved, ContractError::ApprovedIsOwner);
    }
    ensure!(sender == owner || state.is_operator(&sender, &owner), ContractError::Unauthorized);

    state.approve(&params.token_id, &params.approved);

    logger.log(&Event::Approval {
        owner,
        approved: params.approved,
        token_id: params.token_id,
    })?;

    Ok(A::accept())
}

#[receive(contract = "erc271", name = "setApprovalForAll", enable_logger)]
fn contract_set_approval_for_all<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> Result<A, ContractError> {
    let params: ApproveForAllParams = ctx.parameter_cursor().get()?;

    let sender = if let Address::Account(account) = ctx.sender() {
        account
    } else {
        bail!(ContractError::AccountSenderOnly)
    };

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

// Tests

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    const ACCOUNT_0: AccountAddress = AccountAddress([0u8; 32]);
    const ACCOUNT_1: AccountAddress = AccountAddress([1u8; 32]);
    const TOKEN_ID: TokenId = 0;

    fn initial_state() -> State {
        let mut tokens: Tokens = BTreeMap::new();
        tokens.insert(TOKEN_ID, TokenMetadata {
            name:   b"MyToken".to_vec(),
            symbol: b"MT".to_vec(),
        });

        State::new(tokens, ACCOUNT_0)
    }

    #[concordium_test]
    fn test_init() {
        let mut ctx = InitContextTest::empty();
        ctx.set_init_origin(ACCOUNT_0);

        let mut tokens: Tokens = BTreeMap::new();
        tokens.insert(0, TokenMetadata {
            name:   b"MyToken".to_vec(),
            symbol: b"MT".to_vec(),
        });

        let parameter_bytes = to_bytes(&tokens);
        ctx.set_parameter(&parameter_bytes);

        let result = contract_init(&ctx);

        let state = result.expect_report("Contract initialization failed");

        claim_eq!(state.token_approvals.len(), 0, "No token approvals at initialization");
        claim_eq!(state.owner_operators.len(), 0, "No operators at initialization");
        claim_eq!(state.tokens, tokens, "Initial tokens are stored in the state");
    }

    #[concordium_test]
    fn test_transfer() {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(Address::Account(ACCOUNT_0));

        let mut state = initial_state();

        let parameter = SafeTransferFromParams {
            from:     ACCOUNT_0,
            to:       ACCOUNT_1,
            token_id: TOKEN_ID,
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();

        let actions: ActionsTree = contract_safe_transfer_from(&ctx, &mut logger, &mut state)
            .expect_report("Failed NFT transfer");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        let owner = state.get_owner(&TOKEN_ID).expect_report("No token with id");
        claim_eq!(owner, &ACCOUNT_1, "Ownership should be transferred");

        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Event::Transfer {
                from:     ACCOUNT_0,
                to:       ACCOUNT_1,
                token_id: TOKEN_ID,
            }),
            "Incorrect event emitted"
        )
    }

    #[concordium_test]
    fn test_transfer_not_authorized() {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(Address::Account(ACCOUNT_1));

        let mut state = initial_state();

        let parameter = SafeTransferFromParams {
            from:     ACCOUNT_0,
            to:       ACCOUNT_1,
            token_id: TOKEN_ID,
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();

        let result: Result<ActionsTree, _> =
            contract_safe_transfer_from(&ctx, &mut logger, &mut state);
        let err = result.expect_err_report("Expected to fail");
        claim_eq!(err, ContractError::Unauthorized, "Error is expected to be Unauthorized")
    }

    #[concordium_test]
    fn test_approved_transfer() {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(Address::Account(ACCOUNT_1));

        let mut state = initial_state();
        state.approve(&TOKEN_ID, &Some(ACCOUNT_1));

        let parameter = SafeTransferFromParams {
            from:     ACCOUNT_0,
            to:       ACCOUNT_1,
            token_id: TOKEN_ID,
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();

        let actions: ActionsTree = contract_safe_transfer_from(&ctx, &mut logger, &mut state)
            .expect_report("Failed NFT transfer");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        let owner = state.get_owner(&TOKEN_ID).expect_report("No token with id");
        claim_eq!(owner, &ACCOUNT_1, "Ownership should be transferred");
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Event::Transfer {
                from:     ACCOUNT_0,
                to:       ACCOUNT_1,
                token_id: TOKEN_ID,
            }),
            "Incorrect event emitted"
        )
    }

    #[concordium_test]
    fn test_operator_transfer() {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(Address::Account(ACCOUNT_1));

        let mut tokens: Tokens = BTreeMap::new();
        let token_id = 0;
        tokens.insert(token_id, TokenMetadata {
            name:   b"MyToken".to_vec(),
            symbol: b"MT".to_vec(),
        });

        let mut state = State::new(tokens, ACCOUNT_0);
        state.approval_for_all(&ACCOUNT_0, &ACCOUNT_1, true);

        let parameter = SafeTransferFromParams {
            from: ACCOUNT_0,
            to: ACCOUNT_1,
            token_id,
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();

        let actions: ActionsTree = contract_safe_transfer_from(&ctx, &mut logger, &mut state)
            .expect_report("Failed NFT transfer");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        let owner = state.get_owner(&TOKEN_ID).expect_report("No token with id");
        claim_eq!(owner, &ACCOUNT_1, "Ownership should be transferred");
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Event::Transfer {
                from: ACCOUNT_0,
                to: ACCOUNT_1,
                token_id
            }),
            "Incorrect event emitted"
        )
    }

    #[concordium_test]
    fn test_approve() {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(Address::Account(ACCOUNT_0));

        let mut tokens: Tokens = BTreeMap::new();
        let token_id = 0;
        tokens.insert(token_id, TokenMetadata {
            name:   b"MyToken".to_vec(),
            symbol: b"MT".to_vec(),
        });

        let mut state = State::new(tokens, ACCOUNT_0);

        let parameter = ApproveParams {
            approved: Some(ACCOUNT_1),
            token_id,
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();

        let actions: ActionsTree = contract_approve(&ctx, &mut logger, &mut state)
            .expect_report("Failed valid approve call");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        let owner = state.get_owner(&TOKEN_ID).expect_report("No token with id");
        claim_eq!(owner, &ACCOUNT_0, "Ownership should not be transferred");
        claim!(state.is_approved(&ACCOUNT_1, &TOKEN_ID), "Account should be approved");
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Event::Approval {
                owner: ACCOUNT_0,
                approved: Some(ACCOUNT_1),
                token_id
            }),
            "Incorrect event emitted"
        )
    }

    #[concordium_test]
    fn test_set_approve_for_all() {
        let mut ctx = ReceiveContextTest::empty();
        ctx.set_sender(Address::Account(ACCOUNT_0));

        let mut tokens: Tokens = BTreeMap::new();
        let token_id = 0;
        tokens.insert(token_id, TokenMetadata {
            name:   b"MyToken".to_vec(),
            symbol: b"MT".to_vec(),
        });

        let mut state = State::new(tokens, ACCOUNT_0);

        let parameter = ApproveForAllParams {
            operator: ACCOUNT_1,
            approved: true,
        };

        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = LogRecorder::init();

        let actions: ActionsTree = contract_set_approval_for_all(&ctx, &mut logger, &mut state)
            .expect_report("Failed valid approve call");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");

        let owner = state.get_owner(&TOKEN_ID).expect_report("No token with id");
        claim_eq!(owner, &ACCOUNT_0, "Ownership should not be transferred");
        claim!(state.is_operator(&ACCOUNT_1, &ACCOUNT_0), "Account should be approved");
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Event::ApprovalForAll {
                owner:    ACCOUNT_0,
                operator: ACCOUNT_1,
                approved: true,
            }),
            "Incorrect event emitted"
        )
    }
}
