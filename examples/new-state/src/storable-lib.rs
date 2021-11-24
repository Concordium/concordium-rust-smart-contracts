use concordium_cis1::*;
use concordium_std::*;

type TokenId = TokenIdU8;
type TokenCount = u8;

/// Stored as:
/// /token_count :: u8
/// /token_state/<address>/<token-id> :: u8
#[derive(SchemaType, Storable)]
struct State {
    token_count: Stored<TokenCount>,
    token_state: StateMap<Address, StateMap<TokenId, TokenCount>>,
}

#[init(contract = "storable-contract")]
fn init(_ctx: &impl HasInitContext) -> InitResult<State> {
    let initial_state = State {
        token_count: Stored(u8),
        token_state: StateMap::new(),
    };

    Ok(initial_state)
    // We call: initial_state.store("", "/")
}

#[derive(Serialize, SchemaType)]
struct MintParams {
    owner:       Address,
    token_id:    TokenId,
    token_count: TokenCount,
}

#[receive(contract = "storable-contract", name = "mint", parameter = "MintParams", enable_logger)]
fn receive_mint<A: HasActions>(
    ctx: &impl HasReceiveContext,
    logger: &mut impl HasLogger,
    state: &mut State,
) -> ReceiveResult<A> {
    let params: MintParams = ctx.parameter_cursor().get()?;

    // Just overwrite existing.
    state.token_state.insert(params.owner, StateMap::new().insert(params.token_id, token_count));

    let old_token_count = state.token_count.get()?;
    let new_token_count = state.token_count.update(|mut current| current += params.token_count)?;
    // state.token_count.sed(old_token_count + params.token_count)?;

    logger.log(format!("Increased token count: {} -> {}", old_token_count, new_token_count));

    Ok(A::accept())
}
