use concordium_cis1::*;
use concordium_std::*;

type TokenId = TokenIdU8;
type TokenCount = u64;

#[derive(Serial)]
enum Keys {
    SimpleMap,
    TokenState,
    TokenCount,
}

#[derive(Serialize, SchemaType)]
struct MintParams {
    owner:       Address,
    token_id:    TokenId,
    token_count: TokenCount,
}

// With GATs (Generic Associated Types), we could avoid the _ parameter and do:
// init<State: HasContractStateHL> .. {
//    let simple_map: State::Map<u8,u8> = state.new_map();
// }

#[init(contract = "new-state", parameter = "MintParams")]
fn init(_ctx: &impl HasInitContext, state: &mut impl HasContractStateHL) -> InitResult<()> {
    let simple_map: StateMap<u8, u8, _> = state.new_map();
    state.insert(Keys::SimpleMap, simple_map);

    let token_state: StateMap<Address, StateMap<TokenId, TokenCount, _>, _> = state.new_map();
    state.insert(Keys::TokenState, token_state);
    state.insert(Keys::TokenCount, 0u64);
    Ok(())
}

#[receive(contract = "new-state", name = "mint", parameter = "MintParams")]
fn receive<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut impl HasContractStateHL,
) -> ReceiveResult<A> {
    let params: MintParams = ctx.parameter_cursor().get()?;

    let mut simple_map: StateMap<u8, u8, _> = state.get(Keys::SimpleMap).unwrap_abort()?;

    // Inserts value in state
    let _ = simple_map.insert(0, 1);
    // Inserts value in state
    let _ = simple_map.insert(1, 2);

    let old_token_count: u64 = state.get(Keys::TokenCount).unwrap_abort()?;
    state.insert(Keys::TokenCount, old_token_count + params.token_count);

    let mut token_state: StateMap<Address, StateMap<TokenId, TokenCount, _>, _> =
        state.get(Keys::TokenState).unwrap_abort()?;

    token_state
        .entry(params.owner)?
        .and_modify::<_, Reject>(|owner_map| {
            owner_map
                .entry(params.token_id)?
                .and_modify::<_, Reject>(|current_count| {
                    *current_count += params.token_count;
                    Ok(())
                })?
                .or_insert(params.token_count);
            Ok(())
        })?
        .or_insert({
            let mut owner_map = state.new_map();
            let _old_value = owner_map.insert(params.token_id, params.token_count);
            owner_map
        });

    Ok(A::accept())
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    #[concordium_test]
    fn test_init() {
        let ctx = InitContextTest::empty();

        let mut state = ContractStateHL::open(ContractStateLLTest::new());

        init(&ctx, &mut state).expect_report("Init failed");

        // This doesn't check that the map type is correct, only that a map has been
        // created with the given key and that it is empty.
        claim!(state
            .get::<_, StateMap<u8, u8, _>>(Keys::SimpleMap)
            .unwrap_abort()
            .unwrap_abort()
            .is_empty());

        claim!(state
            .get::<_, StateMap<Address, StateMap<TokenId, TokenCount, _>, _>>(Keys::TokenState)
            .unwrap_abort()
            .unwrap_abort()
            .is_empty());

        claim_eq!(state.get(Keys::TokenCount), Some(Ok(0u64)));
    }

    #[concordium_test]
    fn test_receive() {
        let mut ctx = ReceiveContextTest::empty();
        let owner = Address::Account(AccountAddress([0u8; 32]));
        let token_id = TokenIdU8(10);
        let expected_token_count = 100;
        let parameter_bytes = to_bytes(&MintParams {
            owner,
            token_id,
            token_count: expected_token_count,
        });
        ctx.set_parameter(&parameter_bytes);

        let mut state = ContractStateHL::open(ContractStateLLTest::new());

        // Set up initial state contents via init.
        init(&InitContextTest::empty(), &mut state).expect_report("Init failed");

        // Invoke receive.
        claim_eq!(receive(&ctx, &mut state), Ok(ActionsTree::accept()));

        // Token count should be 100.
        claim_eq!(state.get(Keys::TokenCount), Some(Ok(expected_token_count)));

        // Simple map should have (0, 1) and (1, 2).
        let simple_map: StateMap<u8, u8, _> =
            state.get(Keys::SimpleMap).unwrap_abort().unwrap_abort();
        claim_eq!(simple_map.get(0), Some(Ok(1)));
        claim_eq!(simple_map.get(1), Some(Ok(2)));

        // TokenState should have (owner, (10, 100))
        let token_state_map: StateMap<Address, StateMap<TokenId, TokenAmount, _>, _> =
            state.get(Keys::TokenState).unwrap_abort().unwrap_abort();
        claim_eq!(
            token_state_map.get(owner).unwrap_abort().unwrap_abort().get(token_id),
            Some(Ok(expected_token_count))
        )
    }
}
