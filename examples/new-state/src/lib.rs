use std::{cell::RefCell, rc::Rc};

use concordium_cis1::*;
use concordium_std::*;

type TokenId = TokenIdU8;
type TokenCount = u8;

/// Stored as:
/// 0/next_collection_id :: u64
/// 1/token_count :: u8
/// 2(first collection index)/<address> => <map_index (3..n)>
/// 3..n maps/token_id => token_count :: u8
#[derive(SchemaType)]
struct State<S: HasContractStateLL + std::fmt::Debug> {
    token_state:        StateMap<Address, StateMap<TokenId, TokenCount, S>, S>,
    another_struct:     AnotherStruct<S>,
    total_tokens:       u64,
    boxed_total_tokens: StateBox<u64, S>,
}

struct AnotherStruct<S: HasContractStateLL> {
    a_set: StateSet<u8, S>,
}

impl<S> Persistable<S> for AnotherStruct<S>
where
    S: HasContractStateLL + std::fmt::Debug,
{
    fn store(self, prefix: &[u8], state_ll: Rc<RefCell<S>>) {
        let mut owned_prefix = prefix.to_vec();
        owned_prefix.push(0);
        self.a_set.store(&owned_prefix, state_ll)
    }

    fn load(prefix: &[u8], state_ll: Rc<RefCell<S>>) -> ParseResult<Self> {
        let mut owned_prefix = prefix.to_vec();
        owned_prefix.push(0);
        Ok(Self {
            a_set: StateSet::load(&owned_prefix, state_ll)?,
        })
    }
}

impl<S> Persistable<S> for State<S>
where
    S: HasContractStateLL + std::fmt::Debug,
{
    fn store(self, prefix: &[u8], state_ll: Rc<RefCell<S>>) {
        let mut owned_prefix = prefix.to_vec();

        owned_prefix.push(0);
        self.token_state.store(&owned_prefix, Rc::clone(&state_ll));
        owned_prefix.pop();

        owned_prefix.push(1);
        self.another_struct.store(&owned_prefix, Rc::clone(&state_ll));
        owned_prefix.pop();

        owned_prefix.push(2);
        self.total_tokens.store(&owned_prefix, Rc::clone(&state_ll));
        owned_prefix.pop();

        owned_prefix.push(3);
        self.boxed_total_tokens.store(&owned_prefix, state_ll);
    }

    fn load(prefix: &[u8], state_ll: Rc<RefCell<S>>) -> ParseResult<Self> {
        let mut owned_prefix = prefix.to_vec();

        owned_prefix.push(0);
        let token_state = StateMap::load(&owned_prefix, Rc::clone(&state_ll))?;
        owned_prefix.pop();

        owned_prefix.push(1);
        let another_struct = AnotherStruct::load(&owned_prefix, Rc::clone(&state_ll))?;
        owned_prefix.pop();

        owned_prefix.push(2);
        let total_tokens = u64::load(&owned_prefix, Rc::clone(&state_ll))?;
        owned_prefix.pop();

        owned_prefix.push(3);
        let boxed_total_tokens = StateBox::load(&owned_prefix, state_ll)?;
        owned_prefix.pop();

        Ok(Self {
            token_state,
            another_struct,
            total_tokens,
            boxed_total_tokens,
        })
    }
}

#[init(contract = "storable-contract")]
fn init<S: HasContractStateLL + std::fmt::Debug>(
    _ctx: &impl HasInitContext,
    allocator: &mut Allocator<S>,
) -> InitResult<((), State<S>)> {
    Ok(((), State {
        token_state:        allocator.new_map(),
        another_struct:     AnotherStruct {
            a_set: allocator.new_set(),
        },
        total_tokens:       0,
        boxed_total_tokens: allocator.new_box(0u64),
    }))
}

#[derive(Serialize, SchemaType)]
struct MintParams {
    owner:       Address,
    token_id:    TokenId,
    token_count: TokenCount,
}

#[receive(contract = "storable-contract", name = "mint", parameter = "MintParams")]
fn receive_mint<S: HasContractStateLL + std::fmt::Debug>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, ContractStateLLType = S>,
) -> ReceiveResult<()> {
    let params: MintParams = ctx.parameter_cursor().get()?;

    // Just overwrite existing.
    host.state()
        .token_state
        .entry(params.owner)
        .and_modify(|owner_map| {
            owner_map
                .entry(params.token_id)
                .and_modify(|current_count| {
                    *current_count += params.token_count;
                })
                .or_insert(params.token_count);
        })
        .or_insert({
            let mut owner_map = host.allocator().new_map();
            let _old_value = owner_map.insert(params.token_id, params.token_count);
            owner_map
        });

    host.state().another_struct.a_set.insert(42);

    // This won't be persisted. The change only occurs in memory.
    host.state().total_tokens += params.token_count as u64;

    // But this should be.
    host.state().boxed_total_tokens.update(|old_count| *old_count += params.token_count as u64);

    Ok(())
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    #[concordium_test]
    fn test_init() {
        let ctx = InitContextTest::empty();

        let state_ll = Rc::new(RefCell::new(ContractStateLLTest::new()));
        let mut allocator = Allocator::open(Rc::clone(&state_ll));

        let _state = init(&ctx, &mut allocator).expect("Init failed");
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

        let state_ll = Rc::new(RefCell::new(ContractStateLLTest::new()));
        let mut allocator = Allocator::open(Rc::clone(&state_ll));

        // Set up initial state contents via init.
        let (_rv, state_to_store) =
            init(&InitContextTest::empty(), &mut allocator).expect("Init failed");
        // This store invocation normally occurs in the code generated by the init
        // macro.
        state_to_store.store(&[], Rc::clone(&state_ll));

        // Then load the state, as it happens when calling receive.
        let state_for_rcv =
            State::load(&[], Rc::clone(&state_ll)).expect("Could not load all of state.");

        let mut host = HostTest::new_with_allocator(state_for_rcv, allocator);

        // Invoke receive.
        assert!(receive_mint(&ctx, &mut host).is_ok());

        // Reload the state to ensure that it was actually persisted (and not just
        // altered in memory).
        let state_reloaded = State::load(&[], state_ll).expect("Could not load all of state.");

        // Token count should be 100.
        assert_eq!(
            state_reloaded.token_state.get(owner).unwrap().get(token_id),
            Some(expected_token_count)
        );

        let mut a_set_iter = state_reloaded.another_struct.a_set.iter();
        assert_eq!(a_set_iter.next(), Some(42));
        assert_eq!(a_set_iter.next(), None);

        assert_eq!(state_reloaded.total_tokens, 0); // The bare u64 is not persisted.
                                                    // But the Boxed u64 is:
        assert_eq!(state_reloaded.boxed_total_tokens.get_copy(), 100);
    }
}
