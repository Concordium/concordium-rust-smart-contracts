use concordium_cis1::*;
use concordium_std::*;

type TokenId = TokenIdU8;
type TokenCount = u8;

#[derive(SchemaType)]
struct State<S> {
    token_state:        StateMap<Address, StateMap<TokenId, TokenCount, S>, S>,
    another_struct:     AnotherStruct<S>,
    total_tokens:       u64,
    boxed_total_tokens: StateBox<u64, S>,
}

struct AnotherStruct<S> {
    a_set: StateSet<u8, S>,
}

impl<S> Serial for State<S> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.token_state.serial(out)?;
        self.another_struct.serial(out)?;
        self.total_tokens.serial(out)?;
        self.boxed_total_tokens.serial(out)
    }
}

impl<S> Serial for AnotherStruct<S> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> { self.a_set.serial(out) }
}

impl<S> DeserialStateCtx<S> for State<S>
where
    S: HasContractStateLL,
{
    fn deserial_state_ctx<R: Read>(state: &S, source: &mut R) -> ParseResult<Self> {
        let token_state = DeserialStateCtx::deserial_state_ctx(state, source)?;
        let another_struct = DeserialStateCtx::deserial_state_ctx(state, source)?;
        let total_tokens = DeserialStateCtx::deserial_state_ctx(state, source)?;
        let boxed_total_tokens = DeserialStateCtx::deserial_state_ctx(state, source)?;
        Ok(Self {
            token_state,
            another_struct,
            total_tokens,
            boxed_total_tokens,
        })
    }
}

impl<S> DeserialStateCtx<S> for AnotherStruct<S>
where
    S: HasContractStateLL,
{
    fn deserial_state_ctx<R: Read>(state: &S, source: &mut R) -> ParseResult<Self> {
        Ok(Self {
            a_set: DeserialStateCtx::deserial_state_ctx(state, source)?,
        })
    }
}

#[init(contract = "storable-contract")]
fn init<S: HasContractStateLL>(
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

#[receive(contract = "storable-contract", name = "mint", parameter = "MintParams", mutable)]
fn receive_mint<S: HasContractStateLL + std::fmt::Debug>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, ContractStateLLType = S>,
) -> ReceiveResult<()> {
    let params: MintParams = ctx.parameter_cursor().get()?;

    // TODO: Avoid allocating new map up front. Necessary because of lifetime
    // restrictions on host.
    let mut owner_map = host.allocator().new_map();

    host.state_mut()
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
            let _old_value = owner_map.insert(params.token_id, params.token_count);
            owner_map
        });

    host.state_mut().another_struct.a_set.insert(42);

    // This won't be persisted. The change only occurs in memory.
    host.state_mut().total_tokens += params.token_count as u64;

    // But this should be.
    host.state_mut().boxed_total_tokens.update(|old_count| *old_count += params.token_count as u64);

    Ok(())
}

#[receive(contract = "storable-contract", name = "readonly")]
fn receive_readonly<S: HasContractStateLL + std::fmt::Debug>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, ContractStateLLType = S>,
) -> ReceiveResult<u64> {
    Ok(*host.state().boxed_total_tokens.get())
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    #[concordium_test]
    fn test_init() {
        let ctx = InitContextTest::empty();

        let state_ll = ContractStateLLTest::new();
        let mut allocator = Allocator::open(state_ll);

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

        let mut state_ll = ContractStateLLTest::new();
        let mut allocator = Allocator::open(state_ll.clone());

        // TODO: These extra serial/deserial state steps are no longer necessary. But we
        // can keep them for now to ensure that everything works as expected.

        // Set up initial state contents via init.
        let (_rv, state_to_store) =
            init(&InitContextTest::empty(), &mut allocator).expect("Init failed");

        // This store invocation normally occurs in the code generated by the init
        // macro.
        let mut root_entry = state_ll.create(&[]).expect("Creating root entry failed");
        state_to_store.serial(&mut root_entry).expect("Writing state failed");

        // Then load the state, as it happens when calling receive.
        root_entry.seek(SeekFrom::Start(0)).expect("Seeking to start failed");
        let state_for_rcv =
            State::deserial_state_ctx(&state_ll, &mut root_entry).expect("Could not read state");

        let mut host = HostTest::new_with_allocator(state_for_rcv, allocator);

        // Invoke receive.
        assert!(receive_mint(&ctx, &mut host).is_ok());

        // Store the state, as it normally occurs with the receive.
        root_entry.seek(SeekFrom::Start(0)).expect("Seeking to start failed");
        host.state().serial(&mut root_entry).expect("Could not serial state");

        // Reload the state to ensure that it was actually persisted (and not just
        // altered in memory).
        root_entry.seek(SeekFrom::Start(0)).expect("Seeking to start failed");
        let state_reloaded = State::deserial_state_ctx(&state_ll, &mut root_entry)
            .expect("Could not load all of state.");

        // Token count should be 100.
        assert_eq!(
            *state_reloaded.token_state.get(&owner).unwrap().get(&token_id).unwrap(),
            expected_token_count
        );

        let mut a_set_iter = state_reloaded.another_struct.a_set.iter();
        assert_eq!(*a_set_iter.next().expect("Should exist"), 42);
        assert!(a_set_iter.next().is_none());

        assert_eq!(state_reloaded.total_tokens, 100);
        assert_eq!(*state_reloaded.boxed_total_tokens.get(), 100);
    }
}
