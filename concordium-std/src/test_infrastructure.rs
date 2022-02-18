//! The test infrastructure module provides alternative implementations of
//! `HasInitContext`, `HasReceiveContext`, `HasParameter`, `HasContractState`,
//! and `HasHost` traits intended for testing.
//!
//! They allow writing unit tests directly in contract modules with little to no
//! external tooling, depending on what is required.
//!
//!
//! # Example
//!
//! ```rust
//! // Some contract
//! #[init(contract = "noop")]
//! fn contract_init(
//!     ctx: &impl HasInitContext,
//! ) -> InitResult<State> { ... }
//!
//! #[receive(contract = "noop", name = "receive", payable, enable_logger)]
//! fn contract_receive(
//!     ctx: &impl HasReceiveContext,
//!     amount: Amount,
//!     logger: &mut impl HasLogger,
//!     host: &mut HasHost<State>,
//! ) -> ReceiveResult<MyReturnValue> { ... }
//!
//! #[cfg(test)]
//! mod tests {
//!     use super::*;
//!     use concordium_sc_base::test_infrastructure::*;
//!     #[test]
//!     fn test_init() {
//!         let mut ctx = InitContextTest::empty();
//!         ctx.set_init_origin(AccountAddress([0u8; 32]));
//!         ...
//!         let result = contract_init(&ctx);
//!         claim!(...)
//!         ...
//!     }
//!
//!     #[test]
//!     fn test_receive() {
//!         let mut ctx = ReceiveContextTest::empty();
//!         let mut host = HostTest::new(State::new());
//!         ctx.set_owner(AccountAddress([0u8; 32]));
//!         ...
//!         let mut logger = LogRecorder::init();
//!         host.setup_mock_entrypoint(
//!             ContractAddress{index: 0, subindex: 0},
//!             OwnedEntrypointName::new_unchecked("get".into()),
//!             MockFn::returning_ok(MyReturnValue::new()));
//!         let result: ReceiveResult<MyReturnValue> = contract_receive(&ctx, &mut host,
//!                    Amount::zero(), &mut logger);
//!         claim!(...)
//!         ...
//!     }
//! }
//! ```
use crate::{constants::MAX_CONTRACT_STATE_SIZE, *};

use crate::collections::{BTreeMap, BTreeSet};
#[cfg(not(feature = "std"))]
use alloc::boxed::Box;
use convert::TryInto;
#[cfg(not(feature = "std"))]
use core::{cmp, num};
#[cfg(feature = "std")]
use std::{boxed::Box, cmp, num};
use std::{
    cell::{RefCell, RefMut},
    rc::Rc,
};

use self::trie::StateTrie;

mod trie;

/// Placeholder for the context chain meta data.
/// All the fields are optionally set and the getting an unset field will result
/// in test failing.
/// For most cases it is used as part of either
/// [`InitContextTest`](struct.InitContextTest.html) or
/// [`ReceiveContextTest`](struct.ReceiveContextTest.html).
/// Use only in unit tests!
///
/// Defaults to having all of the fields unset
#[derive(Default, Clone)]
pub struct ChainMetaTest {
    pub(crate) slot_time: Option<SlotTime>,
}

/// Policy type used by init and receive contexts for testing.
/// This type should not be used directly, but rather through
/// its `HasPolicy` interface.
#[derive(Debug, Clone)]
pub struct TestPolicy {
    /// Current position in the vector of policies. Used to implement
    /// `next_item`.
    position: usize,
    policy:   OwnedPolicy,
}

impl TestPolicy {
    fn new(policy: OwnedPolicy) -> Self {
        Self {
            position: 0,
            policy,
        }
    }
}

/// Placeholder for the common data shared between the `InitContext` and
/// `ReceiveContext`. This type is a technicality, see `InitContext` and
/// `ReceiveContext` for the types to use.
///
/// # Default
/// Defaults to having all the fields unset, and constructing
/// [`ChainMetaTest`](struct.ChainMetaTest.html) using default.
#[derive(Default, Clone)]
#[doc(hidden)]
pub struct CommonDataTest<'a> {
    pub(crate) metadata:  ChainMetaTest,
    pub(crate) parameter: Option<&'a [u8]>,
    /// Policy of the creator. We keep the `Option` wrapper
    /// in order that the user can be warned that they are using a policy.
    /// Thus there is a distinction between `Some(Vec::new())` and `None`.
    pub(crate) policies:  Option<Vec<TestPolicy>>,
}

/// Context used for testing. The type parameter C is used to determine whether
/// this will be an init or receive context.
#[derive(Default, Clone)]
pub struct ContextTest<'a, C> {
    pub(crate) common: CommonDataTest<'a>,
    pub(crate) custom: C,
}

/// Placeholder for the initial context. All the fields can be set optionally
/// and the getting an unset field will result in calling
/// [`fail!`](../macro.fail.html). Use only in tests!
///
/// # Setters
/// Every field has a setter function prefixed with `set_`.

/// ### Example
/// Creating an empty context and setting the `init_origin`.
/// ```
/// let mut ctx = InitContextTest::empty();
/// ctx.set_init_origin(AccountAddress([0u8; 32]));
/// ```
/// ## Set chain meta data
/// Chain meta data is set using setters on the context or by setters on a
/// mutable reference of [`ChainMetaTest`](struct.ChainMetaTest.html).
///
/// ### Example
/// Creating an empty context and setting the `slot_time` metadata.
/// ```
/// let mut ctx = InitContextTest::empty();
/// ctx.set_metadata_slot_time(1609459200);
/// ```
/// or
/// ```
/// let mut ctx = InitContextTest::empty();
/// ctx.metadata_mut().set_slot_time(1609459200);
/// ```
///
/// # Use case example
///
/// ```rust
/// #[init(contract = "noop")]
/// fn contract_init<I: HasInitContext, L: HasLogger>(
///     ctx: &I,
///     _amount: Amount,
///     _logger: &mut L,
/// ) -> InitResult<()> {
///     let init_origin = ctx.init_origin();
///     let parameter: SomeParameterType = ctx.parameter_cursor().get()?;
///     Ok(())
/// }
///
/// #[cfg(test)]
/// mod tests {
///     use super::*;
///     use concordium_sc_base::test_infrastructure::*;
///     #[test]
///     fn test() {
///         let mut ctx = InitContextTest::empty();
///         ctx.set_init_origin(AccountAddress([0u8; 32]));
///         ...
///         let result = contract_init(&ctx, 0, &mut logger);
///         // Reads the init_origin without any problems.
///         // But then fails because the parameter is not set.
///     }
/// }
/// ```
pub type InitContextTest<'a> = ContextTest<'a, InitOnlyDataTest>;

#[derive(Default)]
#[doc(hidden)]
pub struct InitOnlyDataTest {
    init_origin: Option<AccountAddress>,
}

/// Placeholder for the receiving context. All the fields can be set optionally
/// and the getting an unset field will result in calling
/// [`fail!`](../macro.fail.html). Use only in tests!
///
/// # Setters
/// Every field have a setter function prefixed with `set_`.
///
/// ### Example
/// Creating an empty context and setting the `init_origin`.
/// ```
/// let owner = AccountAddress([0u8; 32]);
/// let mut ctx = ReceiveContextTest::empty();
/// ctx.set_owner(owner);
/// ctx.set_sender(Address::Account(owner));
/// ```
/// ## Set chain meta data
/// Chain meta data is set using setters on the context or by setters on a
/// mutable reference of [`ChainMetaTest`](struct.ChainMetaTest.html).
///
/// ### Example
/// Creating an empty context and setting the `slot_time` metadata.
/// ```
/// let mut ctx = ReceiveContextTest::empty();
/// ctx.set_metadata_slot_time(1609459200);
/// ```
/// or
/// ```
/// let mut ctx = ReceiveContextTest::empty();
/// ctx.metadata_mut().set_slot_time(1609459200);
/// ```
///
/// # Use case example
/// Creating a context for running unit tests
/// ```rust
/// #[receive(contract = "mycontract", name = "receive")]
/// fn contract_receive<R: HasReceiveContext, L: HasLogger, A: HasActions>(
///     ctx: &R,
///     amount: Amount,
///     logger: &mut L,
///     state: &mut State,
/// ) -> ReceiveResult<A> {
///     ensure!(ctx.sender().matches_account(&ctx.owner()), "Only the owner can increment.");
///     Ok(A::accept())
/// }
///
/// #[cfg(test)]
/// mod tests {
///     use super::*;
///     use concordium_sc_base::test_infrastructure::*;
///     #[test]
///     fn test() {
///         let owner = AccountAddress([0u8; 32]);
///         let mut ctx = ReceiveContextTest::empty();
///         ctx.set_owner(owner);
///         ctx.set_sender(Address::Account(owner));
///         ...
///         let result: ReceiveResult<ActionsTree> = contract_receive(&ctx, 0, &mut logger, state);
///     }
/// }
/// ```
pub type ReceiveContextTest<'a> = ContextTest<'a, ReceiveOnlyDataTest>;

#[derive(Default)]
#[doc(hidden)]
pub struct ReceiveOnlyDataTest {
    pub(crate) invoker:      Option<AccountAddress>,
    pub(crate) self_address: Option<ContractAddress>,
    pub(crate) sender:       Option<Address>,
    pub(crate) owner:        Option<AccountAddress>,
}

// Setters for testing-context
impl ChainMetaTest {
    /// Create an `ChainMetaTest` where every field is unset, and getting any of
    /// the fields will result in [`fail!`](../macro.fail.html).
    pub fn empty() -> Self { Default::default() }

    /// Set the block slot time
    pub fn set_slot_time(&mut self, value: SlotTime) -> &mut Self {
        self.slot_time = Some(value);
        self
    }
}

impl<'a, C> ContextTest<'a, C> {
    /// Push a new sender policy to the context.
    /// When the first policy is pushed this will set the policy vector
    /// to 'Some', even if it was undefined previously.
    pub fn push_policy(&mut self, value: OwnedPolicy) -> &mut Self {
        if let Some(policies) = self.common.policies.as_mut() {
            policies.push(TestPolicy::new(value));
        } else {
            self.common.policies = Some(vec![TestPolicy::new(value)])
        }
        self
    }

    /// Set the policies to be defined, but an empty list.
    /// Such a situation can not realistically happen on the chain,
    /// but we provide functionality for it in case smart contract
    /// writers wish to program defensively.
    pub fn empty_policies(&mut self) -> &mut Self {
        self.common.policies = Some(Vec::new());
        self
    }

    pub fn set_parameter(&mut self, value: &'a [u8]) -> &mut Self {
        self.common.parameter = Some(value);
        self
    }

    /// Get a mutable reference to the chain meta data placeholder
    pub fn metadata_mut(&mut self) -> &mut ChainMetaTest { &mut self.common.metadata }

    /// Set the metadata block slot time
    pub fn set_metadata_slot_time(&mut self, value: SlotTime) -> &mut Self {
        self.metadata_mut().set_slot_time(value);
        self
    }
}

impl<'a> InitContextTest<'a> {
    /// Create an `InitContextTest` where every field is unset, and getting any
    /// of the fields will result in [`fail!`](../macro.fail.html).
    pub fn empty() -> Self { Default::default() }

    /// Set `init_origin` in the `InitContextTest`
    pub fn set_init_origin(&mut self, value: AccountAddress) -> &mut Self {
        self.custom.init_origin = Some(value);
        self
    }
}

impl<'a> ReceiveContextTest<'a> {
    /// Create a `ReceiveContextTest` where every field is unset, and getting
    /// any of the fields will result in [`fail!`](../macro.fail.html).
    pub fn empty() -> Self { Default::default() }

    pub fn set_invoker(&mut self, value: AccountAddress) -> &mut Self {
        self.custom.invoker = Some(value);
        self
    }

    pub fn set_self_address(&mut self, value: ContractAddress) -> &mut Self {
        self.custom.self_address = Some(value);
        self
    }

    pub fn set_sender(&mut self, value: Address) -> &mut Self {
        self.custom.sender = Some(value);
        self
    }

    pub fn set_owner(&mut self, value: AccountAddress) -> &mut Self {
        self.custom.owner = Some(value);
        self
    }
}

// Error handling when unwrapping
fn unwrap_ctx_field<A>(opt: Option<A>, name: &str) -> A {
    match opt {
        Some(v) => v,
        None => fail!(
            "Unset field on test context '{}', make sure to set all the fields necessary for the \
             contract",
            name
        ),
    }
}

// Getters for testing-context
impl HasChainMetadata for ChainMetaTest {
    fn slot_time(&self) -> SlotTime { unwrap_ctx_field(self.slot_time, "metadata.slot_time") }
}

impl HasPolicy for TestPolicy {
    fn identity_provider(&self) -> IdentityProvider { self.policy.identity_provider }

    fn created_at(&self) -> Timestamp { self.policy.created_at }

    fn valid_to(&self) -> Timestamp { self.policy.valid_to }

    fn next_item(&mut self, buf: &mut [u8; 31]) -> Option<(AttributeTag, u8)> {
        if let Some(item) = self.policy.items.get(self.position) {
            let len = item.1.len();
            buf[0..len].copy_from_slice(&item.1);
            self.position += 1;
            Some((item.0, len as u8))
        } else {
            None
        }
    }
}

impl<'a, C> HasCommonData for ContextTest<'a, C> {
    type MetadataType = ChainMetaTest;
    type ParamType = Cursor<&'a [u8]>;
    type PolicyIteratorType = crate::vec::IntoIter<TestPolicy>;
    type PolicyType = TestPolicy;

    fn parameter_cursor(&self) -> Self::ParamType {
        Cursor::new(unwrap_ctx_field(self.common.parameter, "parameter"))
    }

    fn metadata(&self) -> &Self::MetadataType { &self.common.metadata }

    fn policies(&self) -> Self::PolicyIteratorType {
        unwrap_ctx_field(self.common.policies.clone(), "policies").into_iter()
    }
}

impl<'a> HasInitContext for InitContextTest<'a> {
    type InitData = ();

    fn open(_data: Self::InitData) -> Self { InitContextTest::default() }

    fn init_origin(&self) -> AccountAddress {
        unwrap_ctx_field(self.custom.init_origin, "init_origin")
    }
}

impl<'a> HasReceiveContext for ReceiveContextTest<'a> {
    type ReceiveData = ();

    fn open(_data: Self::ReceiveData) -> Self { ReceiveContextTest::default() }

    fn invoker(&self) -> AccountAddress { unwrap_ctx_field(self.custom.invoker, "invoker") }

    fn self_address(&self) -> ContractAddress {
        unwrap_ctx_field(self.custom.self_address, "self_address")
    }

    fn sender(&self) -> Address { unwrap_ctx_field(self.custom.sender, "sender") }

    fn owner(&self) -> AccountAddress { unwrap_ctx_field(self.custom.owner, "owner") }
}

impl<'a> HasParameter for Cursor<&'a [u8]> {
    fn size(&self) -> u32 { self.data.len() as u32 }
}

/// A logger that simply accumulates all the logged items to be inspected at the
/// end of execution.
pub struct LogRecorder {
    pub logs: Vec<Vec<u8>>,
}

impl HasLogger for LogRecorder {
    fn init() -> Self {
        Self {
            logs: Vec::new(),
        }
    }

    fn log_raw(&mut self, event: &[u8]) -> Result<(), LogError> {
        if event.len() > constants::MAX_LOG_SIZE {
            return Err(LogError::Malformed);
        }
        if self.logs.len() >= constants::MAX_NUM_LOGS {
            return Err(LogError::Full);
        }
        self.logs.push(event.to_vec());
        Ok(())
    }
}

/// An actions tree, used to provide a simpler presentation for testing.
#[derive(Eq, PartialEq, Debug)]
pub enum ActionsTree {
    Accept,
    SimpleTransfer {
        to:     AccountAddress,
        amount: Amount,
    },
    Send {
        to:           ContractAddress,
        receive_name: OwnedReceiveName,
        amount:       Amount,
        parameter:    Vec<u8>,
    },
    AndThen {
        left:  Box<ActionsTree>,
        right: Box<ActionsTree>,
    },
    OrElse {
        left:  Box<ActionsTree>,
        right: Box<ActionsTree>,
    },
}

/// Reports back an error to the host when compiled to wasm
/// Used internally, not meant to be called directly by contract writers
#[doc(hidden)]
#[cfg(all(feature = "wasm-test", target_arch = "wasm32"))]
pub fn report_error(message: &str, filename: &str, line: u32, column: u32) {
    let msg_bytes = message.as_bytes();
    let filename_bytes = filename.as_bytes();
    unsafe {
        crate::prims::report_error(
            msg_bytes.as_ptr(),
            msg_bytes.len() as u32,
            filename_bytes.as_ptr(),
            filename_bytes.len() as u32,
            line,
            column,
        )
    };
}

/// Reports back an error to the host when compiled to wasm
/// Used internally, not meant to be called directly by contract writers
#[doc(hidden)]
#[cfg(not(all(feature = "wasm-test", target_arch = "wasm32")))]
pub fn report_error(_message: &str, _filename: &str, _line: u32, _column: u32) {}

#[derive(Debug, PartialEq, Eq)]
/// An error that is raised when operating with `Seek`, `Write`, or `Read` trait
/// methods of the `ContractStateTest` type.
pub enum ContractStateError {
    /// The computation of the new offset would result in an overflow.
    Overflow,
    /// An error occurred when writing to the contract state.
    Write,
    /// The new offset would be out of bounds of the state.
    Offset,
    /// Some other error occurred.
    Default,
}

impl Default for ContractStateError {
    fn default() -> Self { Self::Default }
}

impl From<num::TryFromIntError> for ContractStateError {
    fn from(_: num::TryFromIntError) -> Self { ContractStateError::Overflow }
}

// TODO: Replace the Vec with a generic T.
#[derive(Debug, PartialEq)]
pub struct StateEntryTest {
    pub(crate) cursor:         Cursor<Rc<RefCell<Vec<u8>>>>,
    pub(crate) key:            Vec<u8>,
    pub(crate) state_entry_id: StateEntryId,
}

impl StateEntryTest {
    pub fn open(data: Rc<RefCell<Vec<u8>>>, key: Vec<u8>, state_entry_id: StateEntryId) -> Self {
        Self {
            cursor: Cursor::new(data),
            key,
            state_entry_id,
        }
    }
}

#[derive(Debug)]
pub struct ContractStateLLTest {
    trie: StateTrie,
}

impl HasContractStateLL for ContractStateLLTest {
    type ContractStateData = StateTrie;
    type EntryType = StateEntryTest;
    type IterType = trie::Iter;

    fn open(trie: Self::ContractStateData) -> Self {
        Self {
            trie,
        }
    }

    fn entry(&mut self, key: &[u8]) -> EntryRaw<Self::EntryType> {
        if let Some(state_entry) = self.trie.lookup(key) {
            EntryRaw::Occupied(OccupiedEntryRaw::new(state_entry))
        } else {
            EntryRaw::Vacant(VacantEntryRaw::new(self.trie.create(key)))
        }
    }

    fn lookup(&self, key: &[u8]) -> Option<Self::EntryType> { self.trie.lookup(key) }

    fn delete_entry(&mut self, entry: Self::EntryType) -> bool { self.trie.delete_entry(entry) }

    fn delete_prefix(&mut self, prefix: &[u8], exact: bool) -> bool {
        self.trie.delete_prefix(prefix, exact)
    }

    fn iterator(&self, prefix: &[u8]) -> Self::IterType { self.trie.iter(prefix) }
}

impl ContractStateLLTest {
    pub fn new() -> Self {
        Self {
            trie: StateTrie::new(),
        }
    }
}

impl HasContractStateEntry for StateEntryTest {
    type Error = ContractStateError;
    type StateEntryData = Rc<RefCell<Vec<u8>>>;
    type StateEntryKey = Vec<u8>;

    fn open(data: Self::StateEntryData, key: Self::StateEntryKey, entry_id: StateEntryId) -> Self {
        Self {
            cursor: Cursor::new(data),
            state_entry_id: entry_id,
            key,
        }
    }

    fn size(&self) -> u32 { self.cursor.data.borrow().len() as u32 }

    fn truncate(&mut self, new_size: u32) {
        if self.size() > new_size {
            let new_size = new_size as usize;
            let data: &mut Vec<u8> = &mut self.cursor.data.as_ref().borrow_mut();
            data.truncate(new_size);
            if self.cursor.offset > new_size {
                self.cursor.offset = new_size
            }
        }
    }

    fn reserve(&mut self, len: u32) -> bool {
        // TODO: Max still needed?
        if len <= constants::MAX_CONTRACT_STATE_SIZE {
            if self.size() < len {
                let data: &mut Vec<u8> = &mut self.cursor.data.as_ref().borrow_mut();
                data.resize(len as usize, 0u8);
            }
            true
        } else {
            false
        }
    }

    fn get_key(&self) -> Vec<u8> { self.key.clone() }
}

impl Read for StateEntryTest {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
        let mut len = self.cursor.data.borrow().len() - self.cursor.offset;
        if len > buf.len() {
            len = buf.len();
        }
        if len > 0 {
            buf[0..len].copy_from_slice(
                &self.cursor.data.borrow()[self.cursor.offset..self.cursor.offset + len],
            );
            self.cursor.offset += len;
            Ok(len)
        } else {
            Ok(0)
        }
    }
}

impl Write for StateEntryTest {
    type Err = ContractStateError;

    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Err> {
        // The chain automatically resizes the state up until MAX_CONTRACT_STATE_SIZE.
        // TODO: Still the case?
        let end = cmp::min(MAX_CONTRACT_STATE_SIZE as usize, self.cursor.offset + buf.len());
        if self.cursor.data.borrow().len() < end {
            let mut data: RefMut<Vec<u8>> = self.cursor.data.as_ref().borrow_mut();
            data.resize(end as usize, 0u8);
        }
        let data = &mut self.cursor.data.as_ref().borrow_mut()[self.cursor.offset..];
        let to_write = cmp::min(data.len(), buf.len());
        data[..to_write].copy_from_slice(&buf[..to_write]);
        self.cursor.offset += to_write;
        Ok(to_write)
    }
}

impl Seek for StateEntryTest {
    type Err = ContractStateError;

    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Err> {
        use ContractStateError::*;
        match pos {
            SeekFrom::Start(x) => {
                // We can set the position to just after the end of the current length.
                let new_offset = x.try_into()?;
                if new_offset <= self.cursor.data.borrow().len() {
                    self.cursor.offset = new_offset;
                    Ok(x)
                } else {
                    Err(Offset)
                }
            }
            SeekFrom::End(x) => {
                // cannot seek beyond end, nor before beginning
                if x <= 0 {
                    let end: u32 = self.cursor.data.borrow().len().try_into()?;
                    let minus_x = x.checked_abs().ok_or(Overflow)?;
                    if let Some(new_pos) = end.checked_sub(minus_x.try_into()?) {
                        self.cursor.offset = new_pos.try_into()?;
                        Ok(u64::from(new_pos))
                    } else {
                        Err(Offset)
                    }
                } else {
                    Err(Offset)
                }
            }
            SeekFrom::Current(x) => match x {
                0 => Ok(self.cursor.offset.try_into()?),
                x if x > 0 => {
                    let x = x.try_into()?;
                    let new_pos = self.cursor.offset.checked_add(x).ok_or(Overflow)?;
                    if new_pos <= self.cursor.data.borrow().len() {
                        self.cursor.offset = new_pos;
                        new_pos.try_into().map_err(Self::Err::from)
                    } else {
                        Err(Offset)
                    }
                }
                x => {
                    let x = (-x).try_into()?;
                    let new_pos = self.cursor.offset.checked_sub(x).ok_or(Overflow)?;
                    self.cursor.offset = new_pos;
                    new_pos.try_into().map_err(Self::Err::from)
                }
            },
        }
    }
}

impl HasCallResponse for Cursor<Vec<u8>> {
    fn size(&self) -> u32 { self.data.len() as u32 }
}

/// Holds a function used for mocking invocations of contracts with
/// `invoke_contract`.
pub struct MockFn<State> {
    f: TestMockFn<State>,
}

/// The handler for a specific entrypoint. This is a boxed closure for good
/// ergonomics. It does however mean that in practice only closures which don't
/// capture any references may be put into it. This does prevent some example
/// uses, or at least forces them to use awkward patterns. In particular, a test
/// example where the closure would keep track of whether it is called or not
/// via incrementing a local variable is not going to be possible to express.
///
/// This might be improved in the future.
type TestMockFn<State> = Box<
    dyn FnMut(Parameter, Amount, &mut Amount, &mut State) -> CallContractResult<Cursor<Vec<u8>>>,
>;

impl<State> MockFn<State> {
    /// Create a mock function which has access to `parameter`, `amount`,
    /// `balance`, and `state`.
    ///
    /// `parameter` and `amount` correspond to the values used in
    /// `invoke_contract(.., parameter, .., amount)`.
    /// `balance` and `state` correspond to the values from the contract you are
    /// testing. They are used to simulate calls to the contract itself,
    /// which can change the balance and state of the contract.
    ///
    /// The function should return a pair (state_modified, return_value), where
    /// state_modified should be set to `true`, if the function modifies the
    /// state parameter. It should modify the `balance` and `state` in way
    /// desired in the test, or in a way that the called contract is
    /// intended to behave.
    ///
    /// See also `returning_ok` and `returning_err` for when you need simple
    /// mocks.
    pub fn new<R, F>(mut mock_fn_return: F) -> Self
    where
        R: Serial,
        F: FnMut(Parameter, Amount, &mut Amount, &mut State) -> CallContractResult<R> + 'static,
    {
        let mock_fn = Box::new(
            move |parameter: Parameter, amount: Amount, balance: &mut Amount, state: &mut State| {
                match mock_fn_return(parameter, amount, balance, state) {
                    Ok((modified, return_value)) => {
                        if let Some(return_value) = return_value {
                            Ok((modified, Some(Cursor::new(to_bytes(&return_value)))))
                        } else {
                            Ok((modified, None))
                        }
                    }
                    Err(e) => match e {
                        CallContractError::AmountTooLarge => Err(CallContractError::AmountTooLarge),
                        CallContractError::MissingAccount => Err(CallContractError::MissingAccount),
                        CallContractError::MissingContract => {
                            Err(CallContractError::MissingContract)
                        }
                        CallContractError::MissingEntrypoint => {
                            Err(CallContractError::MissingEntrypoint)
                        }
                        CallContractError::MessageFailed => Err(CallContractError::MessageFailed),
                        CallContractError::LogicReject {
                            reason,
                            return_value,
                        } => Err(CallContractError::LogicReject {
                            reason,
                            return_value: Cursor::new(to_bytes(&return_value)),
                        }),
                        CallContractError::Trap => Err(CallContractError::Trap),
                    },
                }
            },
        );
        Self {
            f: mock_fn,
        }
    }

    /// A helper that assumes that a V1 contract is invoked. This means that the
    /// return value will **always** be present in case of success.
    pub fn new_v1<R, F>(mut mock_fn_return: F) -> Self
    where
        R: Serial,
        F: FnMut(
                Parameter,
                Amount,
                &mut Amount,
                &mut State,
            ) -> Result<(bool, R), CallContractError<R>>
            + 'static, {
        Self::new(move |p, a, b, s| {
            mock_fn_return(p, a, b, s).map(|(modified, rv)| (modified, Some(rv)))
        })
    }

    /// A helper that assumes that a V0 contract is invoked. This means that the
    /// return value will **never** be present in case of success, and hence
    /// does not have to be provided by the caller.
    pub fn new_v0<R, F>(mut mock_fn_return: F) -> Self
    where
        R: Serial,
        F: FnMut(Parameter, Amount, &mut Amount, &mut State) -> Result<bool, CallContractError<R>>
            + 'static, {
        Self::new(move |p, a, b, s| mock_fn_return(p, a, b, s).map(|modified| (modified, None)))
    }

    /// Create a simple mock function that returns `Ok` with the same
    /// value every time, and signals the state is not changed.
    pub fn returning_ok<R: Clone + Serial + 'static>(return_value: R) -> Self {
        Self::new(move |_parameter, _amount, _balance, _state| -> CallContractResult<R> {
            Ok((false, Some(return_value.clone())))
        })
    }

    /// Create a simple mock function that returns `Err` with same error every
    /// time.
    pub fn returning_err<R: Clone + Serial + 'static>(error: CallContractError<R>) -> Self {
        Self::new(
            move |_parameter: Parameter,
                  _amount: Amount,
                  _balance: &mut Amount,
                  _state: &mut State|
                  -> CallContractResult<R> { Err(error.clone()) },
        )
    }
}

/// A Host implementation used for testing.
/// Exposes a number of helper functions for mocking host behavior.
pub struct HostTest<State> {
    /// Functions that mock responses to calls.
    mocking_fns:      BTreeMap<(ContractAddress, OwnedEntrypointName), MockFn<State>>,
    /// Transfers the contract has made during its execution.
    transfers:        Vec<(AccountAddress, Amount)>,
    /// The contract balance. This is updated during execution based on contract
    /// invocations, e.g., a successful transfer from the contract decreases it.
    contract_balance: Amount,
    /// Allocator for the state.
    allocator:        Allocator<ContractStateLLTest>,
    /// State of the instance.
    state:            State,
    /// List of accounts that will cause a contract invocation to fail.
    missing_accounts: BTreeSet<AccountAddress>,
}

impl<State> HasHost<State> for HostTest<State> {
    type ContractStateLLType = ContractStateLLTest;
    type ReturnValueType = Cursor<Vec<u8>>;

    /// Perform a transfer to the given account if the contract has sufficient
    /// balance.
    ///
    /// By default, all accounts are assumed to exist, and transfers to them
    /// will succeed (provided sufficient balance).
    /// Use `make_account_missing` to test out transfers to accounts not on
    /// chain.
    ///
    /// Possible errors:
    ///   - [TransferError::AmountTooLarge]: Contract has insufficient funds.
    ///   - [TransferError::MissingAccount]: Attempted transfer to an account
    ///     set as missing with `make_account_missing`.
    fn invoke_transfer(&mut self, receiver: &AccountAddress, amount: Amount) -> TransferResult {
        if self.missing_accounts.contains(receiver) {
            return Err(TransferError::MissingAccount);
        }
        if amount.micro_ccd > 0 {
            if self.contract_balance >= amount {
                self.contract_balance -= amount;
                self.transfers.push((*receiver, amount));
                Ok(())
            } else {
                Err(TransferError::AmountTooLarge)
            }
        } else {
            Ok(())
        }
    }

    /// Invoke a contract entrypoint.
    ///
    /// This uses the mock entrypoints set up with
    /// `setup_mock_entrypoint`. The method will [fail] with a panic
    /// if no responses were set for the given contract address and method.
    fn invoke_contract<'a, 'b>(
        &'a mut self,
        to: &'b ContractAddress,
        parameter: Parameter<'b>,
        method: EntrypointName<'b>,
        amount: Amount,
    ) -> CallContractResult<Self::ReturnValueType> {
        let handler = match self.mocking_fns.get_mut(&(*to, OwnedEntrypointName::from(method))) {
            Some(handler) => handler,
            None => fail!(
                "Mocking has not been set up for invoking contract {:?} with method '{}'.",
                to,
                method
            ),
        };
        // Check if the contract has sufficient balance.
        if amount.micro_ccd > 0 && self.contract_balance < amount {
            return Err(CallContractError::AmountTooLarge);
        }

        // Invoke the handler.
        let res = (handler.f)(parameter, amount, &mut self.contract_balance, &mut self.state);

        // Update the contract balance if the invocation succeeded.
        if res.is_ok() && amount.micro_ccd > 0 {
            self.contract_balance -= amount;
        }
        res
    }

    /// Get the contract state.
    fn state(&mut self) -> &mut State { &mut self.state }

    /// Get the contract balance.
    /// This can be set with `set_balance` and defaults to 0.
    fn self_balance(&self) -> Amount { self.contract_balance }

    fn allocator(&mut self) -> &mut Allocator<Self::ContractStateLLType> { &mut self.allocator }
}

impl<State> HostTest<State> {
    /// Create a new test host.
    pub fn new(state: State) -> Self {
        HostTest::new_with_allocator(state, Allocator {
            state_ll: Rc::new(RefCell::new(ContractStateLLTest::open(StateTrie::new()))),
        })
    }

    /// Create a new test host with an existing allocator.
    /// This can be useful when a single test function invokes both init and
    /// receive.
    pub fn new_with_allocator(state: State, allocator: Allocator<ContractStateLLTest>) -> Self {
        Self {
            mocking_fns: BTreeMap::new(),
            transfers: Vec::new(),
            contract_balance: Amount::zero(),
            allocator,
            state,
            missing_accounts: BTreeSet::new(),
        }
    }

    /// Set up a mock entrypoint for handling calls to `invoke_contract`.
    ///
    /// If you set up multiple handlers for the same entrypoint (to, method),
    /// then the latest handler will be used.
    pub fn setup_mock_entrypoint(
        &mut self,
        to: ContractAddress,
        method: OwnedEntrypointName,
        handler: MockFn<State>,
    ) {
        self.mocking_fns.insert((to, method), handler);
    }

    /// Set the contract balance.
    /// NB: This should be the sum of the contract's initial balance and the
    /// amount you wish to invoke it with.
    ///
    /// Example:
    /// ```ignore
    /// ...
    /// host.set_balance(Amount::from_ccd(10));
    /// contract_receive(&ctx,
    ///                  &mut host,
    ///                  // This amount is _not_ added to the balance of the contract,
    ///                  // so calling `host.self_balance()` will return `10` initially.
    ///                  // This differs from when you run a contract on the node,
    ///                  // where the amount automatically is added to the existing
    ///                  // balance of the contract.
    ///                  Amount::from_ccd(5)
    ///                  );
    /// ```
    pub fn set_balance(&mut self, amount: Amount) { self.contract_balance = amount; }

    /// Check whether a given transfer occured.
    pub fn transfer_occurred(&self, receiver: &AccountAddress, amount: Amount) -> bool {
        self.transfers.contains(&(*receiver, amount))
    }

    /// Get a list of all transfers that has occurred.
    pub fn get_transfers(&self) -> &[(AccountAddress, Amount)] { &self.transfers }

    /// Get a list of all transfers to a specific account.
    pub fn get_transfers_to(&self, account: AccountAddress) -> Vec<Amount> {
        self.transfers
            .iter()
            .filter_map(|(acc, amount)| {
                if *acc == account {
                    Some(*amount)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Set an account to be missing. Any transfers to this account will result
    /// in an [TransferError::MissingAccount] error.
    ///
    /// This differs from the default, where all accounts are assumed to exist.
    pub fn make_account_missing(&mut self, account: AccountAddress) {
        self.missing_accounts.insert(account);
    }
}

#[cfg(test)]
mod test {
    use std::{cell::RefCell, rc::Rc};

    use concordium_contracts_common::{
        to_bytes, Deserial, ParseError, Read, Seek, SeekFrom, Write,
    };

    use super::ContractStateLLTest;
    use crate::{
        constants, test_infrastructure::StateEntryTest, Allocator, EntryRaw, HasContractStateEntry,
        HasContractStateLL, StateMap, StateSet, UnwrapAbort,
    };

    #[test]
    // Perform a number of operations from Seek, Read, Write and HasContractState
    // classes on the ContractStateTest structure and check that they behave as
    // specified.
    fn test_contract_state() {
        let data = Rc::new(RefCell::new(vec![1; 100]));
        let mut state = StateEntryTest::open(data, Vec::new(), 0);
        assert_eq!(state.seek(SeekFrom::Start(100)), Ok(100), "Seeking to the end failed.");
        assert_eq!(
            state.seek(SeekFrom::Current(0)),
            Ok(100),
            "Seeking from current position with offset 0 failed."
        );
        assert!(
            state.seek(SeekFrom::Current(1)).is_err(),
            "Seeking from current position with offset 1 succeeded."
        );
        assert_eq!(state.cursor.offset, 100, "Cursor position changed on failed seek.");
        assert_eq!(
            state.seek(SeekFrom::Current(-1)),
            Ok(99),
            "Seeking from current position backwards with offset 1 failed."
        );
        assert!(state.seek(SeekFrom::Current(-100)).is_err(), "Seeking beyond beginning succeeds");
        assert_eq!(state.seek(SeekFrom::Current(-99)), Ok(0), "Seeking to the beginning fails.");
        assert_eq!(state.seek(SeekFrom::End(0)), Ok(100), "Seeking from end fails.");
        assert!(
            state.seek(SeekFrom::End(1)).is_err(),
            "Seeking beyond the end succeeds but should fail."
        );
        assert_eq!(state.cursor.offset, 100, "Cursor position changed on failed seek.");
        assert_eq!(
            state.seek(SeekFrom::End(-20)),
            Ok(80),
            "Seeking from end leads to incorrect position."
        );
        assert_eq!(state.write(&[0; 21]), Ok(21), "Writing writes an incorrect amount of data.");
        assert_eq!(state.cursor.offset, 101, "After writing the cursor is at the end.");
        assert_eq!(state.write(&[0; 21]), Ok(21), "Writing again writes incorrect amount of data.");
        let mut buf = [0; 30];
        assert_eq!(state.read(&mut buf), Ok(0), "Reading from the end should read 0 bytes.");
        assert_eq!(state.seek(SeekFrom::End(-20)), Ok(102));
        assert_eq!(state.read(&mut buf), Ok(20), "Reading from offset 80 should read 20 bytes.");
        assert_eq!(&buf[0..20], &state.cursor.data.borrow()[80..100], "Incorrect data was read.");
        assert_eq!(
            state.cursor.offset, 122,
            "After reading the offset is in the correct position."
        );
        assert!(state.reserve(222), "Could not increase state to 222.");
        assert!(
            !state.reserve(constants::MAX_CONTRACT_STATE_SIZE + 1),
            "State should not be resizable beyond max limit."
        );
        assert_eq!(state.write(&[2; 100]), Ok(100), "Should have written 100 bytes.");
        assert_eq!(state.cursor.offset, 222, "After writing the offset should be 200.");
        state.truncate(50);
        assert_eq!(state.cursor.offset, 50, "After truncation the state should be 50.");
        assert!(state.reserve(constants::MAX_CONTRACT_STATE_SIZE), "Could not increase state MAX.");
        assert_eq!(
            state.seek(SeekFrom::End(0)),
            Ok(u64::from(constants::MAX_CONTRACT_STATE_SIZE)),
            "State should be full now."
        );
        assert_eq!(
            state.write(&[1; 1000]),
            Ok(0),
            "Writing at the end after truncation should do nothing."
        );
        assert_eq!(
            state.cursor.data.as_ref().borrow().len(),
            constants::MAX_CONTRACT_STATE_SIZE as usize,
            "State size should not increase beyond max."
        );
    }

    #[test]
    fn test_contract_state_write() {
        let data = Rc::new(RefCell::new(vec![0u8; 10]));
        let mut state = StateEntryTest::open(data, Vec::new(), 0);
        assert_eq!(state.write(&1u64.to_le_bytes()), Ok(8), "Incorrect number of bytes written.");
        assert_eq!(
            state.write(&2u64.to_le_bytes()),
            Ok(8),
            "State should be resized automatically."
        );
        assert_eq!(state.cursor.offset, 16, "Pos should be at the end.");
        assert_eq!(
            *state.cursor.data.as_ref().borrow(),
            vec![1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
            "Correct data was written."
        );
    }

    #[test]
    fn high_level_insert_get() {
        let expected_value: u64 = 123123123;
        let mut allocator = Allocator::open(Rc::new(RefCell::new(ContractStateLLTest::new())));
        allocator.insert(0, expected_value);
        let actual_value: u64 = allocator.get(0).expect("Not found").expect("Not a valid u64");
        assert_eq!(expected_value, actual_value);
    }

    #[test]
    fn low_level_entry() {
        let expected_value: u64 = 123123123;
        let key = to_bytes(&42u64);
        let mut state = ContractStateLLTest::new();
        state.entry(&key).or_insert(&to_bytes(&expected_value));

        match state.entry(&key) {
            EntryRaw::Vacant(_) => assert!(false),
            EntryRaw::Occupied(occ) => {
                assert_eq!(u64::deserial(&mut occ.get()), Ok(expected_value))
            }
        }
    }

    #[test]
    fn high_level_statemap() -> Result<(), ParseError> {
        let my_map_key = "my_map";
        let mut allocator = Allocator::open(Rc::new(RefCell::new(ContractStateLLTest::new())));

        let map_to_insert = allocator.new_map::<String, String>();
        allocator.insert(my_map_key, map_to_insert);

        let mut my_map: StateMap<String, String, _> = allocator.get(my_map_key).unwrap_abort()?;
        my_map.insert("abc".to_string(), "hello, world".to_string());
        my_map.insert("def".to_string(), "hallo, weld".to_string());
        my_map.insert("ghi".to_string(), "hej, verden".to_string());
        assert_eq!(my_map.get("abc".to_string()), Some(Ok("hello, world".to_string())));

        let mut iter = my_map.iter();
        assert_eq!(iter.next(), Some(Ok(("abc".to_string(), "hello, world".to_string()))));
        assert_eq!(iter.next(), Some(Ok(("def".to_string(), "hallo, weld".to_string()))));
        assert_eq!(iter.next(), Some(Ok(("ghi".to_string(), "hej, verden".to_string()))));
        assert_eq!(iter.next(), None);

        Ok(())
    }

    #[test]
    fn high_level_nested_statemaps() {
        let inner_map_key = 0u8;
        let key_to_value = 77u8;
        let value = 255u8;
        let mut allocator = Allocator::open(Rc::new(RefCell::new(ContractStateLLTest::new())));
        let mut outer_map = allocator.new_map::<u8, StateMap<u8, u8, _>>();
        let mut inner_map = allocator.new_map::<u8, u8>();

        inner_map.insert(key_to_value, value);
        outer_map.insert(inner_map_key, inner_map);

        assert_eq!(
            outer_map.get(inner_map_key).unwrap().unwrap().get(key_to_value),
            Some(Ok(value))
        );
    }

    #[test]
    fn high_level_stateset() {
        let my_set_key = "my_set";
        let mut allocator = Allocator::open(Rc::new(RefCell::new(ContractStateLLTest::new())));

        let mut set = allocator.new_set::<u8>();
        assert_eq!(set.insert(0), true);
        assert_eq!(set.insert(1), true);
        assert_eq!(set.insert(1), false);
        assert_eq!(set.insert(2), true);
        assert_eq!(set.remove(&2), true);
        allocator.insert(my_set_key, set);

        assert_eq!(
            allocator.get::<_, StateSet<u8, _>>(my_set_key).unwrap().unwrap().contains(&0),
            true
        );
        assert_eq!(
            allocator.get::<_, StateSet<u8, _>>(my_set_key).unwrap().unwrap().contains(&2),
            false
        );

        let mut iter = allocator.get::<_, StateSet<u8, _>>(my_set_key).unwrap().unwrap().iter();
        assert_eq!(iter.next(), Some(Ok(0)));
        assert_eq!(iter.next(), Some(Ok(1)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn high_level_nested_stateset() {
        let inner_set_key = 0u8;
        let value = 255u8;
        let mut allocator = Allocator::open(Rc::new(RefCell::new(ContractStateLLTest::new())));
        let mut outer_map = allocator.new_map::<u8, StateSet<u8, _>>();
        let mut inner_set = allocator.new_set::<u8>();

        inner_set.insert(value);
        outer_map.insert(inner_set_key, inner_set);

        assert_eq!(outer_map.get(inner_set_key).unwrap().unwrap().contains(&value), true);
    }

    #[test]
    fn allocate_and_get_statebox() {
        let mut allocator = Allocator::open(Rc::new(RefCell::new(ContractStateLLTest::new())));
        let boxed_value = String::from("I'm boxed");
        let statebox = allocator.new_box(boxed_value.clone());
        assert_eq!(statebox.get_copy().unwrap().unwrap(), boxed_value);
    }
}
