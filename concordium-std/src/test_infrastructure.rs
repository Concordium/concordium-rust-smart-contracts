//! The test infrastructure module provides alternative implementations of
//! `HasInitContext`, `HasReceiveContext`, `HasParameter`, `HasStateApi`,
//! and `HasHost` traits intended for testing.
//!
//! They allow writing unit tests directly in contract modules with little to no
//! external tooling, depending on what is required.
//!
//!
//! # Example
//!
//! ```rust
//! # use concordium_std::*;
//! # type MyReturnValue = u64;
//! # type State = u64;
//! // Some contract
//! #[init(contract = "noop")]
//! fn contract_init<S: HasStateApi>(
//!     ctx: &impl HasInitContext,
//!     state_builder: &mut StateBuilder<S>,
//! ) -> InitResult<State> {
//!     // ...
//!     # Ok(0)
//! }
//!
//! #[receive(contract = "noop", name = "receive", payable, enable_logger, mutable)]
//! fn contract_receive<S: HasStateApi>(
//!     ctx: &impl HasReceiveContext,
//!     host: &mut impl HasHost<State, StateApiType = S>,
//!     amount: Amount,
//!     logger: &mut impl HasLogger,
//! ) -> ReceiveResult<MyReturnValue> {
//!     // ...
//!    # Ok(0)
//! }
//!
//! #[cfg(test)]
//! mod tests {
//!     use super::*;
//!     use concordium_std::test_infrastructure::*;
//!     #[test]
//!     fn test_init() {
//!         let mut ctx = TestInitContext::empty();
//!         let mut state_builder = TestStateBuilder::new();
//!         ctx.set_init_origin(AccountAddress([0u8; 32]));
//!         let result = contract_init(&ctx, &mut state_builder);
//!         // claim!(...)
//!     }
//!
//!     #[test]
//!     fn test_receive() {
//!         let mut ctx = TestReceiveContext::empty();
//!         let mut host = TestHost::new(State::new(), TestStateBuilder::new());
//!         ctx.set_owner(AccountAddress([0u8; 32]));
//!         // ...
//!         let mut logger = TestLogger::init();
//!         host.setup_mock_entrypoint(
//!             ContractAddress {
//!                 index:    0,
//!                 subindex: 0,
//!             },
//!             OwnedEntrypointName::new_unchecked("get".into()),
//!             MockFn::returning_ok(MyReturnValue::new()),
//!         );
//!         let result: ReceiveResult<MyReturnValue> =
//!             contract_receive(&ctx, &mut host, Amount::zero(), &mut logger);
//!         // claim!(...)
//!     }
//! }
//! ```
use crate::*;

use self::trie::StateTrie;
use crate::{
    boxed::Box,
    cell::RefCell,
    cmp,
    collections::{BTreeMap, BTreeSet},
    num,
    rc::Rc,
};
use convert::TryInto;

mod trie;

/// Placeholder for the context chain meta data.
/// All the fields are optionally set and the getting an unset field will result
/// in test failing.
/// For most cases it is used as part of either
/// [`TestInitContext`](struct.TestInitContext.html) or
/// [`TestReceiveContext`](struct.TestReceiveContext.html).
/// Use only in unit tests!
///
/// Defaults to having all of the fields unset
#[derive(Default, Clone)]
pub struct TestChainMeta {
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
/// [`TestChainMeta`](struct.TestChainMeta.html) using default.
#[derive(Default, Clone)]
#[doc(hidden)]
pub struct TestCommonData<'a> {
    pub(crate) metadata:  TestChainMeta,
    pub(crate) parameter: Option<&'a [u8]>,
    /// Policy of the creator. We keep the `Option` wrapper
    /// in order that the user can be warned that they are using a policy.
    /// Thus there is a distinction between `Some(Vec::new())` and `None`.
    pub(crate) policies:  Option<Vec<TestPolicy>>,
}

/// Context used for testing. The type parameter C is used to determine whether
/// this will be an init or receive context.
#[derive(Default, Clone)]
pub struct TestContext<'a, C> {
    pub(crate) common: TestCommonData<'a>,
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
/// ```rust
/// # use concordium_std::*;
/// # use concordium_std::test_infrastructure::*;
/// let mut ctx = TestInitContext::empty();
/// ctx.set_init_origin(AccountAddress([0u8; 32]));
/// ```
/// ## Set chain meta data
/// Chain meta data is set using setters on the context or by setters on a
/// mutable reference of [`TestChainMeta`](struct.TestChainMeta.html).
///
/// ### Example
/// Creating an empty context and setting the `slot_time` metadata.
/// ```rust
/// # use concordium_std::*;
/// # use concordium_std::test_infrastructure::*;
/// let mut ctx = TestInitContext::empty();
/// ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(1609459200));
/// ```
/// or
/// ```rust
/// # use concordium_std::*;
/// # use concordium_std::test_infrastructure::*;
/// let mut ctx = TestInitContext::empty();
/// ctx.metadata_mut().set_slot_time(Timestamp::from_timestamp_millis(1609459200));
/// ```
///
/// # Use case example
///
/// ```rust
/// # use concordium_std::*;
/// type ParameterType = u64;
/// #[init(contract = "noop", parameter = "ParameterType")]
/// fn contract_init<S: HasStateApi>(
///     ctx: &impl HasInitContext,
///     state_builder: &mut StateBuilder<S>,
/// ) -> InitResult<()> {
///     let init_origin = ctx.init_origin();
///     let parameter: ParameterType = ctx.parameter_cursor().get()?;
///     Ok(())
/// }
///
/// #[cfg(test)]
/// mod tests {
///     use super::*;
///     use concordium_std::test_infrastructure::*;
///     #[test]
///     fn test() {
///         let ctx = TestInitContext::empty();
///         let mut state_builder = TestStateBuilder::new();
///         ctx.set_init_origin(AccountAddress([0u8; 32]));
///         let result = contract_init(&ctx, &mut state_builder);
///         // Reads the init_origin without any problems.
///         // But then fails because the parameter is not set.
///     }
/// }
/// ```
pub type TestInitContext<'a> = TestContext<'a, TestInitOnlyData>;

#[derive(Default)]
#[doc(hidden)]
pub struct TestInitOnlyData {
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
/// ```rust
/// # use concordium_std::*;
/// # use concordium_std::test_infrastructure::*;
/// let owner = AccountAddress([0u8; 32]);
/// let mut ctx = TestReceiveContext::empty();
/// ctx.set_owner(owner);
/// ctx.set_sender(Address::Account(owner));
/// ```
/// ## Set chain meta data
/// Chain meta data is set using setters on the context or by setters on a
/// mutable reference of [`TestChainMeta`](struct.TestChainMeta.html).
///
/// ### Example
/// Creating an empty context and setting the `slot_time` metadata.
/// ```rust
/// # use concordium_std::*;
/// # use concordium_std::test_infrastructure::*;
/// let mut ctx = TestReceiveContext::empty();
/// ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(1609459200));
/// ```
/// or
/// ```rust
/// # use concordium_std::*;
/// # use concordium_std::test_infrastructure::*;
/// let mut ctx = TestReceiveContext::empty();
/// ctx.metadata_mut().set_slot_time(Timestamp::from_timestamp_millis(1609459200));
/// ```
///
/// # Use case example
/// Creating a context for running unit tests
/// ```rust
/// # use concordium_std::*;
/// # type ReceiveResult<A> = Result<A, ParseError>;
/// # type State = u64;
/// #[receive(contract = "mycontract", name = "receive", mutable)]
/// fn contract_receive<S: HasStateApi>(
///     ctx: &impl HasReceiveContext,
///     host: &mut impl HasHost<State, StateApiType = S>,
/// ) -> ReceiveResult<()> {
///     ensure!(ctx.sender().matches_account(&ctx.owner()));
///     // ...
///     Ok(())
/// }
///
/// #[cfg(test)]
/// mod tests {
///     use super::*;
///     use concordium_sc_base::test_infrastructure::*;
///     #[test]
///     fn test() {
///         let owner = AccountAddress([0u8; 32]);
///         let mut ctx = TestReceiveContext::empty();
///         ctx.set_owner(owner);
///         ctx.set_sender(Address::Account(owner));
///         // ...
///         let result: ReceiveResult<ActionsTree> = contract_receive(&ctx, 0, &mut logger, state);
///     }
/// }
/// ```
pub type TestReceiveContext<'a> = TestContext<'a, TestReceiveOnlyData>;

#[derive(Default)]
#[doc(hidden)]
pub struct TestReceiveOnlyData {
    pub(crate) invoker:          Option<AccountAddress>,
    pub(crate) self_address:     Option<ContractAddress>,
    pub(crate) sender:           Option<Address>,
    pub(crate) owner:            Option<AccountAddress>,
    pub(crate) named_entrypoint: Option<OwnedEntrypointName>,
}

// Setters for testing-context
impl TestChainMeta {
    /// Create an `TestChainMeta` where every field is unset, and getting any of
    /// the fields will result in [`fail!`](../macro.fail.html).
    pub fn empty() -> Self { Default::default() }

    /// Set the block slot time
    pub fn set_slot_time(&mut self, value: SlotTime) -> &mut Self {
        self.slot_time = Some(value);
        self
    }
}

impl<'a, C> TestContext<'a, C> {
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
    pub fn metadata_mut(&mut self) -> &mut TestChainMeta { &mut self.common.metadata }

    /// Set the metadata block slot time
    pub fn set_metadata_slot_time(&mut self, value: SlotTime) -> &mut Self {
        self.metadata_mut().set_slot_time(value);
        self
    }
}

impl<'a> TestInitContext<'a> {
    /// Create an `TestInitContext` where every field is unset, and getting any
    /// of the fields will result in [`fail!`](../macro.fail.html).
    pub fn empty() -> Self { Default::default() }

    /// Set `init_origin` in the `TestInitContext`
    pub fn set_init_origin(&mut self, value: AccountAddress) -> &mut Self {
        self.custom.init_origin = Some(value);
        self
    }
}

impl<'a> TestReceiveContext<'a> {
    /// Create a `TestReceiveContext` where every field is unset, and getting
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

    pub fn set_named_entrypoint(&mut self, value: OwnedEntrypointName) -> &mut Self {
        self.custom.named_entrypoint = Some(value);
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
impl HasChainMetadata for TestChainMeta {
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

impl<'a, C> HasCommonData for TestContext<'a, C> {
    type MetadataType = TestChainMeta;
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

impl<'a> HasInitContext for TestInitContext<'a> {
    type InitData = ();

    fn open(_data: Self::InitData) -> Self { TestInitContext::default() }

    fn init_origin(&self) -> AccountAddress {
        unwrap_ctx_field(self.custom.init_origin, "init_origin")
    }
}

impl<'a> HasReceiveContext for TestReceiveContext<'a> {
    type ReceiveData = ();

    fn open(_data: Self::ReceiveData) -> Self { TestReceiveContext::default() }

    fn invoker(&self) -> AccountAddress { unwrap_ctx_field(self.custom.invoker, "invoker") }

    fn self_address(&self) -> ContractAddress {
        unwrap_ctx_field(self.custom.self_address, "self_address")
    }

    fn sender(&self) -> Address { unwrap_ctx_field(self.custom.sender, "sender") }

    fn owner(&self) -> AccountAddress { unwrap_ctx_field(self.custom.owner, "owner") }

    fn named_entrypoint(&self) -> OwnedEntrypointName {
        unwrap_ctx_field(self.custom.named_entrypoint.clone(), "named_entrypoint")
    }
}

impl<'a> HasParameter for Cursor<&'a [u8]> {
    fn size(&self) -> u32 { self.data.len() as u32 }
}

/// A logger that simply accumulates all the logged items to be inspected at the
/// end of execution.
pub struct TestLogger {
    pub logs: Vec<Vec<u8>>,
}

impl HasLogger for TestLogger {
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
/// An error that is raised when operating with `Seek`, `Write`, `Read`, or
/// `HasStateEntry` trait methods of the `TestStateApi` type.
pub enum TestStateError {
    /// The computation of the new offset would result in an overflow.
    Overflow,
    /// An error occurred when writing to the contract state.
    Write,
    /// The new offset would be out of bounds of the state.
    Offset,
    /// Some other error occurred.
    Default,
    /// The entry has been deleted (via delete_prefix).
    EntryDeleted,
}

impl Default for TestStateError {
    fn default() -> Self { Self::Default }
}

impl From<num::TryFromIntError> for TestStateError {
    fn from(_: num::TryFromIntError) -> Self { TestStateError::Overflow }
}

impl From<TestStateError> for ParseError {
    fn from(_: TestStateError) -> Self { ParseError::default() }
}

#[derive(Debug)]
/// A wrapper for the data stored in [`TestStateEntry`], which is used to match
/// the semantics of the host functions. Specifically, it is used to ensure that
/// interactions with a deleted entry result in a error.
pub enum TestStateEntryData {
    /// The entry has been deleted.
    EntryDeleted,
    /// The entry exists and has data.
    EntryExists(Vec<u8>),
}

impl TestStateEntryData {
    /// Create a new TestStateEntryData::EntryExists with the data given.
    pub(crate) fn new_from(data: Vec<u8>) -> Self { Self::EntryExists(data) }

    /// Create a new TestStateEntryData::EntryExists with a new Vec.
    pub(crate) fn new() -> Self { Self::EntryExists(Vec::new()) }

    /// Tries to get the actual data. Returns an error if the entry has been
    /// deleted.
    pub(crate) fn data(&self) -> Result<&[u8], TestStateError> {
        match self {
            TestStateEntryData::EntryDeleted => Err(TestStateError::EntryDeleted),
            TestStateEntryData::EntryExists(v) => Ok(v),
        }
    }

    /// Tries to get the actual data as mutable. Returns an error if the entry
    /// has been deleted.
    pub(crate) fn data_mut(&mut self) -> Result<&mut Vec<u8>, TestStateError> {
        match self {
            TestStateEntryData::EntryDeleted => Err(TestStateError::EntryDeleted),
            TestStateEntryData::EntryExists(v) => Ok(v),
        }
    }
}

impl From<Vec<u8>> for TestStateEntryData {
    fn from(data: Vec<u8>) -> Self { Self::new_from(data) }
}

#[derive(Debug)]
/// A state entry used for testing. Implements [`HasStateEntry`].
pub struct TestStateEntry {
    pub(crate) cursor:         Cursor<Rc<RefCell<TestStateEntryData>>>,
    pub(crate) key:            Vec<u8>,
    pub(crate) state_entry_id: StateEntryId,
}

impl TestStateEntry {
    pub(crate) fn open(
        data: Rc<RefCell<TestStateEntryData>>,
        key: Vec<u8>,
        state_entry_id: StateEntryId,
    ) -> Self {
        Self {
            cursor: Cursor::new(data),
            key,
            state_entry_id,
        }
    }
}

#[derive(Debug, Clone)]
/// A state api used for testing. Implement [`HasStateApi`].
pub struct TestStateApi {
    trie: Rc<RefCell<StateTrie>>,
}

impl HasStateApi for TestStateApi {
    type EntryType = TestStateEntry;
    type IterType = trie::TestStateIter;

    fn create_entry(&mut self, key: &[u8]) -> Result<Self::EntryType, StateError> {
        self.trie.borrow_mut().create_entry(key)
    }

    fn lookup_entry(&self, key: &[u8]) -> Option<Self::EntryType> { self.trie.borrow().lookup(key) }

    fn delete_entry(&mut self, entry: Self::EntryType) -> Result<(), StateError> {
        self.trie.borrow_mut().delete_entry(entry)
    }

    fn delete_prefix(&mut self, prefix: &[u8]) -> Result<bool, StateError> {
        self.trie.borrow_mut().delete_prefix(prefix)
    }

    fn iterator(&self, prefix: &[u8]) -> Result<Self::IterType, StateError> {
        self.trie.borrow().iterator(prefix)
    }

    fn delete_iterator(&mut self, iter: Self::IterType) {
        self.trie.borrow_mut().delete_iterator(iter);
    }
}

/// An alias for [`StateMapIter`] that fixes the [`HasStateApi`] type to
/// [`TestStateApi`].
pub type TestStateMapIter<'a, K, V> = StateMapIter<'a, K, V, TestStateApi>;

/// An alias for [`StateMapIterMut`] that fixes the [`HasStateApi`] type to
/// [`TestStateApi`].
pub type TestStateMapIterMut<'a, K, V> = StateMapIterMut<'a, K, V, TestStateApi>;

/// An alias for [`StateSetIter`] that fixes the [`HasStateApi`] type to
/// [`TestStateApi`].
pub type TestStateSetIter<'a, T> = StateSetIter<'a, T, TestStateApi>;

impl TestStateApi {
    /// Create a new empty state.
    pub fn new() -> Self {
        Self {
            trie: Rc::new(RefCell::new(StateTrie::new())),
        }
    }
}

impl Default for TestStateApi {
    fn default() -> Self { Self::new() }
}

// Type alias for [`StateBuilder`], which fixes the [`HasHost`] type to
// [`TestStateApi`].
pub type TestStateBuilder = StateBuilder<TestStateApi>;

impl TestStateBuilder {
    /// Create a new [`Self`] with an empty [`TestStateApi`].
    pub fn new() -> Self { Self::open(TestStateApi::new()) }
}

impl HasStateEntry for TestStateEntry {
    type Error = TestStateError;
    type StateEntryData = Rc<RefCell<TestStateEntryData>>;
    type StateEntryKey = Vec<u8>;

    #[inline(always)]
    fn move_to_start(&mut self) { self.cursor.offset = 0; }

    /// Get the size of the data in the entry.
    /// Returns an error if the entry has been deleted with delete_prefix.
    fn size(&self) -> Result<u32, Self::Error> {
        Ok(self.cursor.data.borrow().data()?.len() as u32)
    }

    /// Truncate the entry.
    /// Returns an error if the entry has been deleted with delete_prefix.
    fn truncate(&mut self, new_size: u32) -> Result<(), Self::Error> {
        let cur_size = self.size()?;
        if cur_size > new_size {
            self.resize(new_size)?;
        }
        Ok(())
    }

    /// Get a reference to the key.
    fn get_key(&self) -> &[u8] { &self.key }

    /// Resize the entry.
    /// Returns an error if the entry has been deleted with delete_prefix.
    fn resize(&mut self, new_size: u32) -> Result<(), Self::Error> {
        let new_size = new_size as usize;
        self.cursor.data.borrow_mut().data_mut()?.resize(new_size, 0);
        if self.cursor.offset > new_size {
            self.cursor.offset = new_size;
        }
        Ok(())
    }
}

impl Read for TestStateEntry {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
        let mut len = self.cursor.data.borrow().data()?.len() - self.cursor.offset;
        if len > buf.len() {
            len = buf.len();
        }
        if len > 0 {
            buf[0..len].copy_from_slice(
                &self.cursor.data.borrow().data()?[self.cursor.offset..self.cursor.offset + len],
            );
            self.cursor.offset += len;
            Ok(len)
        } else {
            Ok(0)
        }
    }
}

impl Write for TestStateEntry {
    type Err = TestStateError;

    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Err> {
        let end = self.cursor.offset + buf.len();
        if self.cursor.data.borrow().data()?.len() < end {
            self.resize(end.try_into()?)?;
        }
        let mut cursor_data = self.cursor.data.as_ref().borrow_mut();
        let data = &mut cursor_data.data_mut()?[self.cursor.offset..];
        let to_write = cmp::min(data.len(), buf.len());
        data[..to_write].copy_from_slice(&buf[..to_write]);
        self.cursor.offset += to_write;
        Ok(to_write)
    }
}

impl Seek for TestStateEntry {
    type Err = TestStateError;

    // TODO: This does _not_ match the semantics of Seek for StateEntry.
    fn seek(&mut self, pos: SeekFrom) -> Result<u32, Self::Err> {
        use self::TestStateError::*;
        // This will fail immediately, if the entry has been deleted.
        let len = self.cursor.data.borrow().data()?.len();
        match pos {
            SeekFrom::Start(x) => {
                // We can set the position to just after the end of the current length.
                let new_offset = x.try_into()?;
                if new_offset <= len {
                    self.cursor.offset = new_offset;
                    Ok(x)
                } else {
                    Err(Offset)
                }
            }
            SeekFrom::End(x) => {
                // cannot seek beyond end, nor before beginning
                if x <= 0 {
                    let end: u32 = len.try_into()?;
                    let minus_x = x.checked_abs().ok_or(Overflow)?;
                    if let Some(new_pos) = end.checked_sub(minus_x.try_into()?) {
                        self.cursor.offset = new_pos.try_into()?;
                        Ok(new_pos)
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
                    if new_pos <= len {
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
type TestMockFn<State> =
    Box<dyn Fn(Parameter, Amount, &mut Amount, &mut State) -> CallContractResult<Cursor<Vec<u8>>>>;

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
    pub fn new<R, F>(mock_fn_return: F) -> Self
    where
        R: Serial,
        F: Fn(Parameter, Amount, &mut Amount, &mut State) -> CallContractResult<R> + 'static, {
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
    pub fn new_v1<R, F>(mock_fn_return: F) -> Self
    where
        R: Serial,
        F: Fn(
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
    pub fn new_v0<R, F>(mock_fn_return: F) -> Self
    where
        R: Serial,
        F: Fn(Parameter, Amount, &mut Amount, &mut State) -> Result<bool, CallContractError<R>>
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

/// A [`Host`](HasHost) implementation used for unit testing smart contracts.
///
/// The host provides a way to set up mock responses to transfers, and to
/// contract invocations. This allows testing a specific entrypoint of a
/// contract in isolation, assuming its dependents behave in the way specified
/// by the supplied mock functions.
///
/// Additionally, this host provides some inspection capability so that after
/// execution of an entrypoint tests can observe which accounts or contracts
/// were affected.
pub struct TestHost<State> {
    /// Functions that mock responses to calls.
    mocking_fns:      BTreeMap<(ContractAddress, OwnedEntrypointName), MockFn<State>>,
    /// Transfers the contract has made during its execution.
    transfers:        RefCell<Vec<(AccountAddress, Amount)>>,
    /// The contract balance. This is updated during execution based on contract
    /// invocations, e.g., a successful transfer from the contract decreases it.
    contract_balance: RefCell<Amount>,
    /// StateBuilder for the state.
    state_builder:    StateBuilder<TestStateApi>,
    /// State of the instance.
    state:            State,
    /// List of accounts that will cause a contract invocation to fail.
    missing_accounts: BTreeSet<AccountAddress>,
}

impl<State: Serial + DeserialWithState<TestStateApi>> HasHost<State> for TestHost<State> {
    type ReturnValueType = Cursor<Vec<u8>>;
    type StateApiType = TestStateApi;

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
    fn invoke_transfer(&self, receiver: &AccountAddress, amount: Amount) -> TransferResult {
        if self.missing_accounts.contains(receiver) {
            return Err(TransferError::MissingAccount);
        }
        if amount.micro_ccd > 0 {
            if *self.contract_balance.borrow() >= amount {
                *self.contract_balance.borrow_mut() -= amount;
                self.transfers.borrow_mut().push((*receiver, amount));
                Ok(())
            } else {
                Err(TransferError::AmountTooLarge)
            }
        } else {
            self.transfers.borrow_mut().push((*receiver, amount));
            Ok(())
        }
    }

    /// Invoke a contract entrypoint.
    ///
    /// This uses the mock entrypoints set up with
    /// `setup_mock_entrypoint`. The method will [fail] with a panic
    /// if no responses were set for the given contract address and method.
    fn invoke_contract_raw(
        &mut self,
        to: &ContractAddress,
        parameter: Parameter,
        method: EntrypointName,
        amount: Amount,
    ) -> CallContractResult<Self::ReturnValueType> {
        self.commit_state();
        let handler = match self.mocking_fns.get_mut(&(*to, OwnedEntrypointName::from(method))) {
            Some(handler) => handler,
            None => fail!(
                "Mocking has not been set up for invoking contract {:?} with method '{}'.",
                to,
                method
            ),
        };

        // Check if the contract has sufficient balance.
        if amount.micro_ccd > 0 && *self.contract_balance.borrow() < amount {
            return Err(CallContractError::AmountTooLarge);
        }
        // Invoke the handler.
        let (state_modified, res) = (handler.f)(
            parameter,
            amount,
            &mut self.contract_balance.borrow_mut(),
            &mut self.state,
        )?;

        // Update the contract balance if the invocation succeeded.
        if amount.micro_ccd > 0 {
            *self.contract_balance.borrow_mut() -= amount;
        }
        // since the caller only modified (in principle) the in-memory state,
        // we make sure to persist it to reflect what happens in actual calls
        if state_modified {
            self.commit_state();
        }
        Ok((state_modified, res))
    }

    /// Invoke a contract entrypoint.
    ///
    /// This uses the mock entrypoints set up with
    /// `setup_mock_entrypoint`. The method will [fail] with a panic
    /// if no responses were set for the given contract address and method.
    fn invoke_contract_raw_read_only(
        &self,
        to: &ContractAddress,
        parameter: Parameter,
        method: EntrypointName,
        amount: Amount,
    ) -> ReadOnlyCallContractResult<Self::ReturnValueType> {
        let handler = match self.mocking_fns.get(&(*to, OwnedEntrypointName::from(method))) {
            Some(handler) => handler,
            None => fail!(
                "Mocking has not been set up for invoking contract {:?} with method '{}'.",
                to,
                method
            ),
        };
        // Check if the contract has sufficient balance.
        if amount.micro_ccd > 0 && *self.contract_balance.borrow() < amount {
            return Err(CallContractError::AmountTooLarge);
        }

        // The callee will see state that is stored at this point.
        let mut state = match State::deserial_with_state(
            &self.state_builder.state_api,
            &mut self
                .state_builder
                .state_api
                .lookup_entry(&[])
                .expect_report("Could not lookup the state root."),
        ) {
            Ok(state) => state,
            Err(e) => fail!("Failed to deserialize state: {:?}", e),
        };

        // Invoke the handler.
        let (state_modified, res) =
            (handler.f)(parameter, amount, &mut self.contract_balance.borrow_mut(), &mut state)?;
        if state_modified {
            fail!("State modified in a read-only contract call.");
        }
        // Update the contract balance if the invocation succeeded.
        if amount.micro_ccd > 0 {
            *self.contract_balance.borrow_mut() -= amount;
        }
        Ok(res)
    }

    fn commit_state(&mut self) {
        let mut root_entry = self
            .state_builder
            .state_api
            .lookup_entry(&[])
            .expect_report("commit_state: Cannot lookup state root.");
        self.state.serial(&mut root_entry).expect_report("commit_state: Cannot serialize state.");
        let new_state_size = root_entry
            .size()
            .expect_report("commit_state: Cannot get state size. Entry was deleted.");
        root_entry
            .truncate(new_state_size)
            .expect_report("commit_state: Cannot truncate state. Entry was deleted.");
    }

    /// Get an immutable reference to the contract state.
    fn state(&self) -> &State { &self.state }

    /// Get a mutable reference to the contract state.
    fn state_mut(&mut self) -> &mut State { &mut self.state }

    /// Get the contract balance.
    /// This can be set with `set_self_balance` and defaults to 0.
    fn self_balance(&self) -> Amount { *self.contract_balance.borrow() }

    fn state_builder(&mut self) -> &mut StateBuilder<Self::StateApiType> { &mut self.state_builder }

    fn state_and_builder(&mut self) -> (&mut State, &mut StateBuilder<Self::StateApiType>) {
        (&mut self.state, &mut self.state_builder)
    }
}

impl<State: Serial + DeserialWithState<TestStateApi>> TestHost<State> {
    /// Create a new test host. **It is essential that any [`StateMap`],
    /// [`StateSet`] or [`StateBox`] that exists in the provided `state` was
    /// created with the `state_builder` that is supplied. Otherwise the
    /// runtime error in the test.
    pub fn new(state: State, mut state_builder: StateBuilder<TestStateApi>) -> Self {
        let mut root_entry = state_builder
            .state_api
            .create_entry(&[])
            .expect_report("TestHost::new: Could not store state root.");
        state.serial(&mut root_entry).expect_report("TestHost::new: cannot serialize state.");
        Self {
            mocking_fns: BTreeMap::new(),
            transfers: RefCell::new(Vec::new()),
            contract_balance: RefCell::new(Amount::zero()),
            state_builder,
            state,
            missing_accounts: BTreeSet::new(),
        }
    }

    /// Retrieve a reference to the underlying state builder.
    pub fn state_builder(&mut self) -> &mut StateBuilder<TestStateApi> { &mut self.state_builder }

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
    /// ```rust
    /// # use concordium_std::*;
    /// # use concordium_std::test_infrastructure::*;
    /// # fn contract_receive<S: HasStateApi>(
    /// #    ctx: &impl HasReceiveContext,
    /// #    host: &mut impl HasHost<u64, StateApiType = S>,
    /// #    amount: Amount,
    /// # ) -> ReceiveResult<()> {
    /// #    Ok(())
    /// # }
    /// # let mut host = TestHost::new(0u64, TestStateBuilder::new());
    /// # let ctx = TestReceiveContext::empty();
    /// host.set_self_balance(Amount::from_ccd(10));
    /// contract_receive(
    ///     &ctx,
    ///     &mut host,
    ///     // This amount is _not_ added to the balance of the contract,
    ///     // so calling `host.self_balance()` will return `10` initially.
    ///     // When a contract is executed by the node the amount that is being sent (`5`)
    ///     // is added to the balance of the contract, so that `host.self_balance()`
    ///     // already observes it.
    ///     Amount::from_ccd(5),
    /// );
    /// ```
    pub fn set_self_balance(&mut self, amount: Amount) {
        *self.contract_balance.borrow_mut() = amount;
    }

    /// Check whether a given transfer occured.
    pub fn transfer_occurred(&self, receiver: &AccountAddress, amount: Amount) -> bool {
        self.transfers.borrow().contains(&(*receiver, amount))
    }

    /// Get a list of all transfers that have occurred, in the order they
    /// occurred in.
    pub fn get_transfers(&self) -> Vec<(AccountAddress, Amount)> {
        self.transfers.borrow().to_vec()
    }

    /// Get a list of all transfers to a specific account.
    pub fn get_transfers_to(&self, account: AccountAddress) -> Vec<Amount> {
        self.transfers
            .borrow()
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
    use super::TestStateApi;
    use crate::{
        cell::RefCell,
        rc::Rc,
        test_infrastructure::{TestStateBuilder, TestStateEntry},
        Deletable, EntryRaw, HasStateApi, HasStateEntry, StateMap, StateSet,
        INITIAL_NEXT_ITEM_PREFIX,
    };
    use concordium_contracts_common::{to_bytes, Deserial, Read, Seek, SeekFrom, Write};

    #[test]
    // Perform a number of operations from Seek, Read, Write and HasStateApi
    // classes on the TestStateApi structure and check that they behave as
    // specified.
    fn test_contract_state() {
        let data = Rc::new(RefCell::new(vec![1; 100].into()));
        let mut state = TestStateEntry::open(data, Vec::new(), 0);
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
        assert_eq!(
            &buf[0..20],
            &state.cursor.data.borrow().data().expect("Entry was deleted")[80..100],
            "Incorrect data was read."
        );
        assert_eq!(
            state.cursor.offset, 122,
            "After reading the offset is in the correct position."
        );
        assert!(state.reserve(222).is_ok(), "Could not increase state to 222.");
        assert_eq!(state.write(&[2; 100]), Ok(100), "Should have written 100 bytes.");
        assert_eq!(state.cursor.offset, 222, "After writing the offset should be 200.");
        state.truncate(50).expect("Could not truncate state to 50.");
        assert_eq!(state.cursor.offset, 50, "After truncation the state should be 50.");
        assert_eq!(
            state.write(&[1; 1000]),
            Ok(1000),
            "Writing at the end after truncation should succeed."
        );
    }

    #[test]
    fn test_contract_state_write() {
        let data = Rc::new(RefCell::new(vec![0u8; 10].into()));
        let mut state = TestStateEntry::open(data, Vec::new(), 0);
        assert_eq!(state.write(&1u64.to_le_bytes()), Ok(8), "Incorrect number of bytes written.");
        assert_eq!(
            state.write(&2u64.to_le_bytes()),
            Ok(8),
            "State should be resized automatically."
        );
        assert_eq!(state.cursor.offset, 16, "Pos should be at the end.");
        assert_eq!(
            *state.cursor.data.as_ref().borrow().data().expect("Entry was deleted"),
            vec![1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
            "Correct data was written."
        );
    }

    #[test]
    fn high_level_insert_get() {
        let expected_value: u64 = 123123123;
        let mut state_builder = TestStateBuilder::new();
        state_builder.insert(0, expected_value).expect("Insert failed");
        let actual_value: u64 = state_builder.get(0).expect("Not found").expect("Not a valid u64");
        assert_eq!(expected_value, actual_value);
    }

    #[test]
    fn low_level_entry() {
        let expected_value: u64 = 123123123;
        let key = to_bytes(&42u64);
        let mut state = TestStateApi::new();
        state
            .entry(&key[..])
            .or_insert_raw(&to_bytes(&expected_value))
            .expect("No iterators, so insertion should work.");

        match state.entry(key) {
            EntryRaw::Vacant(_) => panic!("Unexpected vacant entry."),
            EntryRaw::Occupied(occ) => {
                assert_eq!(u64::deserial(&mut occ.get()), Ok(expected_value))
            }
        }
    }

    #[test]
    fn high_level_statemap() {
        let my_map_key = "my_map";
        let mut state_builder = TestStateBuilder::new();

        let map_to_insert = state_builder.new_map::<String, String>();
        state_builder.insert(my_map_key, map_to_insert).expect("Insert failed");

        let mut my_map: StateMap<String, String, _> = state_builder
            .get(my_map_key)
            .expect("Could not get statemap")
            .expect("Deserializing statemap failed");
        my_map.insert("abc".to_string(), "hello, world".to_string());
        my_map.insert("def".to_string(), "hallo, Weld".to_string());
        my_map.insert("ghi".to_string(), "hej, verden".to_string());
        assert_eq!(*my_map.get(&"abc".to_string()).unwrap(), "hello, world".to_string());

        let mut iter = my_map.iter();
        let (k1, v1) = iter.next().unwrap();
        assert_eq!(*k1, "abc".to_string());
        assert_eq!(*v1, "hello, world".to_string());
        let (k2, v2) = iter.next().unwrap();
        assert_eq!(*k2, "def".to_string());
        assert_eq!(*v2, "hallo, Weld".to_string());
        let (k3, v3) = iter.next().unwrap();
        assert_eq!(*k3, "ghi".to_string());
        assert_eq!(*v3, "hej, verden".to_string());
        assert!(iter.next().is_none());
    }

    #[test]
    fn statemap_insert_remove() {
        let mut state_builder = TestStateBuilder::new();
        let mut map = state_builder.new_map();
        let value = String::from("hello");
        let _ = map.insert(42, value.clone());
        assert_eq!(*map.get(&42).unwrap(), value);
        map.remove(&42);
        assert!(map.get(&42).is_none());
    }

    #[test]
    fn statemap_clear() {
        let mut state_builder = TestStateBuilder::new();
        let mut map = state_builder.new_map();
        let _ = map.insert(1, 2);
        let _ = map.insert(2, 3);
        let _ = map.insert(3, 4);
        map.clear();
        assert!(map.is_empty());
    }

    #[test]
    fn high_level_nested_statemaps() {
        let inner_map_key = 0u8;
        let key_to_value = 77u8;
        let value = 255u8;
        let mut state_builder = TestStateBuilder::new();
        let mut outer_map = state_builder.new_map::<u8, StateMap<u8, u8, _>>();
        let mut inner_map = state_builder.new_map::<u8, u8>();

        inner_map.insert(key_to_value, value);
        outer_map.insert(inner_map_key, inner_map);

        assert_eq!(*outer_map.get(&inner_map_key).unwrap().get(&key_to_value).unwrap(), value);
    }

    #[test]
    fn statemap_iter_mut_works() {
        let mut state_builder = TestStateBuilder::new();
        let mut map = state_builder.new_map();
        map.insert(0u8, 1u8);
        map.insert(1u8, 2u8);
        map.insert(2u8, 3u8);
        for (_, mut v) in map.iter_mut() {
            v.update(|old_value| *old_value += 10);
        }
        let mut iter = map.iter();
        let (k1, v1) = iter.next().unwrap();
        assert_eq!(*k1, 0);
        assert_eq!(*v1, 11);
        let (k2, v2) = iter.next().unwrap();
        assert_eq!(*k2, 1);
        assert_eq!(*v2, 12);
        let (k3, v3) = iter.next().unwrap();
        assert_eq!(*k3, 2);
        assert_eq!(*v3, 13);
        assert!(iter.next().is_none());
    }

    #[test]
    fn iter_mut_works_on_nested_statemaps() {
        let mut state_builder = TestStateBuilder::new();
        let mut outer_map = state_builder.new_map();
        let mut inner_map = state_builder.new_map();
        inner_map.insert(0u8, 1u8);
        inner_map.insert(1u8, 2u8);
        outer_map.insert(99u8, inner_map);
        for (_, mut v_map) in outer_map.iter_mut() {
            v_map.update(|v_map| {
                for (_, mut inner_v) in v_map.iter_mut() {
                    inner_v.update(|inner_v| *inner_v += 10);
                }
            });
        }

        // Check the outer map.
        let mut outer_iter = outer_map.iter();
        let (inner_map_key, inner_map) = outer_iter.next().unwrap();
        assert_eq!(*inner_map_key, 99);
        assert!(outer_iter.next().is_none());

        // Check the inner map.
        let mut inner_iter = inner_map.iter();
        let (k1, v1) = inner_iter.next().unwrap();
        assert_eq!(*k1, 0);
        assert_eq!(*v1, 11);
        let (k2, v2) = inner_iter.next().unwrap();
        assert_eq!(*k2, 1);
        assert_eq!(*v2, 12);
        assert!(inner_iter.next().is_none());
    }

    #[test]
    fn statemap_iterator_unlocks_tree_once_dropped() {
        let mut state_builder = TestStateBuilder::new();
        let mut map = state_builder.new_map();
        map.insert(0u8, 1u8);
        map.insert(1u8, 2u8);
        {
            let _iter = map.iter();
            // Uncommenting these two lines (and making iter mutable) should
            // give a compile error:
            //
            // map.insert(2u8, 3u8);
            // let n = iter.next();
        } // iter is dropped here, unlocking the subtree.
        map.insert(2u8, 3u8);
    }

    #[test]
    fn high_level_stateset() {
        let my_set_key = "my_set";
        let mut state_builder = TestStateBuilder::new();

        let mut set = state_builder.new_set::<u8>();
        assert!(set.insert(0));
        assert!(set.insert(1));
        assert!(!set.insert(1));
        assert!(set.insert(2));
        assert!(set.remove(&2));
        state_builder.insert(my_set_key, set).expect("Insert failed");

        assert!(state_builder.get::<_, StateSet<u8, _>>(my_set_key).unwrap().unwrap().contains(&0),);
        assert!(!state_builder
            .get::<_, StateSet<u8, _>>(my_set_key)
            .unwrap()
            .unwrap()
            .contains(&2),);

        let set = state_builder.get::<_, StateSet<u8, _>>(my_set_key).unwrap().unwrap();
        let mut iter = set.iter();
        assert_eq!(*iter.next().unwrap(), 0);
        assert_eq!(*iter.next().unwrap(), 1);
        assert!(iter.next().is_none());
    }

    #[test]
    fn high_level_nested_stateset() {
        let inner_set_key = 0u8;
        let value = 255u8;
        let mut state_builder = TestStateBuilder::new();
        let mut outer_map = state_builder.new_map::<u8, StateSet<u8, _>>();
        let mut inner_set = state_builder.new_set::<u8>();

        inner_set.insert(value);
        outer_map.insert(inner_set_key, inner_set);

        assert!(outer_map.get(&inner_set_key).unwrap().contains(&value));
    }

    #[test]
    fn stateset_insert_remove() {
        let mut state_builder = TestStateBuilder::new();
        let mut set = state_builder.new_set();
        let _ = set.insert(42);
        assert!(set.contains(&42));
        set.remove(&42);
        assert!(!set.contains(&42));
    }

    #[test]
    fn stateset_clear() {
        let mut state_builder = TestStateBuilder::new();
        let mut set = state_builder.new_set();
        let _ = set.insert(1);
        let _ = set.insert(2);
        let _ = set.insert(3);
        set.clear();
        assert!(set.is_empty());
    }

    #[test]
    fn stateset_iterator_unlocks_tree_once_dropped() {
        let mut state_builder = TestStateBuilder::new();
        let mut set = state_builder.new_set();
        set.insert(0u8);
        set.insert(1);
        {
            let _iter = set.iter();
            // Uncommenting these two lines (and making iter mutable) should
            // give a compile error:
            //
            // set.insert(2);
            // let n = iter.next();
        } // iter is dropped here, unlocking the subtree.
        set.insert(2);
    }

    #[test]
    fn allocate_and_get_statebox() {
        let mut state_builder = TestStateBuilder::new();
        let boxed_value = String::from("I'm boxed");
        let statebox = state_builder.new_box(boxed_value.clone());
        assert_eq!(*statebox.get(), boxed_value);
    }

    #[test]
    fn a_new_entry_can_not_be_created_under_a_locked_subtree() {
        let expected_value: u64 = 123123123;
        let key = to_bytes(b"ab");
        let sub_key = to_bytes(b"abc");
        let mut state = TestStateApi::new();
        state
            .entry(&key[..])
            .or_insert_raw(&to_bytes(&expected_value))
            .expect("No iterators, so insertion should work.");
        assert!(state.iterator(&key).is_ok(), "Iterator should be present");
        let entry = state.create_entry(&sub_key);
        assert!(entry.is_err(), "Should not be able to create an entry under a locked subtree");
    }

    #[test]
    fn a_new_entry_can_be_created_under_a_different_subtree_in_same_super_tree() {
        let expected_value: u64 = 123123123;
        let key = to_bytes(b"abcd");
        let key2 = to_bytes(b"abe");
        let mut state = TestStateApi::new();
        state
            .entry(&key[..])
            .or_insert_raw(&to_bytes(&expected_value))
            .expect("No iterators, so insertion should work.");
        assert!(state.iterator(&key).is_ok(), "Iterator should be present");
        let entry = state.create_entry(&key2);
        assert!(entry.is_ok(), "Failed to create a new entry under a different subtree");
    }

    #[test]
    fn an_existing_entry_can_not_be_deleted_under_a_locked_subtree() {
        let expected_value: u64 = 123123123;
        let key = to_bytes(b"ab");
        let sub_key = to_bytes(b"abc");
        let mut state = TestStateApi::new();
        state
            .entry(&key[..])
            .or_insert_raw(&to_bytes(&expected_value))
            .expect("no iterators, so insertion should work.");
        let sub_entry = state
            .entry(sub_key)
            .or_insert_raw(&to_bytes(&expected_value))
            .expect("Should be possible to create the entry.");
        assert!(state.iterator(&key).is_ok(), "Iterator should be present");
        assert!(
            state.delete_entry(sub_entry).is_err(),
            "Should not be able to create an entry under a locked subtree"
        );
    }

    #[test]
    fn an_existing_entry_can_be_deleted_from_a_different_subtree_in_same_super_tree() {
        let expected_value: u64 = 123123123;
        let key = to_bytes(b"abcd");
        let key2 = to_bytes(b"abe");
        let mut state = TestStateApi::new();
        state
            .entry(&key[..])
            .or_insert_raw(&to_bytes(&expected_value))
            .expect("No iterators, so insertion should work.");
        let entry2 = state
            .entry(key2)
            .or_insert_raw(&to_bytes(&expected_value))
            .expect("Should be possible to create the entry.");
        assert!(state.iterator(&key).is_ok(), "Iterator should be present");
        assert!(
            state.delete_entry(entry2).is_ok(),
            "Failed to create a new entry under a different subtree"
        );
    }

    #[test]
    fn deleting_nested_stateboxes_works() {
        let mut state_builder = TestStateBuilder::new();
        let inner_box = state_builder.new_box(99u8);
        let middle_box = state_builder.new_box(inner_box);
        let outer_box = state_builder.new_box(middle_box);
        outer_box.delete();
        let mut iter = state_builder.state_api.iterator(&[]).expect("Could not get iterator");
        // The only remaining node should be the state_builder's next_item_prefix node.
        assert!(iter.nth(1).is_none());
    }

    #[test]
    fn clearing_statemap_with_stateboxes_works() {
        let mut state_builder = TestStateBuilder::new();
        let box1 = state_builder.new_box(1u8);
        let box2 = state_builder.new_box(2u8);
        let box3 = state_builder.new_box(3u8);
        let mut map = state_builder.new_map();
        map.insert(1u8, box1);
        map.insert(2u8, box2);
        map.insert(3u8, box3);
        map.clear();
        let mut iter = state_builder.state_api.iterator(&[]).expect("Could not get iterator");
        // The only remaining node should be the state_builder's next_item_prefix node.
        assert!(iter.nth(1).is_none());
    }

    #[test]
    fn clearing_nested_statemaps_works() {
        let mut state_builder = TestStateBuilder::new();
        let mut inner_map_1 = state_builder.new_map();
        inner_map_1.insert(1u8, 2u8);
        inner_map_1.insert(2u8, 3u8);
        inner_map_1.insert(3u8, 4u8);
        let mut inner_map_2 = state_builder.new_map();
        inner_map_2.insert(11u8, 12u8);
        inner_map_2.insert(12u8, 13u8);
        inner_map_2.insert(13u8, 14u8);
        let mut outer_map = state_builder.new_map();
        outer_map.insert(0u8, inner_map_1);
        outer_map.insert(1u8, inner_map_2);
        outer_map.clear();
        let iter = state_builder.state_api.iterator(&[]).expect("Could not get iterator");
        // The only remaining node should be the state_builder's next_item_prefix node.
        assert!(iter.skip(1).next().is_none());
    }

    #[test]
    fn multiple_entries_not_allowed() {
        let mut state_builder = TestStateBuilder::new();
        let mut map = state_builder.new_map();
        map.insert(0u8, 1u8);
        let e1 = map.entry(0u8);
        // Uncommenting this line should give a borrow-check error.
        // let e2 = map.entry(1u8);
        e1.and_modify(|v| *v += 1);
    }

    #[test]
    fn occupied_entry_truncates_leftover_data() {
        let mut state_builder = TestStateBuilder::new();
        let mut map = state_builder.new_map();
        map.insert(99u8, "A longer string that should be truncated".into());
        let a_short_string = "A short string".to_string();
        let expected_size = a_short_string.len() + 4; // 4 bytes for the length of the string.
        map.entry(99u8).and_modify(|v| *v = a_short_string);
        let actual_size = state_builder
            .state_api
            .lookup_entry(&[INITIAL_NEXT_ITEM_PREFIX[0], 0, 0, 0, 0, 0, 0, 0, 99])
            .expect("Lookup failed")
            .size()
            .expect("Getting size failed");
        assert_eq!(expected_size as u32, actual_size);
    }

    #[test]
    fn occupied_entry_raw_truncates_leftover_data() {
        let mut state = TestStateApi::new();
        state
            .entry([])
            .or_insert_raw(&to_bytes(&"A longer string that should be truncated"))
            .expect("No iterators, so insertion should work.");

        let a_short_string = "A short string";
        let expected_size = a_short_string.len() + 4; // 4 bytes for the length of the string.

        match state.entry([]) {
            EntryRaw::Vacant(_) => panic!("Entry is vacant"),
            EntryRaw::Occupied(mut occ) => occ.insert_raw(&to_bytes(&a_short_string)),
        }
        let actual_size =
            state.lookup_entry(&[]).expect("Lookup failed").size().expect("Getting size failed");
        assert_eq!(expected_size as u32, actual_size);
    }
}
