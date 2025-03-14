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

use self::trie::StateTrie;
use crate::{
    boxed::Box,
    cell::RefCell,
    cmp,
    num,
    rc::Rc,
    *,
};
use convert::TryInto;
#[cfg(feature = "concordium-quickcheck")]
use quickcheck::*;

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
    policy:   Policy<Rc<[(AttributeTag, AttributeValue)]>>,
}

impl TestPolicy {
    fn new(policy: OwnedPolicy) -> Self {
        let policy = Policy {
            identity_provider: policy.identity_provider,
            created_at:        policy.created_at,
            valid_to:          policy.valid_to,
            items:             policy.items.into(),
        };
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

/// Test parameter cursor.
/// Should not be constructed directly, use [TestReceiveContext] or
/// [TestInitContext].
pub struct TestParameterCursor<'a> {
    cursor: Cursor<&'a [u8]>,
}

impl<'a> TestParameterCursor<'a> {
    fn new(data: &'a [u8]) -> Self {
        TestParameterCursor {
            cursor: Cursor::new(data),
        }
    }
}

impl<'a> AsRef<[u8]> for TestParameterCursor<'a> {
    #[inline(always)]
    fn as_ref(&self) -> &[u8] { self.cursor.as_ref() }
}

impl<'a> Seek for TestParameterCursor<'a> {
    type Err = ();

    #[inline(always)]
    fn seek(&mut self, seek: SeekFrom) -> Result<u32, Self::Err> { self.cursor.seek(seek) }

    #[inline(always)]
    fn cursor_position(&self) -> u32 { self.cursor.cursor_position() }
}

impl<'a> Read for TestParameterCursor<'a> {
    #[inline(always)]
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> { self.cursor.read(buf) }
}

impl<'a> HasParameter for TestParameterCursor<'a> {}

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

pub struct TestIterator {
    items:    Rc<[(AttributeTag, AttributeValue)]>,
    position: usize,
}

impl HasPolicy for TestPolicy {
    type Iterator = TestIterator;

    fn identity_provider(&self) -> IdentityProvider { self.policy.identity_provider }

    fn created_at(&self) -> Timestamp { self.policy.created_at }

    fn valid_to(&self) -> Timestamp { self.policy.valid_to }

    fn next_item(&mut self, buf: &mut [u8; 31]) -> Option<(AttributeTag, u8)> {
        if let Some(item) = self.policy.items.get(self.position) {
            let len = item.1.as_ref().len();
            buf[0..len].copy_from_slice(item.1.as_ref());
            self.position += 1;
            Some((item.0, len as u8))
        } else {
            None
        }
    }

    fn attributes(&self) -> Self::Iterator {
        TestIterator {
            items:    self.policy.items.clone(),
            position: 0,
        }
    }
}

impl Iterator for TestIterator {
    type Item = (AttributeTag, AttributeValue);

    fn next(&mut self) -> Option<Self::Item> {
        let elem = self.items.get(self.position)?;
        self.position += 1;
        Some(*elem)
    }
}

impl<'a, C> HasCommonData for TestContext<'a, C> {
    type MetadataType = TestChainMeta;
    type ParamType = TestParameterCursor<'a>;
    type PolicyIteratorType = crate::vec::IntoIter<TestPolicy>;
    type PolicyType = TestPolicy;

    fn parameter_cursor(&self) -> Self::ParamType {
        TestParameterCursor::new(unwrap_ctx_field(self.common.parameter, "parameter"))
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

#[derive(Debug, Clone)]
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
/// A state api used for testing. Implements [`HasStateApi`].
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

/// A closure used in tests for mocking calls to
/// [`HasCryptoPrimitives::verify_ed25519_signature`].
#[cfg(not(feature = "crypto-primitives"))]
type MockFnVerifyEd25519 = Box<dyn FnMut(PublicKeyEd25519, SignatureEd25519, &[u8]) -> bool>;

/// A closure used in tests for mocking calls to
/// [`HasCryptoPrimitives::verify_ecdsa_secp256k1_signature`].
#[cfg(not(feature = "crypto-primitives"))]
type MockFnEcdsaSecp256k1 =
    Box<dyn FnMut(PublicKeyEcdsaSecp256k1, SignatureEcdsaSecp256k1, [u8; 32]) -> bool>;

/// A closure used in tests for mocking calls to
/// [`HasCryptoPrimitives::hash_sha2_256`],
/// [`HasCryptoPrimitives::hash_sha3_256`], or [`HasCryptoPrimitives::
/// hash_keccak_256`].
#[cfg(not(feature = "crypto-primitives"))]
type MockFnHash<T> = Box<dyn FnMut(&[u8]) -> T>;

/// A [`HasCryptoPrimitives`] implementation used for unit testing smart
/// contracts.
///
/// You can test smart contracts that use the cryptographic primitives in
/// two different ways:
///
/// 1. By setting up mock responses for the functions you need, for example with
///    the `setup_hash_sha_256_mock` method.
/// 2. Or, by using the actual implementations. For this, you need to enable the
///    "crypto-primitives" feature.
pub struct TestCryptoPrimitives {
    #[cfg(not(feature = "crypto-primitives"))]
    verify_ed25519_signature_mock:         RefCell<Option<MockFnVerifyEd25519>>,
    #[cfg(not(feature = "crypto-primitives"))]
    verify_ecdsa_secp256k1_signature_mock: RefCell<Option<MockFnEcdsaSecp256k1>>,
    #[cfg(not(feature = "crypto-primitives"))]
    hash_sha2_256_mock:                    RefCell<Option<MockFnHash<HashSha2256>>>,
    #[cfg(not(feature = "crypto-primitives"))]
    hash_sha3_256_mock:                    RefCell<Option<MockFnHash<HashSha3256>>>,
    #[cfg(not(feature = "crypto-primitives"))]
    hash_keccak_256_mock:                  RefCell<Option<MockFnHash<HashKeccak256>>>,
}

/// Create a new [`TestCryptoPrimitives`], for which no mocks has been set up.
impl Default for TestCryptoPrimitives {
    fn default() -> Self { Self::new() }
}

impl TestCryptoPrimitives {
    /// Create a new [`TestCryptoPrimitives`], for which no mocks has been set
    /// up.
    pub fn new() -> Self {
        #[cfg(not(feature = "crypto-primitives"))]
        return Self {
            verify_ed25519_signature_mock:         RefCell::new(None),
            verify_ecdsa_secp256k1_signature_mock: RefCell::new(None),
            hash_sha2_256_mock:                    RefCell::new(None),
            hash_sha3_256_mock:                    RefCell::new(None),
            hash_keccak_256_mock:                  RefCell::new(None),
        };
        #[cfg(feature = "crypto-primitives")]
        Self {}
    }

    #[cfg(not(feature = "crypto-primitives"))]
    /// Set up a mock for [`verify_ed25519_signature`][link].
    ///
    /// This is not available if the "crypto-primitives" feature is enabled. For
    /// more information on why, see the documentation of
    /// [`TestCryptoPrimitives`].
    ///
    /// [link]: HasCryptoPrimitives::verify_ed25519_signature
    pub fn setup_verify_ed25519_signature_mock<F>(&self, mock: F)
    where
        F: FnMut(PublicKeyEd25519, SignatureEd25519, &[u8]) -> bool + 'static, {
        *self.verify_ed25519_signature_mock.borrow_mut() = Some(Box::new(mock));
    }

    #[cfg(not(feature = "crypto-primitives"))]
    /// Set up a mock for [`verify_ecdsa_secp256k1_signature`][link].
    ///
    /// This is not available if the "crypto-primitives" feature is enabled. For
    /// more information on why, see the documentation of
    /// [`TestCryptoPrimitives`].
    ///
    /// [link]: HasCryptoPrimitives::verify_ecdsa_secp256k1_signature
    pub fn setup_verify_ecdsa_secp256k1_signature_mock<F>(&self, mock: F)
    where
        F: FnMut(PublicKeyEcdsaSecp256k1, SignatureEcdsaSecp256k1, [u8; 32]) -> bool + 'static,
    {
        *self.verify_ecdsa_secp256k1_signature_mock.borrow_mut() = Some(Box::new(mock));
    }

    #[cfg(not(feature = "crypto-primitives"))]
    /// Set up a mock for
    /// [`hash_sha2_256`](HasCryptoPrimitives::hash_sha2_256).
    ///
    /// This is not available if the "crypto-primitives" feature is enabled. For
    /// more information on why, see the documentation of
    /// [`TestCryptoPrimitives`].
    pub fn setup_hash_sha2_256_mock<F>(&self, mock: F)
    where
        F: FnMut(&[u8]) -> HashSha2256 + 'static, {
        *self.hash_sha2_256_mock.borrow_mut() = Some(Box::new(mock));
    }

    #[cfg(not(feature = "crypto-primitives"))]
    /// Set up a mock for
    /// [`hash_sha3_256`](HasCryptoPrimitives::hash_sha3_256).
    ///
    /// This is not available if the "crypto-primitives" feature is enabled. For
    /// more information on why, see the documentation of
    /// [`TestCryptoPrimitives`].
    pub fn setup_hash_sha3_256_mock<F>(&self, mock: F)
    where
        F: FnMut(&[u8]) -> HashSha3256 + 'static, {
        *self.hash_sha3_256_mock.borrow_mut() = Some(Box::new(mock));
    }

    #[cfg(not(feature = "crypto-primitives"))]
    /// Set up a mock for
    /// [`hash_keccak_256`](HasCryptoPrimitives::hash_keccak_256).
    ///
    /// This is not available if the "crypto-primitives" feature is enabled. For
    /// more information on why, see the documentation of
    /// [`TestCryptoPrimitives`].
    pub fn setup_hash_keccak_256_mock<F>(&self, mock: F)
    where
        F: FnMut(&[u8]) -> HashKeccak256 + 'static, {
        *self.hash_keccak_256_mock.borrow_mut() = Some(Box::new(mock));
    }

    /// Fail with an error message that tells you to set up mocks
    /// OR enable the crypto-primitives feature.
    #[cfg(not(feature = "crypto-primitives"))]
    fn fail_with_crypto_primitives_error(method_name: &str) -> ! {
        fail!(
            "To use {}, you need to either enable the \"concordium-std/crypto-primitives\" \
             feature, which makes it use an actual implemenation, or set up a mock with the \
             setup_{}_mock method on TestCryptoPrimitives.",
            method_name,
            method_name
        )
    }
}

impl HasCryptoPrimitives for TestCryptoPrimitives {
    fn verify_ed25519_signature(
        &self,
        public_key: PublicKeyEd25519,
        signature: SignatureEd25519,
        message: &[u8],
    ) -> bool {
        #[cfg(feature = "crypto-primitives")]
        {
            let signature = ed25519_zebra::Signature::try_from(&signature.0[..]);
            let public_key = ed25519_zebra::VerificationKey::try_from(&public_key.0[..]);
            match (signature, public_key) {
                (Ok(ref signature), Ok(public_key)) => {
                    public_key.verify(signature, message).is_ok()
                }
                _ => false,
            }
        }
        #[cfg(not(feature = "crypto-primitives"))]
        {
            if let Some(ref mut mock) = *self.verify_ed25519_signature_mock.borrow_mut() {
                mock(public_key, signature, message)
            } else {
                Self::fail_with_crypto_primitives_error("verify_ed25519_signature")
            }
        }
    }

    fn verify_ecdsa_secp256k1_signature(
        &self,
        public_key: PublicKeyEcdsaSecp256k1,
        signature: SignatureEcdsaSecp256k1,
        message_hash: [u8; 32],
    ) -> bool {
        #[cfg(feature = "crypto-primitives")]
        {
            let signature = secp256k1::ecdsa::Signature::from_compact(&signature.0[..]);
            let public_key = secp256k1::PublicKey::from_slice(&public_key.0[..]);
            let message_hash = secp256k1::Message::from_slice(&message_hash[..]);
            match (signature, public_key, message_hash) {
                (Ok(ref signature), Ok(public_key), Ok(message_hash)) => {
                    let verifier = secp256k1::Secp256k1::verification_only();
                    verifier.verify_ecdsa(&message_hash, signature, &public_key).is_ok()
                }
                _ => false,
            }
        }
        #[cfg(not(feature = "crypto-primitives"))]
        {
            if let Some(ref mut mock) = *self.verify_ecdsa_secp256k1_signature_mock.borrow_mut() {
                mock(public_key, signature, message_hash)
            } else {
                Self::fail_with_crypto_primitives_error("verify_ecdsa_secp256k1")
            }
        }
    }

    fn hash_sha2_256(&self, data: &[u8]) -> HashSha2256 {
        #[cfg(feature = "crypto-primitives")]
        {
            use sha2::Digest;
            HashSha2256(sha2::Sha256::digest(data).into())
        }
        #[cfg(not(feature = "crypto-primitives"))]
        {
            if let Some(ref mut mock) = *self.hash_sha2_256_mock.borrow_mut() {
                mock(data)
            } else {
                Self::fail_with_crypto_primitives_error("hash_sha2_256")
            }
        }
    }

    fn hash_sha3_256(&self, data: &[u8]) -> HashSha3256 {
        #[cfg(feature = "crypto-primitives")]
        {
            use sha3::Digest;
            HashSha3256(sha3::Sha3_256::digest(data).into())
        }
        #[cfg(not(feature = "crypto-primitives"))]
        {
            if let Some(ref mut mock) = *self.hash_sha3_256_mock.borrow_mut() {
                mock(data)
            } else {
                Self::fail_with_crypto_primitives_error("hash_sha3_256")
            }
        }
    }

    fn hash_keccak_256(&self, data: &[u8]) -> HashKeccak256 {
        #[cfg(feature = "crypto-primitives")]
        {
            use sha3::Digest;
            HashKeccak256(sha3::Keccak256::digest(data).into())
        }
        #[cfg(not(feature = "crypto-primitives"))]
        {
            if let Some(ref mut mock) = *self.hash_keccak_256_mock.borrow_mut() {
                mock(data)
            } else {
                Self::fail_with_crypto_primitives_error("hash_keccak_256")
            }
        }
    }
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

    #[inline(always)]
    fn cursor_position(&self) -> u32 { self.cursor.offset as u32 }
}

impl HasCallResponse for Cursor<Vec<u8>> {
    fn size(&self) -> u32 { self.data.len() as u32 }
}

#[cfg(all(feature = "wasm-test", feature = "concordium-quickcheck", target_arch = "wasm32"))]
use getrandom::register_custom_getrandom;
#[cfg(all(feature = "wasm-test", feature = "concordium-quickcheck", target_arch = "wasm32"))]
/// A custom function for generating random numbers.
/// There is no Wasm primitive to sample random numbers and this function
/// redirects calls to the `get_random` primitive (host function), which is
/// later handled by `TestHost`, where the actual random number generation
/// happens.
fn get_random(dest: &mut [u8]) -> Result<(), getrandom::Error> {
    unsafe {
        crate::prims::get_random(dest.as_mut_ptr(), dest.len() as u32);
    }
    Ok(())
}

#[cfg(all(feature = "wasm-test", feature = "concordium-quickcheck", target_arch = "wasm32"))]
// When compiling to Wasm, we register our own custom random number generation
// function, so all the calls, that depend on `getrandom` (like
// `from_entropy`) will call our function instead.
register_custom_getrandom!(get_random);

// Overall number of QuickCheck tests to run.
// Includes both *passed and discarded*.
// Note: when changing this constant, make sure that
// concordium_std_derive::QUICKCHECK_MAX_PASSED_TESTS is adjusted:
// - QUICKCHECK_MAX_PASSED_TESTS is capped by
//   QUICKCHECK_MAX_WITH_DISCARDED_TESTS;
// - QUICKCHECK_MAX_WITH_DISCARDED_TESTS should be bigger allowing some test to
//   be discarded (QuickCheck default is x100).
#[cfg(feature = "concordium-quickcheck")]
const QUICKCHECK_MAX_WITH_DISCARDED_TESTS: u64 = 100_000_000;

#[cfg(all(feature = "concordium-quickcheck", target_arch = "wasm32"))]
/// A customized QuickCheck test runner used for on-chain wasm code.
/// Adds support for reporting errors using the primitives available when
/// running Wasm code.
///
/// The `num_tests` parameter specifies how many random tests to run.
pub fn concordium_qc<A: Testable>(num_tests: u64, f: A) {
    let mut qc = QuickCheck::new().tests(num_tests).max_tests(QUICKCHECK_MAX_WITH_DISCARDED_TESTS);
    let res = qc.quicktest(f);
    match res {
        Ok(n_tests_passed) => {
            if n_tests_passed == 0 {
                // report a error is no tests were generated
                let msg = "(No QuickCheck tests were generated)";
                // calls `report_error` which is handled by `TestHost`
                report_error(msg, file!(), line!(), column!())
            }
        }
        Err(result) => {
            let msg = format!("Failed with the counterexample: {:#?}", result);
            // calls `report_error` which is handled by `TestHost`
            report_error(&msg, file!(), line!(), column!());
        }
    }
}

#[cfg(all(feature = "concordium-quickcheck", not(target_arch = "wasm32")))]
/// A wrapper for QuickCheck test runner for non-wasm targets.
// The `num_tests` parameter specifies how many random tests to run.
pub fn concordium_qc<A: Testable>(num_tests: u64, f: A) {
    QuickCheck::new().tests(num_tests).max_tests(QUICKCHECK_MAX_WITH_DISCARDED_TESTS).quickcheck(f)
}

#[cfg(test)]
#[allow(deprecated)]
mod test {
    use crate::{cell::RefCell, rc::Rc, test_infrastructure::TestStateEntry, HasStateEntry};
    use concordium_contracts_common::{Read, Seek, SeekFrom, Write};

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
}
