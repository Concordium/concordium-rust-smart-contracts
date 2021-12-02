//! The test infrastructure module provides alternative implementations of
//! `HasInitContext`, `HasReceiveContext`, `HasParameter`, `HasActions`, and
//! `HasContractState` traits intended for testing.
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
//! fn contract_init<I: HasInitContext, L: HasLogger>(
//!     ctx: &I,
//! ) -> InitResult<State> { ... }
//!
//! #[receive(contract = "noop", name = "receive", payable, enable_logger)]
//! fn contract_receive<R: HasReceiveContext, L: HasLogger, A: HasActions>(
//!     ctx: &R,
//!     amount: Amount,
//!     logger: &mut L,
//!     state: &mut State,
//! ) -> ReceiveResult<A> { ... }
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
//!         ctx.set_owner(AccountAddress([0u8; 32]));
//!         ...
//!         let mut logger = LogRecorder::init();
//!         let result: ReceiveResult<ActionsTree> = contract_receive(&ctx, 0, &mut logger, state);
//!         claim!(...)
//!         ...
//!     }
//! }
//! ```
use crate::{constants::MAX_CONTRACT_STATE_SIZE, *};

#[cfg(not(feature = "std"))]
use alloc::boxed::Box;
use convert::TryInto;
#[cfg(not(feature = "std"))]
use core::{cmp, num};
use std::{
    borrow::BorrowMut,
    cell::{RefCell, RefMut},
    rc::Rc,
};
#[cfg(feature = "std")]
use std::{boxed::Box, cmp, num};

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
    pub(crate) self_balance: Option<Amount>,
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

    pub fn set_self_balance(&mut self, value: Amount) -> &mut Self {
        self.custom.self_balance = Some(value);
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
            "Unset field on test context '{}', make sure to set all the field necessary for the \
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

    fn self_balance(&self) -> Amount { unwrap_ctx_field(self.custom.self_balance, "self_balance") }

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

impl HasActions for ActionsTree {
    fn accept() -> Self { ActionsTree::Accept }

    fn simple_transfer(acc: &AccountAddress, amount: Amount) -> Self {
        ActionsTree::SimpleTransfer {
            to: *acc,
            amount,
        }
    }

    fn send_raw(
        ca: &ContractAddress,
        receive_name: ReceiveName,
        amount: Amount,
        parameter: &[u8],
    ) -> Self {
        ActionsTree::Send {
            to: *ca,
            receive_name: receive_name.to_owned(),
            amount,
            parameter: parameter.to_vec(),
        }
    }

    fn and_then(self, then: Self) -> Self {
        ActionsTree::AndThen {
            left:  Box::new(self),
            right: Box::new(then),
        }
    }

    fn or_else(self, el: Self) -> Self {
        ActionsTree::OrElse {
            left:  Box::new(self),
            right: Box::new(el),
        }
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

/// Contract state for testing, mimicking the operations the scheduler allows,
/// including the limit on the size of the maximum size of the contract state.
pub struct ContractStateTest<T> {
    pub cursor: Cursor<T>,
}

/// A borrowed instantiation of `ContractStateTest`.
pub type ContractStateTestBorrowed<'a> = ContractStateTest<&'a mut Vec<u8>>;

/// An owned variant that can be more convenient for testing since the type
/// itself owns the data.
pub type ContractStateTestOwned = ContractStateTest<Vec<u8>>;

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

impl<T: convert::AsRef<[u8]>> Read for ContractStateTest<T> {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> { self.cursor.read(buf) }
}

impl<T: convert::AsMut<Vec<u8>>> Write for ContractStateTest<T> {
    type Err = ContractStateError;

    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Err> {
        // The chain automatically resizes the state up until MAX_CONTRACT_STATE_SIZE.
        let end = cmp::min(MAX_CONTRACT_STATE_SIZE as usize, self.cursor.offset + buf.len());
        if self.cursor.data.as_mut().len() < end {
            self.cursor.data.as_mut().resize(end as usize, 0u8);
        }
        let data = &mut self.cursor.data.as_mut()[self.cursor.offset..];
        let to_write = cmp::min(data.len(), buf.len());
        data[..to_write].copy_from_slice(&buf[..to_write]);
        self.cursor.offset += to_write;
        Ok(to_write)
    }
}

impl<T: AsMut<Vec<u8>> + AsMut<[u8]> + AsRef<[u8]>> HasContractState<ContractStateError>
    for ContractStateTest<T>
{
    type ContractStateData = T;

    fn open(data: Self::ContractStateData) -> Self {
        Self {
            cursor: Cursor::new(data),
        }
    }

    fn size(&self) -> u32 { self.cursor.data.as_ref().len() as u32 }

    fn truncate(&mut self, new_size: u32) {
        if self.size() > new_size {
            let new_size = new_size as usize;
            let data: &mut Vec<u8> = self.cursor.data.as_mut();
            data.truncate(new_size);
            if self.cursor.offset > new_size {
                self.cursor.offset = new_size
            }
        }
    }

    fn reserve(&mut self, len: u32) -> bool {
        if len <= constants::MAX_CONTRACT_STATE_SIZE {
            if self.size() < len {
                let data: &mut Vec<u8> = self.cursor.data.as_mut();
                data.resize(len as usize, 0u8);
            }
            true
        } else {
            false
        }
    }
}

impl Default for ContractStateError {
    fn default() -> Self { Self::Default }
}

impl From<num::TryFromIntError> for ContractStateError {
    fn from(_: num::TryFromIntError) -> Self { ContractStateError::Overflow }
}

impl<T: AsRef<[u8]>> Seek for ContractStateTest<T> {
    type Err = ContractStateError;

    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Err> {
        use ContractStateError::*;
        match pos {
            SeekFrom::Start(x) => {
                // We can set the position to just after the end of the current length.
                let new_offset = x.try_into()?;
                if new_offset <= self.cursor.data.as_ref().len() {
                    self.cursor.offset = new_offset;
                    Ok(x)
                } else {
                    Err(Offset)
                }
            }
            SeekFrom::End(x) => {
                // cannot seek beyond end, nor before beginning
                if x <= 0 {
                    let end: u32 = self.cursor.data.as_ref().len().try_into()?;
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
                    if new_pos <= self.cursor.data.as_ref().len() {
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

struct StateTrie;

// TODO: Replace the Vec with a generic T.
struct StateEntryTest {
    pub(crate) cursor:         Cursor<Rc<RefCell<Vec<u8>>>>,
    pub(crate) state_entry_id: StateEntryId,
}

struct ContractStateLLTest {
    trie: StateTrie,
}

impl StateTrie {
    fn lookup(&self, key: &[u8]) -> Option<StateEntryTest> { todo!() }

    fn create(&mut self, key: &[u8]) -> StateEntryTest { todo!() }

    fn delete_entry(&mut self, entry_id: StateEntryId) -> bool { todo!() }

    fn delete_prefix(&mut self, prefix: &[u8], exact: bool) -> bool { todo!() }
}

impl HasContractStateLL for ContractStateLLTest {
    type ContractStateData = StateTrie;
    type EntryType = StateEntryTest;
    type IterType = ContractStateIter<StateEntryTest>;

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

    fn delete_entry(&mut self, entry_id: StateEntryId) -> bool { self.trie.delete_entry(entry_id) }

    fn delete_prefix(&mut self, prefix: &[u8], exact: bool) -> bool {
        self.trie.delete_prefix(prefix, exact)
    }

    fn iterator(&self, _prefix: &[u8]) -> Self::IterType { todo!() }
}

impl HasContractStateEntry for StateEntryTest {
    type Error = ContractStateError;
    type StateEntryData = Rc<RefCell<Vec<u8>>>;

    fn open(data: Self::StateEntryData, entry_id: StateEntryId) -> Self {
        Self {
            cursor:         Cursor::new(data),
            state_entry_id: entry_id,
        }
    }

    fn state_entry_id(&self) -> StateEntryId { self.state_entry_id }

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

#[cfg(test)]
mod test {
    use concordium_contracts_common::{Read, Seek, SeekFrom, Write};

    use super::ContractStateTest;
    use crate::{constants, traits::HasContractState};

    #[test]
    // Perform a number of operations from Seek, Read, Write and HasContractState
    // classes on the ContractStateTest structure and check that they behave as
    // specified.
    fn test_contract_state() {
        let data = vec![1; 100];
        let mut state = ContractStateTest::open(data);
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
        assert_eq!(&buf[0..20], &state.cursor.data[80..100], "Incorrect data was read.");
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
            state.cursor.data.len(),
            constants::MAX_CONTRACT_STATE_SIZE as usize,
            "State size should not increase beyond max."
        )
    }

    #[test]
    fn test_contract_state_write() {
        let data = vec![0u8; 10];
        let mut state = ContractStateTest::open(data);
        assert_eq!(state.write(&1u64.to_le_bytes()), Ok(8), "Incorrect number of bytes written.");
        assert_eq!(
            state.write(&2u64.to_le_bytes()),
            Ok(8),
            "State should be resized automatically."
        );
        assert_eq!(state.cursor.offset, 16, "Pos should be at the end.");
        assert_eq!(
            state.cursor.data,
            vec![1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
            "Correct data was written."
        );
    }
}
