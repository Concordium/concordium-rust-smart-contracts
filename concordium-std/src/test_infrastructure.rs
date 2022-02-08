//! The test infrastructure module provides alternative implementations of
//! `HasInitContext`, `HasReceiveContext`, `HasParameter`, and
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
use std::collections::HashMap;
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

impl HasCallResponse for Cursor<Vec<u8>> {
    fn size(&self) -> u32 { self.data.len() as u32 }
}

pub struct MockFn<State> {
    /// A mock function. The return value indicates whether the state was
    /// modified or not.
    mock_fn: Box<dyn Fn(Parameter, Amount, &mut State, &mut Vec<u8>) -> InvokeResult<bool>>,
}

impl<State> MockFn<State> {
    /// Create a mock function which has access to the parameter, amount, and
    /// state.
    pub fn new<R, F>(mock_fn_return: F) -> Self
    where
        R: Serial,
        F: Fn(Parameter, Amount, &mut State) -> InvokeResult<(bool, R)> + 'static, {
        // Put it on the heap, so it will live long enough.
        let boxed_mock_fn_return = Box::new(mock_fn_return);

        // TODO: Ideally, the Host should figure out whether the state has been altered
        // or not. I.e. the bool should not be returned in the `mock_fn_return` closure.
        let mock_fn = Box::new(
            move |parameter: Parameter, amount: Amount, state: &mut State, output: &mut Vec<u8>| {
                let (modified, return_value) = boxed_mock_fn_return(parameter, amount, state)?;
                return_value.serial(output).map_err(|_| InvokeError::Trap)?;
                Ok(modified)
            },
        );

        Self {
            mock_fn,
        }
    }

    /// Create a simple mock function that returns `Ok` with the same
    /// value every time.
    pub fn returning_ok<R>(return_value: R) -> Self
    where
        R: Serial + 'static + Clone, {
        Self::new(move |_parameter, _amount, _state| -> InvokeResult<(bool, R)> {
            Ok((false, return_value.clone()))
        })
    }

    /// Create a simple mock function that returns `Err` with same error every
    /// time.
    pub fn returning_err(error: InvokeError) -> Self {
        let mock_fn = Box::new(
            move |_parameter: Parameter,
                  _amount: Amount,
                  _state: &mut State,
                  _output: &mut Vec<u8>| { Err(error.clone()) },
        );
        Self {
            mock_fn,
        }
    }
}

pub struct HostTest<State> {
    mocking_fns:      HashMap<(ContractAddress, OwnedEntrypointName), MockFn<State>>,
    transfers:        Vec<(AccountAddress, Amount)>,
    contract_balance: Option<Amount>,
    state:            State,
    missing_accounts: Vec<AccountAddress>,
}

impl<State> HasHost<State> for HostTest<State> {
    type CallResponseType = Cursor<Vec<u8>>;

    /// Perform a transfer to the given account if the contract has sufficient
    /// balance. Use `make_account_missing` to test out transfers to
    /// accounts not on chain.
    ///
    /// Possible errors:
    ///   - `InvokeError::AmountTooLarge`: Contract has insufficient funds.
    ///   - `InvokeError::MissingAccount`: Attempted transfer to an account set
    ///     a missing with `make_account_missing`.
    fn invoke_transfer(&mut self, receiver: &AccountAddress, amount: Amount) -> InvokeResult<()> {
        if self.missing_accounts.contains(receiver) {
            return Err(InvokeError::MissingAccount);
        }
        let contract_balance = unwrap_contract_balance(&mut self.contract_balance);
        if *contract_balance >= amount {
            *contract_balance -= amount;
            self.transfers.push((receiver.clone(), amount));
            Ok(())
        } else {
            Err(InvokeError::AmountTooLarge)
        }
    }

    /// Invoke a contract.
    fn invoke_contract(
        &mut self,
        to: &ContractAddress,
        parameter: Parameter,
        method: EntrypointName,
        amount: Amount,
    ) -> InvokeResult<(bool, Option<Self::CallResponseType>)> {
        let handler = match self.mocking_fns.get(&(*to, OwnedEntrypointName::from(method))) {
            Some(handler) => handler,
            None => fail!(
                "Mocking has not been set up for invoking contract {:?} with method '{}'.",
                to,
                method
            ),
        };
        // Check if the contract has sufficient balance.
        // Do not try to unwrap the balance if amount is zero.
        if amount.micro_ccd > 0 && *unwrap_contract_balance(&mut self.contract_balance) < amount {
            return Err(InvokeError::AmountTooLarge);
        }
        let mut output = Vec::new();
        let res = (handler.mock_fn)(parameter, amount, &mut self.state, &mut output)
            .and_then(|state_modified| Ok((state_modified, Some(Cursor::new(output)))));
        if res.is_ok() && amount.micro_ccd > 0 {
            *unwrap_contract_balance(&mut self.contract_balance) -= amount;
        }
        res
    }

    fn state(&mut self) -> &mut State { &mut self.state }

    fn self_balance(&self) -> Amount {
        match self.contract_balance {
            Some(amount) => amount,
            None => fail!(
                "Unset contract balance on the test host. Make sure to use `set_balance` if your \
                 contract uses the balance."
            ),
        }
    }
}

/// Helper function for unwrapping the contract balance.
/// Fails with a descriptive error message on `None`.
fn unwrap_contract_balance(balance: &mut Option<Amount>) -> &mut Amount {
    match balance {
        Some(ref mut amount) => amount,
        None => fail!(
            "Unset contract balance on the test host. Make sure to use `set_balance` if your \
             contract uses the balance."
        ),
    }
}

impl<State> HostTest<State> {
    pub fn new(state: State) -> Self {
        Self {
            mocking_fns: HashMap::new(),
            transfers: Vec::new(),
            contract_balance: None,
            state,
            missing_accounts: Vec::new(),
        }
    }

    pub fn setup_mock_invocation(
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
    ///                  // so calling host.self_balance will return `10` initially.
    ///                  // This differs from when you run a contract on the node,
    ///                  // where the amount automatically is added to the existing
    ///                  // balance of the contract.
    ///                  Amount::from_ccd(5)
    ///                  );
    /// ```
    pub fn set_balance(&mut self, amount: Amount) { self.contract_balance = Some(amount); }

    /// Check whether a given transfer occured.
    pub fn transfer_occurred(&self, receiver: &AccountAddress, amount: Amount) -> bool {
        self.transfers.contains(&(receiver.clone(), amount))
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
    /// in an `InvokeError::MissingAccount` error.
    pub fn make_account_missing(&mut self, account: AccountAddress) {
        self.missing_accounts.push(account);
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
