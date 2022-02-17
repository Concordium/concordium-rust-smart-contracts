use crate::{num::NonZeroU32, HasContractStateEntry, HasContractStateLL};
use std::{cell::RefCell, marker::PhantomData, rc::Rc};

#[derive(Debug)]
pub struct StateMap<K, V, S>
where
    S: HasContractStateLL, {
    pub(crate) _marker_key:   PhantomData<K>,
    pub(crate) _marker_value: PhantomData<V>,
    pub(crate) prefix:        StateMapPrefix,
    pub(crate) state_ll:      Rc<RefCell<S>>,
}

#[derive(Debug)]
pub struct StateMapIter<K, V, S: HasContractStateLL> {
    pub(crate) state_iter:    S::IterType,
    pub(crate) state_ll:      Rc<RefCell<S>>,
    pub(crate) _marker_key:   PhantomData<K>,
    pub(crate) _marker_value: PhantomData<V>,
}

#[derive(Debug)]
pub struct StateSet<T, S>
where
    S: HasContractStateLL, {
    pub(crate) _marker:  PhantomData<T>,
    pub(crate) prefix:   StateMapPrefix,
    pub(crate) state_ll: Rc<RefCell<S>>,
}

#[derive(Debug)]
pub struct StateSetIter<T, S: HasContractStateLL> {
    pub(crate) state_iter: S::IterType,
    pub(crate) state_ll:   Rc<RefCell<S>>,
    pub(crate) _marker:    PhantomData<T>,
}

#[derive(Debug)]
pub enum Persisted<T, S> {
    New(T),
    Loaded {
        value:    Option<T>, // Only used for get()
        prefix:   Vec<u8>,
        state_ll: Rc<RefCell<S>>,
    },
}

#[derive(Debug, Default)]
pub struct ContractStateLL;

pub struct ContractStateIter {
    pub(crate) iterator_id: StateIteratorId,
}

pub type StateEntryId = u32;
pub type StateIteratorId = u32;
pub type StateMapPrefix = Vec<u8>;

#[derive(Default)]
pub struct StateEntry {
    pub(crate) state_entry_id:   StateEntryId,
    pub(crate) current_position: u32,
}

pub struct VacantEntryRaw<StateEntryType>
where
    StateEntryType: HasContractStateEntry, {
    pub(crate) state_entry: StateEntryType,
}

pub struct OccupiedEntryRaw<StateEntryType>
where
    StateEntryType: HasContractStateEntry, {
    pub(crate) state_entry: StateEntryType,
}

pub enum EntryRaw<StateEntryType>
where
    StateEntryType: HasContractStateEntry, {
    Vacant(VacantEntryRaw<StateEntryType>),
    Occupied(OccupiedEntryRaw<StateEntryType>),
}

pub struct VacantEntry<K, V, StateEntryType> {
    pub(crate) key:           K,
    pub(crate) state_entry:   StateEntryType,
    pub(crate) _marker_value: PhantomData<V>,
}

pub struct OccupiedEntry<K, V, StateEntryType> {
    pub(crate) key:         K,
    pub(crate) value:       V,
    pub(crate) state_entry: StateEntryType,
}

pub enum Entry<K, V, S> {
    Vacant(VacantEntry<K, V, S>),
    Occupied(OccupiedEntry<K, V, S>),
}

#[derive(Default)]
/// A type representing the parameter to init and receive methods.
/// Its trait implementations are backed by host functions.
pub struct ExternParameter {
    pub(crate) current_position: u32,
}

/// A type representing the return value of contract calls.
/// This is when a contract calls another contract, it may get a return value.
#[derive(Debug, Clone, Copy)]
pub struct CallResponse {
    /// The index of the call response.
    pub(crate) i:                NonZeroU32,
    pub(crate) current_position: u32,
}

impl CallResponse {
    #[inline(always)]
    /// Construct a new call response with the given index,
    /// and starting position set to 0.
    pub(crate) fn new(i: NonZeroU32) -> Self {
        Self {
            i,
            current_position: 0,
        }
    }
}

/// A type representing the return value of contract init or receive method.
pub struct ReturnValue {
    pub(crate) current_position: u32,
}

#[repr(i32)]
#[derive(Debug, Clone, Copy)]
/// Errors that may occur when invoking a contract entrypoint.
pub enum CallContractError<ReturnValueType> {
    /// Amount that was to be transferred is not available to the sender.
    AmountTooLarge,
    /// Owner account of the smart contract that is being invoked does not
    /// exist. This variant should in principle not happen, but is here for
    /// completeness.
    MissingAccount,
    /// Contract that is to be invoked does not exist.
    MissingContract,
    /// The contract to be invoked exists, but the entrypoint that was named
    /// does not.
    MissingEntrypoint,
    /// Sending a message to the V0 contract failed.
    MessageFailed,
    /// Contract that was called rejected with the given reason.
    LogicReject {
        reason:       i32,
        return_value: ReturnValueType,
    },
    /// Execution of a contract call triggered a runtime error.
    Trap,
}

#[repr(i32)]
#[derive(Debug, Clone)]
/// Errors that may occur when transferring CCD to an account.
pub enum TransferError {
    /// Amount that was to be transferred is not available to the sender.
    AmountTooLarge,
    /// Account that is to be transferred to does not exist.
    MissingAccount,
}

/// A wrapper around [Result] that fixes the error variant to
/// [CallContractError].
pub type CallContractResult<A> = Result<(bool, Option<A>), CallContractError<A>>;

/// A wrapper around [Result] that fixes the error variant to [TransferError]
/// and result to [()](https://doc.rust-lang.org/std/primitive.unit.html).
pub type TransferResult = Result<(), TransferError>;

/// A type representing the attributes, lazily acquired from the host.
#[derive(Default)]
pub struct AttributesCursor {
    /// Current position of the cursor, starting from 0.
    /// Note that this is only for the variable attributes.
    /// `created_at` and `valid_to` will require.
    pub(crate) current_position: u32,
    /// The number of remaining items in the policy.
    pub(crate) remaining_items:  u16,
}

/// A type representing the logger.
#[derive(Default)]
pub struct Logger {
    pub(crate) _private: (),
}

/// Errors that can occur during logging.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[repr(u8)]
pub enum LogError {
    /// The log is full.
    Full,
    /// The message to log was malformed (e.g., too long)
    Malformed,
}

/// Error triggered when a non-zero amount of CCD is sent to a contract
/// init or receive function that is not marked as `payable`.
#[derive(Clone, Copy, Debug)]
pub struct NotPayableError;

/// An error message, signalling rejection of a smart contract invocation.
/// The client will see the error code as a reject reason; if a schema is
/// provided, the error message corresponding to the error code will be
/// displayed. The valid range for an error code is from i32::MIN to -1.
/// A return value can also be provided.
#[derive(Eq, PartialEq, Debug)]
pub struct Reject {
    pub error_code:   crate::num::NonZeroI32,
    pub return_value: Option<Vec<u8>>,
}

impl From<crate::num::NonZeroI32> for Reject {
    #[inline(always)]
    fn from(error_code: crate::num::NonZeroI32) -> Self {
        Self {
            error_code,
            return_value: None,
        }
    }
}

/// Default error is i32::MIN.
impl Default for Reject {
    #[inline(always)]
    fn default() -> Self {
        Self {
            error_code:   unsafe { crate::num::NonZeroI32::new_unchecked(i32::MIN) },
            return_value: None,
        }
    }
}

impl Reject {
    /// This returns `None` for all values >= 0 and `Some` otherwise.
    pub fn new(x: i32) -> Option<Self> {
        if x < 0 {
            let error_code = unsafe { crate::num::NonZeroI32::new_unchecked(x) };
            Some(Reject {
                error_code,
                return_value: None,
            })
        } else {
            None
        }
    }
}

// Macros for failing a contract function

/// The `bail` macro can be used for cleaner error handling. If the function has
/// result type `Result` invoking `bail` will terminate execution early with an
/// error.
/// If an argument is supplied, this will be used as the error, otherwise it
/// requires the type `E` in `Result<_, E>` to implement the `Default` trait.
#[macro_export]
macro_rules! bail {
    () => {{
        return Err(Default::default());
    }};
    ($arg:expr) => {{
        // format_err!-like formatting
        // logs are only retained in case of rejection when testing.
        return Err($arg);
    }};
}

/// The `ensure` macro can be used for cleaner error handling. It is analogous
/// to `assert`, but instead of panicking it uses `bail` to terminate execution
/// of the function early.
#[macro_export]
macro_rules! ensure {
    ($p:expr) => {
        if !$p {
            $crate::bail!();
        }
    };
    ($p:expr, $arg:expr) => {{
        if !$p {
            $crate::bail!($arg);
        }
    }};
}

/// ## Variants of `ensure` for ease of use in certain contexts.
/// Ensure the first two arguments are equal, using `bail` otherwise.
#[macro_export]
macro_rules! ensure_eq {
    ($l:expr, $r:expr) => {
        $crate::ensure!($l == $r)
    };
    ($l:expr, $r:expr, $arg:expr) => {
        $crate::ensure!($l == $r, $arg)
    };
}

#[macro_export]
/// Ensure the first two arguments are __not__ equal, using `bail` otherwise.
macro_rules! ensure_ne {
    ($l:expr, $r:expr) => {
        $crate::ensure!($l != $r)
    };
    ($l:expr, $r:expr, $arg:expr) => {
        $crate::ensure!($l != $r, $arg)
    };
}

// Macros for failing a test

/// The `fail` macro is used for testing as a substitute for the panic macro.
/// It reports back error information to the host.
/// Used only in testing.
#[cfg(feature = "std")]
#[macro_export]
macro_rules! fail {
    () => {
        {
            $crate::test_infrastructure::report_error("", file!(), line!(), column!());
            panic!()
        }
    };
    ($($arg:tt),+) => {
        {
            let msg = format!($($arg),+);
            $crate::test_infrastructure::report_error(&msg, file!(), line!(), column!());
            panic!("{}", msg)
        }
    };
}

/// The `fail` macro is used for testing as a substitute for the panic macro.
/// It reports back error information to the host.
/// Used only in testing.
#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! fail {
    () => {
        {
            $crate::test_infrastructure::report_error("", file!(), line!(), column!());
            panic!()
        }
    };
    ($($arg:tt),+) => {
        {
            let msg = &$crate::alloc::format!($($arg),+);
            $crate::test_infrastructure::report_error(&msg, file!(), line!(), column!());
            panic!("{}", msg)
        }
    };
}

/// The `claim` macro is used for testing as a substitute for the assert macro.
/// It checks the condition and if false it reports back an error.
/// Used only in testing.
#[macro_export]
macro_rules! claim {
    ($cond:expr) => {
        if !$cond {
            $crate::fail!()
        }
    };
    ($cond:expr,) => {
        if !$cond {
            $crate::fail!()
        }
    };
    ($cond:expr, $($arg:tt),+) => {
        if !$cond {
            $crate::fail!($($arg),+)
        }
    };
}

/// Ensure the first two arguments are equal, just like `assert_eq!`, otherwise
/// reports an error. Used only in testing.
#[macro_export]
macro_rules! claim_eq {
    ($left:expr, $right:expr $(,)?) => {
        // Use match to ensure that the values are only evaluated once,
        // and to ensure that type inference works correctly when printing.
        match (&$left, &$right) {
            (left_val, right_val) => {
                if !(*left_val == *right_val) {
                    $crate::fail!("left and right are not equal\nleft: {:?}\nright: {:?}\n", left_val, right_val);
                }
            }
        }
    };
    ($left:expr, $right:expr, $($arg:tt),+) => {
        $crate::claim!($left == $right, $($arg),+)
    };
}

/// Ensure the first two arguments are *not* equal, just like `assert_ne!`,
/// otherwise reports an error.
/// Used only in testing.
#[macro_export]
macro_rules! claim_ne {
    ($left:expr, $right:expr $(,)?) => {
        // Use match to ensure that the values are only evaluated once,
        // and to ensure that type inference works correctly when printing.
        match (&$left, &$right) {
            (left_val, right_val) => {
                if *left_val == *right_val {
                    $crate::fail!("left and right are equal\nleft: {:?}\nright: {:?}\n", left_val, right_val);
                }
            }
        }
    };
    ($left:expr, $right:expr, $($arg:tt),+) => {
        $crate::claim!($left != $right, $($arg),+)
    };
}

/// The expected return type of the receive method of a smart contract.
///
/// Optionally, to define a custom type for error instead of using
/// Reject, allowing to track the reason for rejection, *but only in unit
/// tests*.
///
/// See also the documentation for [bail!](macro.bail.html) for how to use
/// custom error types.
///
/// # Example
/// Defining a custom error type
/// ```rust
/// enum MyCustomError {
///     SomeError
/// }
///
/// #[receive(contract = "mycontract", name = "receive")]
/// fn contract_receive<R: HasReceiveContext, L: HasLogger, A: HasActions>(
///     ctx: &R,
///     receive_amount: Amount,
///     logger: &mut L,
///     state: &mut State,
/// ) -> Result<A, MyCustomError> { ... }
/// ```
pub type ReceiveResult<A> = Result<A, Reject>;

/// The expected return type of the init method of the smart contract,
/// parametrized by the state type of the smart contract.
///
/// Optionally, to define a custom type for error instead of using Reject,
/// allowing the track the reason for rejection, *but only in unit tests*.
///
/// See also the documentation for [bail!](macro.bail.html) for how to use
/// custom error types.
///
/// # Example
/// Defining a custom error type
/// ```rust
/// enum MyCustomError {
///     SomeError
/// }
///
/// #[init(contract = "mycontract")]
/// fn contract_init<R: HasReceiveContext, L: HasLogger, A: HasActions>(
///     ctx: &R,
///     receive_amount: Amount,
///     logger: &mut L,
/// ) -> Result<State, MyCustomError> { ... }
/// ```
pub type InitResult<S> = Result<S, Reject>;

/// Operations backed by host functions for the high-level interface.
#[doc(hidden)]
pub struct ExternHost<State> {
    pub state:     State,
    pub allocator: Allocator<ContractStateLL>,
}

#[derive(Default)]
pub struct Allocator<StateLL> {
    pub(crate) state_ll: Rc<RefCell<StateLL>>,
}

/// Operations backed by host functions for the low-level interface.
#[doc(hidden)]
#[derive(Default)]
pub struct ExternLowLevelHost {
    pub(crate) state:     ContractStateLL,
    pub(crate) allocator: Allocator<ContractStateLL>,
}

/// Context backed by host functions.
#[derive(Default)]
#[doc(hidden)]
pub struct ExternContext<T: sealed::ContextType> {
    marker: crate::marker::PhantomData<T>,
}

#[doc(hidden)]
pub struct ChainMetaExtern {}

#[derive(Default)]
#[doc(hidden)]
pub struct InitContextExtern;
#[derive(Default)]
#[doc(hidden)]
pub struct ReceiveContextExtern;

pub(crate) mod sealed {
    use super::*;
    /// Marker trait intended to indicate which context type we have.
    /// This is deliberately a sealed trait, so that it is only implementable
    /// by types in this crate.
    pub trait ContextType {}
    impl ContextType for InitContextExtern {}
    impl ContextType for ReceiveContextExtern {}
}
