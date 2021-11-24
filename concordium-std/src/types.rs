use concordium_contracts_common::{Serial, Serialize};
use std::{cell::RefCell, marker::PhantomData, rc::Rc};

use crate::{HasContractStateEntry, HasContractStateLL};

/// A type representing the constract state bytes.
#[derive(Default)]
pub struct ContractState {
    pub(crate) current_position: u32,
}

pub struct ContractStateHL {
    pub(crate) state_ll: Rc<RefCell<ContractStateLL>>,
}

// TODO: Remove serialize constraints?
pub struct StateMap<S, K, V>
where
    K: Serialize,
    V: Serial,
    S: HasContractStateLL, {
    pub(crate) phantom_k: PhantomData<K>,
    pub(crate) phantom_v: PhantomData<V>,
    pub(crate) prefix:    StateMapPrefix,
    pub(crate) state_ll:  Rc<RefCell<S>>,
}

pub struct StateSet<V>
where
    V: Serialize, {
    // S: HasNewContractState, {
    pub(crate) phantom_v: PhantomData<V>,
    // pub(crate) contract_state: S,
}

pub struct ContractStateLL;

pub struct ContractStateIter {
    pub(crate) iterator_id: StateIteratorId,
}

pub type StateEntryId = u32;
pub type StateIteratorId = u32;
pub type StateMapPrefix = Vec<u8>;

pub struct StateEntry {
    pub(crate) entry_id:         StateEntryId,
    pub(crate) current_position: u32,
}

pub struct VacantEntry<EntryType: HasContractStateEntry> {
    pub(crate) entry_id: StateEntryId,
    pub(crate) _marker:  PhantomData<EntryType>,
}

pub struct OccupiedEntry<EntryType: HasContractStateEntry> {
    pub(crate) entry_id: StateEntryId,
    pub(crate) entry:    EntryType,
}

pub enum Entry<EntryType: HasContractStateEntry> {
    Vacant(VacantEntry<EntryType>),
    Occupied(OccupiedEntry<EntryType>),
}

#[derive(Default)]
/// A type representing the parameter to init and receive methods.
pub struct Parameter {
    pub(crate) current_position: u32,
}

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

/// Error triggered when a non-zero amount of GTU is sent to a contract
/// init or receive function that is not marked as `payable`.
#[derive(Clone, Copy, Debug)]
pub struct NotPayableError;

/// Actions that can be produced at the end of a contract execution. This
/// type is deliberately not cloneable so that we can enforce that
/// `and_then` and `or_else` can only be used when more than one event is
/// created.
///
/// This type is marked as `must_use` since functions that produce
/// values of the type are effectful.
#[must_use]
pub struct Action {
    pub(crate) _private: u32,
}

impl Action {
    pub fn tag(&self) -> u32 { self._private }
}

/// An error message, signalling rejection of a smart contract invocation.
/// The client will see the error code as a reject reason; if a schema is
/// provided, the error message corresponding to the error code will be
/// displayed. The valid range for an error code is from i32::MIN to  -1.
#[derive(Eq, PartialEq, Debug)]
#[repr(transparent)]
pub struct Reject {
    pub error_code: crate::num::NonZeroI32,
}

/// Default error is i32::MIN.
impl Default for Reject {
    #[inline(always)]
    fn default() -> Self {
        Self {
            error_code: unsafe { crate::num::NonZeroI32::new_unchecked(i32::MIN) },
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
    ($left:expr, $right:expr) => {
        $crate::claim!($left == $right, "left and right are not equal\nleft: {:?}\nright: {:?}", $left, $right)
    };
    ($left:expr, $right:expr,) => {
        $crate::claim_eq!($left, $right)
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
    ($left:expr, $right:expr) => {
        $crate::claim!($left != $right)
    };
    ($left:expr, $right:expr,) => {
        $crate::claim!($left != $right)
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
