use crate::{cell::RefCell, marker::PhantomData, num::NonZeroU32, HasStateApi, Vec};

#[derive(Debug)]
/// A map based on a [Trie](https://en.wikipedia.org/wiki/Trie) in the state.
///
/// In most situations, this type should be preferred over
/// [`BTreeMap`][btm] and [`HashMap`][hm].
///
/// Stores each value in a separate node in the state trie.
/// This is different from [`BTreeMap`][btm] and
/// [`HashMap`][hm], which store their _whole_ structure in a
/// _single_ node in the state trie. That is why this map should be preferred.
///
/// The cost of updates to the map are dependent on the length of `K` (in bytes)
/// and the size of the data stored (`V`). Short keys are therefore ideal.
///
/// Can only be constructed by the [`new_map`][StateBuilder::new_map] method on
/// [`StateBuilder`].
///
/// ```
/// # use concordium_std::*;
/// # use concordium_std::test_infrastructure::*;
/// # let mut state_builder = TestStateBuilder::new();
/// /// In an init method:
/// let mut map1 = state_builder.new_map();
/// # map1.insert(0u8, 1u8); // Specifies type of map.
///
/// # let mut host = TestHost::new_with_state_builder((), state_builder);
/// /// In a receive method:
/// let mut map2 = host.state_builder().new_map();
/// # map2.insert(0u16, 1u16); // Specifies type of map.
/// ```
///
/// [hm]: crate::collections::HashMap
/// [btm]: crate::collections::BTreeMap
pub struct StateMap<K, V, S> {
    pub(crate) _marker_key:   PhantomData<K>,
    pub(crate) _marker_value: PhantomData<V>,
    pub(crate) prefix:        StateItemPrefix,
    pub(crate) state_api:     S,
}

#[derive(Debug)]
/// An iterator over the entries of a [`StateMap`].
///
/// Ordered by `K` serialized to bytes.
///
/// This `struct` is created by the [`iter`][StateMap::iter] method on
/// [`StateMap`]. See its documentation for more.
pub struct StateMapIter<'a, K, V, S: HasStateApi> {
    pub(crate) state_iter:       Option<S::IterType>,
    pub(crate) state_api:        S,
    pub(crate) _lifetime_marker: PhantomData<&'a (K, V)>,
}

#[derive(Debug)]
/// A mutable iterator over the entries of a [`StateMap`].
///
/// Ordered lexicographically by `K` via its serialization.
///
/// This `struct` is created by the [`iter_mut`][StateMap::iter_mut] method on
/// [`StateMap`]. See its documentation for more.
pub struct StateMapIterMut<'a, K, V, S: HasStateApi> {
    pub(crate) state_iter:       Option<S::IterType>,
    pub(crate) state_api:        S,
    pub(crate) _lifetime_marker: PhantomData<&'a mut (K, V)>,
}

#[derive(Debug)]
/// A set based on a [Trie](https://en.wikipedia.org/wiki/Trie) in the state.
///
/// In most situations, this type should be preferred over
/// [`BTreeSet`][bts] and [`HashSet`][hs].
/// See [`StateMap`]'s documentation for a more information about why this is
/// the case.
///
/// The cost of updates to the set are dependent on the length of `T` (in
/// bytes).
///
/// [hs]: crate::collections::HashSet
/// [bts]: crate::collections::BTreeSet
pub struct StateSet<T, S> {
    pub(crate) _marker:   PhantomData<T>,
    pub(crate) prefix:    StateItemPrefix,
    pub(crate) state_api: S,
}

/// An iterator over the entries of a [`StateMap`].
///
/// Ordered by `T` serialized to bytes.
///
/// This `struct` is created by the [`iter`][StateSet::iter] method on
/// [`StateSet`]. See its documentation for more.
pub struct StateSetIter<'a, T, S: HasStateApi> {
    pub(crate) state_iter:       Option<S::IterType>,
    pub(crate) state_api:        S,
    pub(crate) _marker_lifetime: PhantomData<&'a T>,
}

#[derive(Debug)]
/// A pointer type for data in the state.
///
/// The actual data is lazily loaded and thereafter cached in memory.
///
/// Due to its laziness, a [`Self`] can be used to defer loading of data in your
/// state. This is useful when part of your state isn't used in every receive
/// method.
///
/// The type parameter `T` is the type stored in the box. The type parameter `S`
/// is the state.
pub struct StateBox<T, S> {
    pub(crate) prefix:     StateItemPrefix,
    pub(crate) state_api:  S,
    pub(crate) lazy_value: RefCell<Option<T>>,
}

#[derive(Debug)]
/// The [`StateRef`] behaves like the type `&'a V` in the way that it can be
/// accessed.
///
/// Implements [`Deref`][crate::ops::Deref] for ease of use.
pub struct StateRef<'a, V> {
    pub(crate) value:            V,
    pub(crate) _marker_lifetime: PhantomData<&'a V>,
}

impl<'a, V> StateRef<'a, V> {
    #[inline(always)]
    pub(crate) fn new(value: V) -> Self {
        Self {
            value,
            _marker_lifetime: PhantomData,
        }
    }
}

impl<'a, V> crate::ops::Deref for StateRef<'a, V> {
    type Target = V;

    #[inline(always)]
    fn deref(&self) -> &Self::Target { &self.value }
}

#[derive(Debug)]
/// The [`StateRefMut<_, V, _>`] behaves like the type [`StateBox<V, _>`] in the
/// way that it can be accessed.
pub struct StateRefMut<'a, V, S> {
    pub(crate) state_box:        StateBox<V, S>,
    pub(crate) _marker_lifetime: PhantomData<&'a mut V>,
}

impl<'a, V, S> StateRefMut<'a, V, S> {
    #[inline(always)]
    pub(crate) fn new(value: V, key: &[u8], state_api: S) -> Self {
        Self {
            state_box:        StateBox::new(value, state_api, key.to_vec()),
            _marker_lifetime: PhantomData,
        }
    }
}

#[derive(Debug)]
#[repr(transparent)]
/// An iterator over a part of the state. Its implementation is supported by
/// host calls.
pub struct ExternStateIter {
    pub(crate) iterator_id: StateIteratorId,
}

pub(crate) type StateEntryId = u64;
pub(crate) type StateIteratorId = u64;
pub(crate) type StateItemPrefix = Vec<u8>;

/// Represents the data in a node in the state trie.
pub struct StateEntry {
    pub(crate) state_entry_id:   StateEntryId,
    pub(crate) key:              Vec<u8>,
    pub(crate) current_position: u32,
}

#[repr(transparent)]
/// A view into a vacant entry in a [`HasStateApi`][`crate::HasStateApi`] type.
/// It is part of the [`EntryRaw`] enum.
///
/// Differs from [`VacantEntry`] in that this has access to the raw bytes stored
/// in the state via a [`HasStateEntry`][crate::HasStateEntry] type.
pub struct VacantEntryRaw<StateEntryType> {
    pub(crate) state_entry: StateEntryType,
}

#[repr(transparent)]
/// A view into an occupied entry in a [`HasStateApi`][`crate::HasStateApi`]
/// type. It is part of the [`EntryRaw`] enum.
///
/// Differs from [`OccupiedEntry`] in that this has access to the raw bytes
/// stored in the state via a [`HasStateEntry`][crate::HasStateEntry] type.
pub struct OccupiedEntryRaw<StateEntryType> {
    pub(crate) state_entry: StateEntryType,
}

/// A view into a single entry in a [`HasStateApi`][`crate::HasStateApi`] type,
/// which may either be vacant or occupied.
///
/// This `enum` is constructed from the [`entry`][crate::HasStateApi::entry]
/// method on a [`HasStateApi`][crate::HasStateApi] type.
pub enum EntryRaw<StateEntryType> {
    Vacant(VacantEntryRaw<StateEntryType>),
    Occupied(OccupiedEntryRaw<StateEntryType>),
}

/// A view into a vacant entry in a [`StateMap`]. It is
/// part of the [`Entry`] enum.
///
/// Differs from [`VacantEntryRaw`] in that this automatically handles
/// serialization.
pub struct VacantEntry<'a, K, V, StateEntryType> {
    pub(crate) key:              K,
    pub(crate) state_entry:      StateEntryType,
    pub(crate) _lifetime_marker: PhantomData<&'a mut (K, V)>,
}

/// A view into an occupied entry in a [`StateMap`]. It can be obtained via the
/// [`StateMap::entry`] method. This allows looking up or modifying the value at
/// a give key in-place.
///
/// Differs from [`OccupiedEntryRaw`] in that this automatically handles
/// serialization.
pub struct OccupiedEntry<'a, K, V, StateEntryType> {
    pub(crate) key:              K,
    pub(crate) value:            V,
    pub(crate) state_entry:      StateEntryType,
    pub(crate) _lifetime_marker: PhantomData<&'a mut (K, V)>,
}

/// A view into a single entry in a [`StateMap`], which
/// may either be vacant or occupied.
///
/// This `enum` is constructed from the [`entry`][StateMap::entry] method
/// on a [`StateMap`] type.
pub enum Entry<'a, K, V, S> {
    Vacant(VacantEntry<'a, K, V, S>),
    Occupied(OccupiedEntry<'a, K, V, S>),
}

#[derive(Default)]
/// A type representing the parameter to init and receive methods.
/// Its trait implementations are backed by host functions.
pub struct ExternParameter {
    pub(crate) current_position: u32,
}

/// A type representing the return value of contract invocation.
/// A contract invocation **may** return a value. It is returned in the
/// following cases
/// - an entrypoint of a V1 contract was invoked and the invocation succeeded
/// - an entrypoint of a V1 contract was invoked and the invocation failed due
///   to a [CallContractError::LogicReject]
///
/// In all other cases there is no response.
///
/// This type is designed to be used via its [Read](crate::Read) and
/// [HasCallResponse](crate::HasCallResponse) traits.
#[derive(Debug)]
pub struct ExternCallResponse {
    /// The index of the call response.
    pub(crate) i:                NonZeroU32,
    pub(crate) current_position: u32,
}

impl ExternCallResponse {
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
/// The intention is that this type is manipulated using methods of the
/// [Write](crate::Write) trait. In particular it can be used as a sink to
/// serialize values into.
pub struct ExternReturnValue {
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
/// Defining a custom error type that implements [`Reject`].
/// ```rust
/// #[derive(Reject)]
/// enum MyCustomError {
///     SomeError,
/// }
///
/// #[receive(contract = "mycontract", name = "receive")]
/// fn contract_receive<S: HasStateApi>(
///     _ctx: &impl HasReceiveContext,
///     _host: &impl HasHost<(), StateApiType = S>,
/// ) -> Result<(), MyCustomError> {
///     Err(MyCustomError::SomeError)
/// }
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
/// #[derive(Reject)]
/// enum MyCustomError {
///     SomeError,
/// }
///
/// #[init(contract = "mycontract")]
/// fn contract_init<S: HasStateApi>(
///     _ctx: &impl HasInitContext,
///     _state_builder: &mut StateBuilder<S>,
/// ) -> Result<((), ()), MyCustomError> {
///     Err(MyCustomError::SomeError)
/// }
/// ```
pub type InitResult<S> = Result<S, Reject>;

/// Operations backed by host functions for the high-level interface.
#[doc(hidden)]
pub struct ExternHost<State> {
    pub state:         State,
    pub state_builder: StateBuilder<ExternStateApi>,
}

#[derive(Default)]
/// An state builder that allows the creation of [`StateMap`], [`StateSet`], and
/// [`StateBox`]. It is parametrized by a parameter `S` that is assumed to
/// implement [`HasStateApi`].
///
/// The state_builder is designed to provide an abstraction over the contract
/// state, abstracting over the exact **keys** (keys in the sense of key-value
/// store, which is the low-level semantics of contract state) that are used
/// when storing specific values.
pub struct StateBuilder<S> {
    pub(crate) state_api: S,
}

#[derive(Debug, Clone, Default)]
#[doc(hidden)]
pub struct ExternStateApi {
    pub(crate) private: (),
}

impl ExternStateApi {
    /// Open the contract state. Only one instance can be opened at the same
    /// time.
    pub fn open() -> Self {
        Self {
            private: (),
        }
    }
}

/// Operations backed by host functions for the low-level interface.
#[doc(hidden)]
#[derive(Default)]
pub struct ExternLowLevelHost {
    pub(crate) state_api:     ExternStateApi,
    pub(crate) state_builder: StateBuilder<ExternStateApi>,
}

/// Context backed by host functions.
#[derive(Default)]
#[doc(hidden)]
pub struct ExternContext<T: sealed::ContextType> {
    marker: crate::marker::PhantomData<T>,
}

#[doc(hidden)]
pub struct ExternChainMeta {}

#[derive(Default)]
#[doc(hidden)]
pub struct ExternInitContext;
#[derive(Default)]
#[doc(hidden)]
pub struct ExternReceiveContext;

pub(crate) mod sealed {
    use super::*;
    /// Marker trait intended to indicate which context type we have.
    /// This is deliberately a sealed trait, so that it is only implementable
    /// by types in this crate.
    pub trait ContextType {}
    impl ContextType for ExternInitContext {}
    impl ContextType for ExternReceiveContext {}
}

#[derive(Debug)]
/// The error type which is returned by methods on
/// [`HasStateApi`][`crate::HasStateApi`].
pub enum StateError {
    /// The subtree is locked.
    SubtreeLocked,
    /// The entry does not exist.
    EntryNotFound,
    /// The iterator does not exist.
    IteratorNotFound,
    /// The parameter does not exist.
    ParameterNotFound,
    /// The specified size is too big.
    SizeTooLarge,
    /// The iterator limit for a prefix has been reached.
    IteratorLimitForPrefixExceeded,
    /// The iterator has already been deleted.
    IteratorAlreadyDeleted,
    /// No nodes exist with the given prefix.
    SubtreeWithPrefixNotFound,
}
