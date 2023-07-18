use crate as concordium_std;
use crate::{
    cell::UnsafeCell, marker::PhantomData, num::NonZeroU32, Cursor, HasStateApi, Serial, Vec,
};
use concordium_contracts_common::{
    AccountBalance, AccountThreshold, Amount, ParseError, SchemaType, SignatureThreshold,
};
use core::{fmt, str::FromStr};
// Re-export for backward compatibility.
pub use concordium_contracts_common::ExchangeRates;

#[derive(Debug)]
/// A high-level map based on the low-level key-value store, which is the
/// interface provided by the chain.
///
/// In most situations, this collection should be preferred over
/// [`BTreeMap`][btm] and [`HashMap`][hm] since it will be more efficient to
/// lookup and update since costs to lookup and update will grow very slowly
/// with the size of the collection. In contrast, using [`BTreeMap`][btm] and
/// [`HashMap`][hm] almost always entails their serialization, which is linear
/// in the size of the collection.
///
/// The cost of updates to the map are dependent on the length of `K` (in bytes)
/// and the size of the data stored (`V`). Short keys are therefore ideal.
///
/// New maps can be constructed using the
/// [`new_map`][StateBuilder::new_map] method on the [`StateBuilder`].
///
///
/// ```
/// # use concordium_std::*;
/// # use concordium_std::test_infrastructure::*;
/// # let mut state_builder = TestStateBuilder::new();
/// /// In an init method:
/// let mut map1 = state_builder.new_map();
/// # map1.insert(0u8, 1u8); // Specifies type of map.
///
/// # let mut host = TestHost::new((), state_builder);
/// /// In a receive method:
/// let mut map2 = host.state_builder().new_map();
/// # map2.insert(0u16, 1u16);
/// ```
///
/// ## Type parameters
///
/// The map `StateMap<K, V, S>` is parametrized by the type of _keys_ `K`, the
/// type of _values_ `V` and the type of the low-level state `S`. In line with
/// other Rust collections, e.g., [`BTreeMap`][btm] and [`HashMap`][hm]
/// constructing the statemap via [`new_map`](StateBuilder::new_map) does not
/// require anything specific from `K` and `V`. However most operations do
/// require that `K` is serializable and `V` can be stored and loaded in the
/// context of the low-level state `S`.
///
/// This concretely means that `K` must implement
/// [`Serialize`](crate::Serialize) and `V` has to implement
/// [`Serial`](crate::Serial) and
/// [`DeserialWithState<S>`](crate::DeserialWithState). In practice, this means
/// that keys must be _flat_, meaning that it cannot have any references to the
/// low-level state. This is almost all types, except [`StateBox`], [`StateMap`]
/// and [`StateSet`] and types containing these.
///
/// However values may contain references to the low-level state, in particular
/// maps may be nested.
///
/// ### Low-level state `S`
///
/// The type parameter `S` is extra compared to usual Rust collections. As
/// mentioned above it specifies the [low-level state
/// implementation](crate::HasStateApi). This library provides two such
/// implementations. The "external" one, which is the implementation supported
/// by external host functions provided by the chain, and a
/// [test](crate::test_infrastructure::TestStateApi) one. The latter one is
/// useful for testing since it provides an implementation that is easier to
/// construct, execute, and inspect during unit testing.
///
/// In user code this type parameter should generally be treated as boilerplate,
/// and contract entrypoints should always be stated in terms of a generic type
/// `S` that implements [HasStateApi](crate::HasStateApi)
///
/// #### Example
/// ```rust
/// # use concordium_std::*;
/// #[derive(Serial, DeserialWithState)]
/// #[concordium(state_parameter = "S")]
/// struct MyState<S: HasStateApi> {
///     inner: StateMap<u64, u64, S>,
/// }
/// #[init(contract = "mycontract")]
/// fn contract_init<S: HasStateApi>(
///     _ctx: &impl HasInitContext,
///     state_builder: &mut StateBuilder<S>,
/// ) -> InitResult<MyState<S>> {
///     Ok(MyState {
///         inner: state_builder.new_map(),
///     })
/// }
///
/// #[receive(contract = "mycontract", name = "receive", return_value = "Option<u64>")]
/// fn contract_receive<S: HasStateApi>(
///     _ctx: &impl HasReceiveContext,
///     host: &impl HasHost<MyState<S>, StateApiType = S>, // the same low-level state must be propagated throughout
/// ) -> ReceiveResult<Option<u64>> {
///     let state = host.state();
///     Ok(state.inner.get(&0).map(|v| *v))
/// }
/// ```
///
/// ## **Caution**
///
/// `StateMap`s must be explicitly deleted when they are no longer needed,
/// otherwise they will remain in the contract's state, albeit unreachable.
///
/// ```no_run
/// # use concordium_std::*;
/// struct MyState<S: HasStateApi> {
///     inner: StateMap<u64, u64, S>,
/// }
/// fn incorrect_replace<S: HasStateApi>(
///     state_builder: &mut StateBuilder<S>,
///     state: &mut MyState<S>,
/// ) {
///     // The following is incorrect. The old value of `inner` is not properly deleted.
///     // from the state.
///     state.inner = state_builder.new_map(); // ⚠️
/// }
/// ```
/// Instead, either the map should be [cleared](StateMap::clear) or
/// explicitly deleted.
///
/// ```no_run
/// # use concordium_std::*;
/// # struct MyState<S: HasStateApi> {
/// #    inner: StateMap<u64, u64, S>
/// # }
/// fn correct_replace<S: HasStateApi>(
///     state_builder: &mut StateBuilder<S>,
///     state: &mut MyState<S>,
/// ) {
///     state.inner.clear_flat();
/// }
/// ```
/// Or alternatively
/// ```no_run
/// # use concordium_std::*;
/// # struct MyState<S: HasStateApi> {
/// #    inner: StateMap<u64, u64, S>
/// # }
/// fn correct_replace<S: HasStateApi>(
///     state_builder: &mut StateBuilder<S>,
///     state: &mut MyState<S>,
/// ) {
///     let old_map = mem::replace(&mut state.inner, state_builder.new_map());
///     old_map.delete()
/// }
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
/// A high-level set of _flat_ values based on the low-level key-value store,
/// which is the interface provided by the chain.
///
/// In most situations, this collection should be preferred over
/// [`BTreeSet`][bts] and [`HashSet`][hs] since it will be more efficient to
/// lookup and update since costs to lookup and update will grow very slowly
/// with the size of the collection. In contrast, using [`BTreeSet`][bts] and
/// [`HashSet`][hs] almost always entails their serialization, which is linear
/// in the size of the collection.
///
/// The cost of updates to the set are dependent on the serialized size of the
/// value `T`.
///
/// New sets can be constructed using the
/// [`new_set`][StateBuilder::new_set] method on the [`StateBuilder`].
///
/// ## Type parameters
///
/// The set `StateSet<T, S>` is parametrized by the type of _values_ `T`, and
/// the type of the low-level state `S`. In line with other Rust collections,
/// e.g., [`BTreeSet`][bts] and [`HashSet`][hs] constructing the stateset via
/// [`new_set`](StateBuilder::new_set) does not require anything specific from
/// `T`. However most operations do require that `T` implements
/// [`Serialize`](crate::Serialize).
///
/// Since `StateSet<T, S>` itself **does not** implement
/// [`Serialize`](crate::Serialize) **sets cannot be nested**. If this is really
/// required then a custom solution should be devised using the operations on
/// `S` (see [HasStateApi](crate::HasStateApi)).
///
/// ### Low-level state `S`
///
/// The type parameter `S` is extra compared to usual Rust collections. As
/// mentioned above it specifies the [low-level state
/// implementation](crate::HasStateApi). This library provides two such
/// implementations. The "external" one, which is the implementation supported
/// by external host functions provided by the chain, and a
/// [test](crate::test_infrastructure::TestStateApi) one. The latter one is
/// useful for testing since it provides an implementation that is easier to
/// construct, execute, and inspect during unit testing.
///
/// In user code this type parameter should generally be treated as boilerplate,
/// and contract entrypoints should always be stated in terms of a generic type
/// `S` that implements [HasStateApi](crate::HasStateApi)
///
/// #### Example
/// ```rust
/// # use concordium_std::*;
/// #[derive(Serial, DeserialWithState)]
/// #[concordium(state_parameter = "S")]
/// struct MyState<S: HasStateApi> {
///     inner: StateSet<u64, S>,
/// }
/// #[init(contract = "mycontract")]
/// fn contract_init<S: HasStateApi>(
///     _ctx: &impl HasInitContext,
///     state_builder: &mut StateBuilder<S>,
/// ) -> InitResult<MyState<S>> {
///     Ok(MyState {
///         inner: state_builder.new_set(),
///     })
/// }
///
/// #[receive(contract = "mycontract", name = "receive", return_value = "bool")]
/// fn contract_receive<S: HasStateApi>(
///     _ctx: &impl HasReceiveContext,
///     host: &impl HasHost<MyState<S>, StateApiType = S>, // the same low-level state must be propagated throughout
/// ) -> ReceiveResult<bool> {
///     let state = host.state();
///     Ok(state.inner.contains(&0))
/// }
/// ```
///
/// ## **Caution**
///
/// `StateSet`s must be explicitly deleted when they are no longer needed,
/// otherwise they will remain in the contract's state, albeit unreachable.
///
/// ```no_run
/// # use concordium_std::*;
/// struct MyState<S: HasStateApi> {
///     inner: StateSet<u64, S>,
/// }
/// fn incorrect_replace<S: HasStateApi>(
///     state_builder: &mut StateBuilder<S>,
///     state: &mut MyState<S>,
/// ) {
///     // The following is incorrect. The old value of `inner` is not properly deleted.
///     // from the state.
///     state.inner = state_builder.new_set(); // ⚠️
/// }
/// ```
/// Instead, either the set should be [cleared](StateSet::clear) or
/// explicitly deleted.
///
/// ```no_run
/// # use concordium_std::*;
/// # struct MyState<S: HasStateApi> {
/// #    inner: StateSet<u64, S>
/// # }
/// fn correct_replace<S: HasStateApi>(
///     state_builder: &mut StateBuilder<S>,
///     state: &mut MyState<S>,
/// ) {
///     state.inner.clear();
/// }
/// ```
/// Or alternatively
/// ```no_run
/// # use concordium_std::*;
/// # struct MyState<S: HasStateApi> {
/// #    inner: StateSet<u64, S>
/// # }
/// fn correct_replace<S: HasStateApi>(
///     state_builder: &mut StateBuilder<S>,
///     state: &mut MyState<S>,
/// ) {
///     let old_set = mem::replace(&mut state.inner, state_builder.new_set());
///     old_set.delete()
/// }
/// ```
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
/// Due to its laziness, a [`StateBox`] can be used to defer loading of data in
/// your state. This is useful when part of your state isn't used in every
/// receive method.
///
/// The type parameter `T` is the type stored in the box. The type parameter `S`
/// is the state.
pub struct StateBox<T: Serial, S: HasStateApi> {
    pub(crate) state_api: S,
    pub(crate) inner:     UnsafeCell<StateBoxInner<T, S>>,
}

pub(crate) enum StateBoxInner<T, S: HasStateApi> {
    /// Value is loaded in memory, and we have a backing entry.
    Loaded {
        entry:    S::EntryType,
        modified: bool,
        value:    T,
    },
    /// We only have the memory location at which the value is stored.
    Reference {
        prefix: StateItemPrefix,
    },
}

#[derive(Debug)]
/// The [`StateRef`] behaves akin the type `&'a V`, except that it is not
/// copyable. It should be used as [MutexGuard](std::sync::MutexGuard) or
/// similar types which guard access to a resource.
///
/// The type implements [`Deref`][crate::ops::Deref] to `V`, and that is the
/// intended, and only, way to use it.
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
/// The [`StateRefMut<_, V, _>`] behaves like `&mut V`, by analogy with other
/// standard library RAII guards like [`RefMut`](std::cell::RefMut).
/// The type implements [`DerefMut`](crate::ops::DerefMut) which allows the
/// value to be mutated. Additionally, the [`Drop`](Drop) implementation ensures
/// that the value is properly stored in the contract state maintained by the
/// node.
pub struct StateRefMut<'a, V: Serial, S: HasStateApi> {
    pub(crate) entry:            UnsafeCell<S::EntryType>,
    pub(crate) state_api:        S,
    pub(crate) lazy_value:       UnsafeCell<Option<V>>,
    pub(crate) _marker_lifetime: PhantomData<&'a mut V>,
}

impl<'a, V: Serial, S: HasStateApi> StateRefMut<'a, V, S> {
    #[inline(always)]
    pub(crate) fn new(entry: S::EntryType, state_api: S) -> Self {
        Self {
            entry: UnsafeCell::new(entry),
            state_api,
            lazy_value: UnsafeCell::new(None),
            _marker_lifetime: PhantomData,
        }
    }
}

#[derive(Debug)]
#[repr(transparent)]
/// An iterator over a part of the state. Its implementation is supported by
/// host calls.
#[doc(hidden)]
pub struct ExternStateIter {
    pub(crate) iterator_id: StateIteratorId,
}

pub(crate) type StateEntryId = u64;
pub(crate) type StateIteratorId = u64;
pub(crate) type StateItemPrefix = [u8; 8];
/// Type of keys that index into the contract state.
pub type Key = Vec<u8>;

/// Represents the data in a node in the state trie.
pub struct StateEntry {
    pub(crate) state_entry_id:   StateEntryId,
    pub(crate) key:              Key,
    pub(crate) current_position: u32,
}

/// A view into a vacant entry in a [`HasStateApi`][`crate::HasStateApi`] type.
/// It is part of the [`EntryRaw`] enum.
///
/// Differs from [`VacantEntry`] in that this has access to the raw bytes stored
/// in the state via a [`HasStateEntry`][crate::HasStateEntry] type.
pub struct VacantEntryRaw<S> {
    pub(crate) key:       Key,
    pub(crate) state_api: S,
}

#[repr(transparent)]
/// A view into an occupied entry in a [`HasStateApi`][`crate::HasStateApi`]
/// type. It is part of the [`EntryRaw`] enum.
///
/// Differs from [`OccupiedEntry`] in that this has access to the raw bytes
/// stored in the state via a [`HasStateEntry`][crate::HasStateEntry] type.
pub struct OccupiedEntryRaw<StateApi: HasStateApi> {
    pub(crate) state_entry: StateApi::EntryType,
}

/// A view into a single entry in a [`HasStateApi`][`crate::HasStateApi`] type,
/// which may either be vacant or occupied.
///
/// This `enum` is constructed from the [`entry`][crate::HasStateApi::entry]
/// method on a [`HasStateApi`][crate::HasStateApi] type.
pub enum EntryRaw<StateApi: HasStateApi> {
    Vacant(VacantEntryRaw<StateApi>),
    Occupied(OccupiedEntryRaw<StateApi>),
}

/// A view into a vacant entry in a [`StateMap`]. It is
/// part of the [`Entry`] enum.
///
/// Differs from [`VacantEntryRaw`] in that this automatically handles
/// serialization.
pub struct VacantEntry<'a, K, V, S> {
    pub(crate) key:              K,
    pub(crate) key_bytes:        Vec<u8>,
    pub(crate) state_api:        S,
    pub(crate) _lifetime_marker: PhantomData<&'a mut (K, V)>,
}

/// A view into an occupied entry in a [`StateMap`]. It can be obtained via the
/// [`StateMap::entry`] method. This allows looking up or modifying the value at
/// a give key in-place.
///
/// The type implements [`DerefMut`](crate::ops::DerefMut) which allows the
/// value to be mutated. The [`Drop`](Drop) implementation ensures
/// that the value is properly stored in the contract state maintained by the
/// node.
///
/// This differs from [`OccupiedEntryRaw`] in that this automatically handles
/// serialization and provides convenience methods for modifying the value via
/// the [`DerefMut`](crate::ops::DerefMut) implementation.
pub struct OccupiedEntry<'a, K, V: Serial, S: HasStateApi> {
    pub(crate) key:              K,
    pub(crate) value:            V,
    /// Indicates whether the value should be stored by the drop implementation.
    /// This is set when deref_mut method is called only, since that is when we
    /// **might** implicitly mutate the value.
    pub(crate) modified:         bool,
    pub(crate) state_entry:      S::EntryType,
    pub(crate) _lifetime_marker: PhantomData<&'a mut (K, V)>,
}

impl<'a, K, V: Serial, S: HasStateApi> crate::ops::Deref for OccupiedEntry<'a, K, V, S> {
    type Target = V;

    #[inline(always)]
    fn deref(&self) -> &Self::Target { &self.value }
}

impl<'a, K, V: Serial, S: HasStateApi> crate::ops::DerefMut for OccupiedEntry<'a, K, V, S> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.modified = true;
        &mut self.value
    }
}

impl<'a, K, V: Serial, S: HasStateApi> Drop for OccupiedEntry<'a, K, V, S> {
    #[inline(always)]
    fn drop(&mut self) {
        if self.modified {
            self.store_value()
        }
    }
}

/// A view into a single entry in a [`StateMap`], which
/// may either be vacant or occupied.
///
/// This `enum` is constructed from the [`entry`][StateMap::entry] method
/// on a [`StateMap`] type.
pub enum Entry<'a, K, V: Serial, S: HasStateApi> {
    Vacant(VacantEntry<'a, K, V, S>),
    Occupied(OccupiedEntry<'a, K, V, S>),
}

/// Zero-sized placeholder for the parameter data, only used internally by
/// [ExternParameter].
#[doc(hidden)]
pub(crate) struct ExternParameterDataPlaceholder {}

/// A type representing the parameter to init and receive methods.
/// Its trait implementations are backed by host functions.
#[doc(hidden)]
pub struct ExternParameter {
    pub(crate) cursor: Cursor<ExternParameterDataPlaceholder>,
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
#[doc(hidden)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
#[derive(Debug, Clone, PartialEq, Eq)]
/// Errors that may occur when transferring CCD to an account.
pub enum TransferError {
    /// Amount that was to be transferred is not available to the sender.
    AmountTooLarge,
    /// Account that is to be transferred to does not exist.
    MissingAccount,
}

#[repr(i32)]
#[derive(Debug, Clone, PartialEq, Eq)]
/// Errors that may occur when upgrading the smart contract module.
pub enum UpgradeError {
    /// Provided module does not exist.
    MissingModule,
    /// Provided module does not contain a smart contract with a matching name.
    MissingContract,
    /// Provided module is a version 0 smart contract module.
    UnsupportedModuleVersion,
}

/// Error for querying the balance of an account.
/// No account found for the provided account address.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct QueryAccountBalanceError;

/// Error for querying the balance of a smart contract instance.
/// No instance found for the provided contract address.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct QueryContractBalanceError;

/// Error for querying account's public keys.
/// No account found for the provided account address.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct QueryAccountPublicKeysError;

/// Error for checking an account signature.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum CheckAccountSignatureError {
    /// The account does not exist in the state.
    MissingAccount,
    /// The signature data could not be parsed, i.e.,
    /// we could not deserialize the signature map and the data to check the
    /// signature against. This should typically not happen since the
    /// `concordium-std` library prevents calls that could trigger it, but
    /// is here for completeness since it is a possible error returned from
    /// the node.
    MalformedData,
}

/// A wrapper around [`Result`] that fixes the error variant to
/// [`CallContractError`], and the result to `(bool, Option<A>)`.
/// If the result is `Ok` then the boolean indicates whether the state was
/// modified or not, and the second item is the actual return value, which is
/// present (i.e., [`Some`]) if and only if a `V1` contract was invoked.
pub type CallContractResult<A> = Result<(bool, Option<A>), CallContractError<A>>;

/// A wrapper around [`Result`] that fixes the error variant to
/// [`CallContractError`], and the result to [`Option<A>`](Option)
/// If the result is `Ok` then the value is [`None`] if a `V0` contract was
/// invoked, and a return value returned by a `V1` contract otherwise.
pub type ReadOnlyCallContractResult<A> = Result<Option<A>, CallContractError<A>>;

/// A wrapper around [`Result`] that fixes the error variant to
/// [`TransferError`] and result to [()](https://doc.rust-lang.org/std/primitive.unit.html).
pub type TransferResult = Result<(), TransferError>;

/// A wrapper around [`Result`] that fixes the error variant to [`UpgradeError`]
/// and result to [()](https://doc.rust-lang.org/std/primitive.unit.html).
pub type UpgradeResult = Result<(), UpgradeError>;

/// A wrapper around [`Result`] that fixes the error variant to
/// [`QueryAccountBalanceError`] and result to [`AccountBalance`].
pub type QueryAccountBalanceResult = Result<AccountBalance, QueryAccountBalanceError>;

/// A wrapper around [`Result`] that fixes the error variant to
/// [`QueryContractBalanceError`] and result to [`Amount`].
pub type QueryContractBalanceResult = Result<Amount, QueryContractBalanceError>;

/// A wrapper around [`Result`] that fixes the error variant to
/// [`QueryAccountPublicKeysError`] and result to [`AccountPublicKeys`].
pub type QueryAccountPublicKeysResult = Result<AccountPublicKeys, QueryAccountPublicKeysError>;

/// A wrapper around [`Result`] that fixes the error variant to
/// [`CheckAccountSignatureError`] and result to [`bool`].
pub type CheckAccountSignatureResult = Result<bool, CheckAccountSignatureError>;

pub(crate) type KeyIndex = u8;

#[derive(crate::Serialize, Debug, SchemaType)]
/// A public indexed by the signature scheme. Currently only a
/// single scheme is supported, `ed25519`.
pub(crate) enum PublicKey {
    Ed25519(PublicKeyEd25519),
}

#[derive(crate::Serialize, Debug, SchemaType)]
pub(crate) struct CredentialPublicKeys {
    #[concordium(size_length = 1)]
    pub(crate) keys:      crate::collections::BTreeMap<KeyIndex, PublicKey>,
    pub(crate) threshold: SignatureThreshold,
}

#[derive(crate::Serialize, Debug, SchemaType)]
/// Public keys of an account, together with the thresholds.
/// This type is deliberately made opaque, but it has serialization instances
/// since inside smart contracts there is no need to inspect the values other
/// than to pass them to verification functions.
pub struct AccountPublicKeys {
    #[concordium(size_length = 1)]
    pub(crate) keys:      crate::collections::BTreeMap<CredentialIndex, CredentialPublicKeys>,
    pub(crate) threshold: AccountThreshold,
}

pub(crate) type CredentialIndex = u8;

#[derive(crate::Serialize, Debug, SchemaType)]
#[non_exhaustive]
/// A cryptographic signature indexed by the signature scheme. Currently only a
/// single scheme is supported, `ed25519`.
pub enum Signature {
    Ed25519(SignatureEd25519),
}

#[derive(crate::Serialize, Debug, SchemaType)]
#[concordium(transparent)]
/// Account signatures. This is an analogue of transaction signatures that are
/// part of transactions that get sent to the chain.
///
/// This type is deliberately made opaque, but it has serialization instances.
/// It should be thought of as a nested map, indexed on the outer layer by
/// credential indexes, and the inner map maps key indices to [`Signature`]s.
pub struct AccountSignatures {
    #[concordium(size_length = 1)]
    pub(crate) sigs: crate::collections::BTreeMap<CredentialIndex, CredentialSignatures>,
}

#[derive(crate::Serialize, Debug, SchemaType)]
#[concordium(transparent)]
pub(crate) struct CredentialSignatures {
    #[concordium(size_length = 1)]
    sigs: crate::collections::BTreeMap<KeyIndex, Signature>,
}

/// A type representing the attributes, lazily acquired from the host.
#[derive(Clone, Copy, Default)]
pub struct AttributesCursor {
    /// Current position of the cursor, starting from 0.
    /// Note that this is only for the variable attributes.
    /// `created_at` and `valid_to` will require.
    pub(crate) current_position: u32,
    /// The number of remaining items in the policy.
    pub(crate) remaining_items:  u16,
    /// The total number of items. Used for creating new attribute cursors.
    pub(crate) total_items:      u16,
}

/// An iterator over the attributes of a policy.
/// The iterator returns pairs of
/// [`AttributeTag`](concordium_contracts_common::AttributeTag) and
/// [`AttributeValue`](concordium_contracts_common::AttributeValue).
#[repr(transparent)]
pub struct PolicyAttributesIter {
    pub(crate) cursor: AttributesCursor,
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
/// Defining a custom error type that implements [`Reject`] and [`Serial`].
/// ```no_run
/// # use concordium_std::*;
/// #[derive(Serial, Reject)]
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
/// Defining a custom error type that implements [`Reject`] and [`Serial`].
/// ```no_run
/// # use concordium_std::*;
/// #[derive(Serial, Reject)]
/// enum MyCustomError {
///     SomeError,
/// }
///
/// #[init(contract = "mycontract")]
/// fn contract_init<S: HasStateApi>(
///     _ctx: &impl HasInitContext,
///     _state_builder: &mut StateBuilder<S>,
/// ) -> Result<(), MyCustomError> {
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

impl<S> StateBuilder<S> {
    #[doc(hidden)]
    pub fn into_inner(self) -> S { self.state_api }
}

/// A struct for which HasCryptoPrimitives is implemented via the crypto host
/// functions.
#[doc(hidden)]
pub struct ExternCryptoPrimitives;

/// Public key for Ed25519. Must be 32 bytes long.
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Ord)]
#[repr(transparent)]
pub struct PublicKeyEd25519(pub [u8; 32]);

impl fmt::Display for PublicKeyEd25519 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in self.0 {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl FromStr for PublicKeyEd25519 {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() != 64 {
            return Err(ParseError {});
        }

        let mut public_key: [u8; 32] = [0u8; 32];
        for (i, place) in public_key.iter_mut().enumerate() {
            *place = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).map_err(|_| ParseError {})?;
        }

        Ok(PublicKeyEd25519(public_key))
    }
}

#[cfg(feature = "concordium-quickcheck")]
/// Arbitrary public keys.
/// Note that this is a simple generator that might produce an array of bytes
/// that is not a valid public key.
impl quickcheck::Arbitrary for PublicKeyEd25519 {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let lower: u128 = quickcheck::Arbitrary::arbitrary(g);
        let upper: u128 = quickcheck::Arbitrary::arbitrary(g);
        let mut out = [0u8; 32];
        out[..16].copy_from_slice(&lower.to_le_bytes());
        out[16..].copy_from_slice(&upper.to_le_bytes());
        PublicKeyEd25519(out)
    }
}

/// Public key for ECDSA over Secp256k1. Must be 33 bytes long.
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Ord)]
#[repr(transparent)]
pub struct PublicKeyEcdsaSecp256k1(pub [u8; 33]);

impl fmt::Display for PublicKeyEcdsaSecp256k1 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in self.0 {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl FromStr for PublicKeyEcdsaSecp256k1 {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() != 66 {
            return Err(ParseError {});
        }

        let mut public_key: [u8; 33] = [0u8; 33];
        for (i, place) in public_key.iter_mut().enumerate() {
            *place = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).map_err(|_| ParseError {})?;
        }

        Ok(PublicKeyEcdsaSecp256k1(public_key))
    }
}

/// Signature for a Ed25519 message. Must be 64 bytes long.
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Ord)]
#[repr(transparent)]
pub struct SignatureEd25519(pub [u8; 64]);

impl fmt::Display for SignatureEd25519 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in self.0 {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl FromStr for SignatureEd25519 {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() != 128 {
            return Err(ParseError {});
        }

        let mut signature: [u8; 64] = [0u8; 64];
        for (i, place) in signature.iter_mut().enumerate() {
            *place = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).map_err(|_| ParseError {})?;
        }

        Ok(SignatureEd25519(signature))
    }
}

/// Signature for a ECDSA (over Secp256k1) message. Must be 64 bytes longs
/// (serialized in compressed format).
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Ord)]
#[repr(transparent)]
pub struct SignatureEcdsaSecp256k1(pub [u8; 64]);

impl fmt::Display for SignatureEcdsaSecp256k1 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in self.0 {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl FromStr for SignatureEcdsaSecp256k1 {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() != 128 {
            return Err(ParseError {});
        }

        let mut signature: [u8; 64] = [0u8; 64];
        for (i, place) in signature.iter_mut().enumerate() {
            *place = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).map_err(|_| ParseError {})?;
        }

        Ok(SignatureEcdsaSecp256k1(signature))
    }
}

/// Sha2 digest with 256 bits (32 bytes).
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Ord)]
#[repr(transparent)]
pub struct HashSha2256(pub [u8; 32]);

impl fmt::Display for HashSha2256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in self.0 {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl FromStr for HashSha2256 {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() != 64 {
            return Err(ParseError {});
        }

        let mut hash: [u8; 32] = [0u8; 32];
        for (i, place) in hash.iter_mut().enumerate() {
            *place = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).map_err(|_| ParseError {})?;
        }

        Ok(HashSha2256(hash))
    }
}

/// Sha3 digest with 256 bits (32 bytes).
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Ord)]
#[repr(transparent)]
pub struct HashSha3256(pub [u8; 32]);

/// Keccak digest with 256 bits (32 bytes).
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Ord)]
#[repr(transparent)]
pub struct HashKeccak256(pub [u8; 32]);

#[derive(Debug, Clone, Default)]
#[doc(hidden)]
pub struct ExternStateApi;

impl ExternStateApi {
    /// Open the contract state. Only one instance can be opened at the same
    /// time.
    pub fn open() -> Self { Self }
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
#[repr(u8)]
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

/// The location of the metadata and an optional hash of the content.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct MetadataUrl {
    /// The URL following the specification RFC1738.
    pub url:  crate::String,
    /// A optional hash of the content.
    pub hash: Option<[u8; 32]>,
}
