//! This module implements traits for the contract interface.
//! This allows setting-up mock objects for testing individual
//! contract invocations.

use std::{cell::RefCell, rc::Rc};

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

use crate::{types::LogError, Entry, StateEntryId, StateMap};
use concordium_contracts_common::*;

/// Objects which can access parameters to contracts.
///
/// This trait has a Read supertrait which means that structured parameters can
/// be directly deserialized by using `.get()` function from the `Get` trait.
///
/// The reuse of `Read` methods is the reason for the slightly strange choice of
/// methods of this trait.
pub trait HasParameter: Read {
    /// Get the size of the parameter to the method.
    fn size(&self) -> u32;
}

/// Objects which can access chain metadata.
pub trait HasChainMetadata {
    /// Get time in milliseconds at the beginning of this block.
    fn slot_time(&self) -> SlotTime;
}

/// A type which has access to a policy of a credential.
/// Since policies can be large this is deliberately written in a relatively
/// low-level style to enable efficient traversal of all the attributes without
/// any allocations.
pub trait HasPolicy {
    /// Identity provider who signed the identity object the credential is
    /// derived from.
    fn identity_provider(&self) -> IdentityProvider;
    /// Beginning of the month in milliseconds since unix epoch when the
    /// credential was created.
    fn created_at(&self) -> Timestamp;
    /// Beginning of the month where the credential is no longer valid, in
    /// milliseconds since unix epoch.
    fn valid_to(&self) -> Timestamp;
    /// Get the next attribute, storing it in the provided buffer.
    /// The return value, if `Some`, is a pair of an attribute tag, and the
    /// length, `n` of the attribute value. In this case, the attribute
    /// value is written in the first `n` bytes of the provided buffer. The
    /// rest of the buffer is unchanged.
    ///
    /// The reason this function is added here, and we don't simply implement
    /// an Iterator for this type is that with the supplied buffer we can
    /// iterate through the elements more efficiently, without any allocations,
    /// the consumer being responsible for allocating the buffer.
    fn next_item(&mut self, buf: &mut [u8; 31]) -> Option<(AttributeTag, u8)>;
}

/// Common data accessible to both init and receive methods.
pub trait HasCommonData {
    type PolicyType: HasPolicy;
    type MetadataType: HasChainMetadata;
    type ParamType: HasParameter + Read;
    type PolicyIteratorType: ExactSizeIterator<Item = Self::PolicyType>;
    /// Policies of the sender of the message.
    /// For init methods this is the would-be creator of the contract,
    /// for the receive this is the policies of the immediate sender.
    ///
    /// In the latter case, if the sender is an account then it is the policies
    /// of the account, if it is a contract then it is the policies of the
    /// creator of the contract.
    fn policies(&self) -> Self::PolicyIteratorType;
    /// Get the reference to chain metadata
    fn metadata(&self) -> &Self::MetadataType;
    /// Get the cursor to the parameter.
    fn parameter_cursor(&self) -> Self::ParamType;
}

/// Types which can act as init contexts.
pub trait HasInitContext<Error: Default = ()>: HasCommonData {
    /// Data needed to open the context.
    type InitData;
    /// Open the init context for reading and accessing values.
    fn open(data: Self::InitData) -> Self;
    /// Who invoked this init call.
    fn init_origin(&self) -> AccountAddress;
}

/// Types which can act as receive contexts.
pub trait HasReceiveContext<Error: Default = ()>: HasCommonData {
    type ReceiveData;

    /// Open the receive context for reading and accessing values.
    fn open(data: Self::ReceiveData) -> Self;
    /// Who is the account that initiated the top-level transaction this
    /// invocation is a part of.
    fn invoker(&self) -> AccountAddress;
    /// The address of the contract being invoked.
    fn self_address(&self) -> ContractAddress;
    /// Balance on the contract before the call was made.
    fn self_balance(&self) -> Amount;
    /// The immediate sender of the message. In general different from the
    /// invoker.
    fn sender(&self) -> Address;
    /// Account which created the contract instance.
    fn owner(&self) -> AccountAddress;
}

/// A type that can serve as the contract state type.
pub trait HasContractState<Error: Default = ()>
where
    Self: Read,
    Self: Write<Err = Error>,
    Self: Seek<Err = Error>, {
    type ContractStateData;
    /// Open the contract state. Only one instance can be opened at the same
    /// time.
    fn open(_: Self::ContractStateData) -> Self;

    /// Get the current size of contract state.
    fn size(&self) -> u32;

    /// Truncate the state to the given size. If the given size is more than the
    /// current state size this operation does nothing. The new position is at
    /// most at the end of the stream.
    fn truncate(&mut self, new_size: u32);

    /// Make sure that the memory size is at least that many bytes in size.
    /// Returns true iff this was successful. The new bytes are initialized as
    /// 0.
    fn reserve(&mut self, len: u32) -> bool;
}

/// A type that can serve as the contract state entry type.
pub trait HasContractStateEntry<Error: Default = ()>
where
    Self: Read,
    Self: Write<Err = Error>,
    Self: Seek<Err = Error>, {
    fn open(entry_id: StateEntryId) -> Self;

    /// Get the file id.
    fn entry_id(&self) -> StateEntryId;

    /// Get the current size of the file.
    fn size(&self) -> u32;

    /// Truncate the file to the given size. If the given size is more than the
    /// current size this operation does nothing. The new position is at
    /// most at the end of the stream.
    fn truncate(&mut self, new_size: u32);

    /// Make sure that the memory size is at least that many bytes in size.
    /// Returns true iff this was successful. The new bytes are initialized as
    /// 0.
    fn reserve(&mut self, len: u32) -> bool;
}

pub trait HasContractStateLL {
    type ContractStateData;
    type EntryType: HasContractStateEntry;
    type IterType: Iterator<Item = Self::EntryType>;

    /// Open the contract state. Only one instance can be opened at the same
    /// time.
    fn open(_: Self::ContractStateData) -> Self;

    /// Lookup an entry in the state.
    fn entry(&self, key: &[u8]) -> Entry<Self::EntryType>;

    /// Insert a key-value-pair in the state..
    /// Returns whether anything was overwritten.
    fn insert(&mut self, key: &[u8], value: &[u8]) -> bool;

    /// Try to get the entry at the given key.
    fn get(&self, key: &[u8]) -> Option<Self::EntryType>;

    /// Returns whether an entry is vacant.
    fn vacant(&self, entry_id: StateEntryId) -> bool;

    /// Creates an entry with the given capacity.
    /// Returns whether another value was overwritten.
    fn create(&mut self, entry_id: StateEntryId, capacity: u32) -> bool;

    /// Delete an entry.
    /// Returns whether the entry actually existed.
    fn delete_entry(&mut self, entry_id: StateEntryId) -> bool;

    /// If exact is set, delete the specific key. Otherwise, delete the entire
    /// subtree. Returns whether the entry or subtree existed.
    fn delete_prefix(&mut self, prefix: &[u8], exact: bool) -> bool;

    /// Get an iterator over a map in the state.
    fn iterator(&self, prefix: &[u8]) -> Self::IterType;
}

pub trait HasContractStateHL {
    type ContractStateData;
    type ContractStateLLType: HasContractStateLL;
    fn open(_: Self::ContractStateData) -> Self;
    fn new_map<K: Serialize, V: Serial + DeserialStateCtx<Self::ContractStateLLType>>(
        &mut self,
    ) -> StateMap<Self::ContractStateLLType, K, V>;
    // fn new_set<V: Serialize>(&mut self) -> StateSet<V>;
    fn get<K: Serial, V: DeserialStateCtx<Self::ContractStateLLType>>(
        &self,
        key: K,
    ) -> Option<ParseResult<V>>;
    fn insert<K: Serial, V: Serial>(&mut self, key: K, value: V) -> bool;
}

pub trait HasStateMap<K, V>
where
    K: Serialize,
    V: Serial + DeserialStateCtx<Self::ContractStateLLType>, {
    type ContractStateLLType: HasContractStateLL;
    fn open<P: Serial>(
        contract_state_ll: Rc<RefCell<Self::ContractStateLLType>>,
        prefix: P,
    ) -> Self;

    fn insert(&mut self, key: K, value: V) -> Option<ParseResult<V>>;

    fn get(&self, key: K) -> Option<ParseResult<V>>;

    // fn entry(&self, key: K) -> Entry<<Self::ContractStateLLType as
    // HasContractStateLL>::EntryType>;
}

/// Objects which can serve as loggers.
///
/// Logging functionality can be used by smart contracts to record events that
/// might be of interest to external parties. These events are not used on the
/// chain, and cannot be observed by other contracts, but they are stored by the
/// node, and can be queried to provide information to off-chain actors.
pub trait HasLogger {
    /// Initialize a logger.
    fn init() -> Self;

    /// Log the given slice as-is. If logging is not successful an error will be
    /// returned.
    fn log_raw(&mut self, event: &[u8]) -> Result<(), LogError>;

    #[inline(always)]
    /// Log a serializable event by serializing it with a supplied serializer.
    fn log<S: Serial>(&mut self, event: &S) -> Result<(), LogError> {
        let mut out = Vec::new();
        if event.serial(&mut out).is_err() {
            crate::trap(); // should not happen
        }
        self.log_raw(&out)
    }
}

/// An object that can serve to construct actions.
///
/// The actions that a smart contract can produce as a
/// result of its execution. These actions form a tree and are executed by
/// the scheduler in the predefined order.
pub trait HasActions {
    /// Default accept action.
    fn accept() -> Self;

    /// Send a given amount to an account.
    fn simple_transfer(acc: &AccountAddress, amount: Amount) -> Self;

    /// Send a message to a contract.
    fn send_raw(
        ca: &ContractAddress,
        receive_name: ReceiveName,
        amount: Amount,
        parameter: &[u8],
    ) -> Self;

    /// If the execution of the first action succeeds, run the second action
    /// as well.
    fn and_then(self, then: Self) -> Self;

    /// If the execution of the first action fails, try the second.
    fn or_else(self, el: Self) -> Self;
}

/// Add optimized unwrap behaviour that aborts the process instead of
/// panicking.
pub trait UnwrapAbort {
    /// The underlying result type of the unwrap, in case of success.
    type Unwrap;
    /// Unwrap or call [trap](./fn.trap.html). In contrast to
    /// the unwrap methods on [Option::unwrap](https://doc.rust-lang.org/std/option/enum.Option.html#method.unwrap)
    /// this method will tend to produce smaller code, at the cost of the
    /// ability to handle the panic.
    /// This is intended to be used only in `Wasm` code, where panics cannot be
    /// handled anyhow.
    fn unwrap_abort(self) -> Self::Unwrap;
}

/// Analogue of the `expect` methods on types such as [Option](https://doc.rust-lang.org/std/option/enum.Option.html),
/// but useful in a Wasm setting.
pub trait ExpectReport {
    type Unwrap;
    /// Like the default `expect` on, e.g., `Result`, but calling
    /// [fail](macro.fail.html) with the given message, instead of `panic`.
    fn expect_report(self, msg: &str) -> Self::Unwrap;
}

/// Analogue of the `expect_err` methods on [Result](https://doc.rust-lang.org/std/result/enum.Result.html),
/// but useful in a Wasm setting.
pub trait ExpectErrReport {
    type Unwrap;
    /// Like the default `expect_err` on, e.g., `Result`, but calling
    /// [fail](macro.fail.html) with the given message, instead of `panic`.
    fn expect_err_report(self, msg: &str) -> Self::Unwrap;
}

/// Analogue of the `expect_none` methods on [Option](https://doc.rust-lang.org/std/option/enum.Option.html),
/// but useful in a Wasm setting.
pub trait ExpectNoneReport {
    /// Like the default `expect_none_report` on, e.g., `Option`, but calling
    /// [fail](macro.fail.html) with the given message, instead of `panic`.
    fn expect_none_report(self, msg: &str);
}

/// The `SerialCtx` trait provides a means of writing structures into byte-sinks
/// (`Write`) using contextual information.
/// The contextual information is:
///
///   - `size_length`: The number of bytes used to record the length of the
///     data.
pub trait SerialCtx {
    /// Attempt to write the structure into the provided writer, failing if
    /// if the length cannot be represented in the provided `size_length` or
    /// only part of the structure could be written.
    ///
    /// NB: We use Result instead of Option for better composability with other
    /// constructs.
    fn serial_ctx<W: Write>(
        &self,
        size_length: schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err>;
}

/// The `DeserialCtx` trait provides a means of reading structures from
/// byte-sources (`Read`) using contextual information.
/// The contextual information is:
///
///   - `size_length`: The expected number of bytes used for the length of the
///     data.
///   - `ensure_ordered`: Whether the ordering should be ensured, for example
///     that keys in `BTreeMap` and `BTreeSet` are in strictly increasing order.
pub trait DeserialCtx: Sized {
    /// Attempt to read a structure from a given source and context, failing if
    /// an error occurs during deserialization or reading.
    fn deserial_ctx<R: Read>(
        size_length: schema::SizeLength,
        ensure_ordered: bool,
        source: &mut R,
    ) -> ParseResult<Self>;
}

pub trait DeserialStateCtx<S>: Sized
where
    S: HasContractStateLL, {
    fn deserial_state_ctx<R: Read>(state: &Rc<RefCell<S>>, source: &mut R) -> ParseResult<Self>;
}
