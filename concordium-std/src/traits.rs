//! This module implements traits for the contract interface.
//! This allows setting-up mock objects for testing individual
//! contract invocations.

use crate::{
    types::{LogError, StateError},
    Allocator, CallContractResult, EntryRaw, TransferResult,
};
#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
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

/// Objects which can access call responses from contract invocations.
///
/// This trait has a Read supertrait which means that structured call responses
/// can be directly deserialized by using `.get()` function from the `Get`
/// trait.
///
/// The reuse of `Read` methods is the reason for the slightly strange choice of
/// methods of this trait.
pub trait HasCallResponse: Read {
    /// Get the size of the call response to the contract invocation.
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
    /// The immediate sender of the message. In general different from the
    /// invoker.
    fn sender(&self) -> Address;
    /// Account which created the contract instance.
    fn owner(&self) -> AccountAddress;
}

/// A type that can serve as the contract state entry type.
pub trait HasStateEntry
where
    Self: Read,
    Self: Write<Err = Self::Error>,
    Self: Seek<Err = Self::Error>, {
    type StateEntryData;
    type StateEntryKey;
    type Error: Default;

    /// Get the current size of the entry.
    /// Returns an error if the entry does not exist.
    fn size(&self) -> Result<u32, Self::Error>;

    /// Truncate the entry to the given size. If the given size is more than the
    /// current size this operation does nothing. The new position is at
    /// most at the end of the stream.
    /// Returns an error if the entry does not exist.
    fn truncate(&mut self, new_size: u32) -> Result<(), Self::Error>;

    /// Make sure that the memory size is at least that many bytes in size.
    /// Returns `Ok` iff this was successful. The new bytes are initialized as
    /// 0.
    /// Returns an error if the entry does not exist.
    fn reserve(&mut self, len: u32) -> Result<(), Self::Error> {
        if self.size()? < len {
            self.resize(len)
        } else {
            Ok(())
        }
    }

    /// Get a reference to the entry's key.
    fn get_key(&self) -> &[u8];

    /// Resize the entry to the given size.
    /// Returns an error if the entry does not exist.
    fn resize(&mut self, new_size: u32) -> Result<(), Self::Error>;
}

pub trait HasState: Clone {
    type StateData;
    type EntryType: HasStateEntry;
    type IterType: Iterator<Item = Self::EntryType>;

    /// Open the contract state. Only one instance can be opened at the same
    /// time.
    fn open(_: Self::StateData) -> Self;

    /// Get an entry in the state.
    /// Returns an error if it is part of a locked subtree.
    fn entry(&mut self, key: &[u8]) -> Result<EntryRaw<Self::EntryType>, StateError>;

    /// Create a new entry in the state.
    /// Returns an error if it is part of a locked subtree.
    fn create(&mut self, key: &[u8]) -> Result<Self::EntryType, StateError>;

    /// Lookup an entry in the state.
    fn lookup(&self, key: &[u8]) -> Option<Self::EntryType>;

    /// Delete an entry.
    /// Returns an error if the entry did not exist, or if it is part of a
    /// locked subtree.
    fn delete_entry(&mut self, entry: Self::EntryType) -> Result<(), StateError>;

    /// Delete the entire subtree.
    /// Returns an error if no nodes with that prefix exists, or if it is part
    /// of a locked subtree.
    fn delete_prefix(&mut self, prefix: &[u8]) -> Result<(), StateError>;

    /// Get an iterator over a map in the state.
    /// Returns an error if the number of active iterators fro the same prefix
    /// exceeds [u16::MAX].
    fn iterator(&self, prefix: &[u8]) -> Result<Self::IterType, StateError>;

    /// Delete an iterator.
    fn delete_iterator(&mut self, iter: Self::IterType);
}

/// A type that can serve as the host.
/// It supports invoking operations, accessing state, and self_balance.
pub trait HasHost<State> {
    type StateType: HasState;

    /// The type of return values this host provides. This is the raw return
    /// value. The intention is that it will be deserialized by the
    /// consumer, via the [Read] implementation.
    ///
    /// The Debug requirement exists so that consumers of this trait may use
    /// methods like [ExpectReport::expect_report].
    type ReturnValueType: HasCallResponse + crate::fmt::Debug;

    /// Perform a transfer to the given account if the contract has sufficient
    /// balance.
    fn invoke_transfer(&self, receiver: &AccountAddress, amount: Amount) -> TransferResult;

    /// Invoke a given method of a contract with the amount and parameter
    /// provided. If invocation succeeds then the return value is a pair of
    /// a boolean which indicates whether the state of the contract has changed
    /// or not, and a possible return value. The return value is present if and
    /// only if a V1 contract was invoked.
    fn invoke_contract<'a, 'b>(
        &'a mut self,
        to: &'b ContractAddress,
        parameter: Parameter<'b>,
        method: EntrypointName<'b>,
        amount: Amount,
    ) -> CallContractResult<Self::ReturnValueType>;

    /// Get an immutable refernce to the contract state.
    fn state(&self) -> &State;

    /// Get a mutable reference to the contract state.
    fn state_mut(&mut self) -> &mut State;

    /// Get the allocator for the contract state.
    fn allocator(&mut self) -> &mut Allocator<Self::StateType>;

    /// Get the contract balance.
    fn self_balance(&self) -> Amount;
}

/// A type that can be freed in the state.
/// For simple types, such as `u8` and `String`, the `free` methods is a no-op.
/// But for [crate::StateBox], [crate::StateMap], [crate::StateSet], `free`
/// makes sure to the delete _all_ the necessary data.
pub trait Freeable {
    /// Delete all items that this type owns in the state.
    fn free(self);
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
    S: HasState, {
    fn deserial_state_ctx<R: Read>(state: &S, source: &mut R) -> ParseResult<Self>;
}
