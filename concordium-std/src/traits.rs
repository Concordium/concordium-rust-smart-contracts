//! This module implements traits for the contract interface.
//! This allows setting-up mock objects for testing individual
//! contract invocations.

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

/// Objects which can access chain metadata.
pub trait HasChainMetadata {
    /// Get time in milliseconds at the beginning of this block.
    fn slot_time(&self) -> SlotTime;
    /// Get block height of the current block.
    fn block_height(&self) -> BlockHeight;
    /// Get the height of the last finalized block, i.e., block to which the
    /// current block has a finalized pointer to.
    fn finalized_height(&self) -> FinalizedHeight;
    /// Get the slot number of the current block.
    fn slot_number(&self) -> SlotNumber;
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
    fn created_at(&self) -> TimestampMillis;
    /// Beginning of the month where the credential is no longer valid, in
    /// milliseconds since unix epoch.
    fn valid_to(&self) -> TimestampMillis;
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
    type PolicyIteratorType: Iterator<Item = Self::PolicyType>;
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

/// Objects which can serve as loggers.
///
/// Logging functionality can be used by smart contracts to record events that
/// might be of interest to external parties. These events are not used on the
/// chain, and cannot be observed by other contracts, but they are stored by the
/// node, and can be queried to provide information to off-chain actors.
pub trait HasLogger {
    /// Initialize a logger.
    fn init() -> Self;

    /// Log the given bytes as-is.
    fn log_bytes(&mut self, event: &[u8]);

    #[inline(always)]
    /// Log a serializable event by serializing it with a supplied serializer.
    fn log<S: Serial>(&mut self, event: &S) {
        let mut out = Vec::new();
        if event.serial(&mut out).is_err() {
            crate::trap(); // should not happen
        }
        self.log_bytes(&out)
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
    fn send(ca: &ContractAddress, receive_name: &str, amount: Amount, parameter: &[u8]) -> Self;

    /// If the execution of the first action succeeds, run the second action
    /// as well.
    fn and_then(self, then: Self) -> Self;

    /// If the execution of the first action fails, try the second.
    fn or_else(self, el: Self) -> Self;
}
