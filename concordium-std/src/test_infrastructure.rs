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
//! fn contract_init<I: HasInitContext<()>, L: HasLogger>(
//!     ctx: &I,
//!     _amount: Amount,
//!     _logger: &mut L,
//! ) -> InitResult<State> { ... }
//!
//! #[receive(contract = "noop", name = "receive")]
//! fn contract_receive<R: HasReceiveContext<()>, L: HasLogger, A: HasActions>(
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
//!         let mut logger = LogRecorder::init();
//!         let result = contract_init(&ctx, 0, &mut logger);
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
use crate::*;

#[cfg(not(feature = "std"))]
use alloc::boxed::Box;
#[cfg(feature = "std")]
use std::boxed::Box;

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
    pub(crate) slot_number:      Option<SlotNumber>,
    pub(crate) block_height:     Option<BlockHeight>,
    pub(crate) finalized_height: Option<FinalizedHeight>,
    pub(crate) slot_time:        Option<SlotTime>,
}

/// Placeholder for the initial context. All the fields can be set optionally
/// and the getting an unset field will result in calling
/// [`fail!`](../macro.fail.html). Use only in tests!
///
/// # Setters
/// Every field have a setter function prefixed with `set_`.
///
/// ### Example
/// Creating an empty context and setting the `init_origin`.
/// ```
/// let mut ctx = InitContextTest::empty();
/// ctx.set_init_origin(AccountAddress([0u8; 32]));
/// ```
/// ## Set chain meta data
/// Chain meta data is set using setters on the public field `metadata`
/// (see [`ChainMetaTest`](struct.ChainMetaTest.html)).
///
/// ### Example
/// Creating an empty context and setting the `slot_time` metadata.
/// ```
/// let mut ctx = InitContextTest::empty();
/// ctx.metadata.set_slot_time(1609459200);
/// ```
///
/// # Use case example
///
/// ```rust
/// #[init(contract = "noop")]
/// fn contract_init<I: HasInitContext<()>, L: HasLogger>(
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
/// # Default
/// Defaults to having all the fields unset, and constructing
/// [`ChainMetaTest`](struct.ChainMetaTest.html) using default.
#[derive(Default, Clone)]
pub struct InitContextTest<'a> {
    pub metadata:           ChainMetaTest,
    pub(crate) parameter:   Option<&'a [u8]>,
    pub(crate) init_origin: Option<AccountAddress>,
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
/// Chain meta data is set using setters on the public field `metadata`
/// (see [`ChainMetaTest`](struct.ChainMetaTest.html)).
///
/// ### Example
/// Creating an empty context and setting the `slot_time` metadata.
/// ```
/// let mut ctx = ReceiveContextTest::empty();
/// ctx.metadata.set_slot_time(1609459200);
/// ```
///
/// # Use case example
/// Creating a context for running unit tests
/// ```rust
/// #[receive(contract = "mycontract", name = "receive")]
/// fn contract_receive<R: HasReceiveContext<()>, L: HasLogger, A: HasActions>(
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
#[derive(Default, Clone)]
pub struct ReceiveContextTest<'a> {
    pub metadata:            ChainMetaTest,
    pub(crate) parameter:    Option<&'a [u8]>,
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

    /// Set the block height
    pub fn set_block_height(&mut self, value: BlockHeight) -> &mut Self {
        self.block_height = Some(value);
        self
    }

    /// Set the finalized block height
    pub fn set_finalized_height(&mut self, value: FinalizedHeight) -> &mut Self {
        self.finalized_height = Some(value);
        self
    }

    /// Set the slot number
    pub fn set_slot_number(&mut self, value: SlotNumber) -> &mut Self {
        self.slot_number = Some(value);
        self
    }
}

impl<'a> InitContextTest<'a> {
    /// Create an `InitContextTest` where every field is unset, and getting any
    /// of the fields will result in [`fail!`](../macro.fail.html).
    pub fn empty() -> Self { Default::default() }

    /// Set the parameter bytes of the `InitContextTest`
    pub fn set_parameter(&mut self, value: &'a [u8]) -> &mut Self {
        self.parameter = Some(value);
        self
    }

    /// Set `init_origin` in the `InitContextTest`
    pub fn set_init_origin(&mut self, value: AccountAddress) -> &mut Self {
        self.init_origin = Some(value);
        self
    }
}

impl<'a> ReceiveContextTest<'a> {
    /// Create an `InitContextTest` where every field is unset, and getting any
    /// of the fields will result in [`fail!`](../macro.fail.html).
    pub fn empty() -> Self { Default::default() }

    pub fn set_parameter(&mut self, value: &'a [u8]) -> &mut Self {
        self.parameter = Some(value);
        self
    }

    pub fn set_invoker(&mut self, value: AccountAddress) -> &mut Self {
        self.invoker = Some(value);
        self
    }

    pub fn set_self_address(&mut self, value: ContractAddress) -> &mut Self {
        self.self_address = Some(value);
        self
    }

    pub fn set_self_balance(&mut self, value: Amount) -> &mut Self {
        self.self_balance = Some(value);
        self
    }

    pub fn set_sender(&mut self, value: Address) -> &mut Self {
        self.sender = Some(value);
        self
    }

    pub fn set_owner(&mut self, value: AccountAddress) -> &mut Self {
        self.owner = Some(value);
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

    fn block_height(&self) -> BlockHeight {
        unwrap_ctx_field(self.block_height, "metadata.block_height")
    }

    fn finalized_height(&self) -> FinalizedHeight {
        unwrap_ctx_field(self.finalized_height, "metadata.finalized_height")
    }

    fn slot_number(&self) -> SlotNumber {
        unwrap_ctx_field(self.slot_number, "metadata.slot_number")
    }
}

impl<'a> HasInitContext<()> for InitContextTest<'a> {
    type InitData = ();
    type MetadataType = ChainMetaTest;
    type ParamType = Cursor<&'a [u8]>;

    fn open(_data: Self::InitData) -> Self { InitContextTest::default() }

    fn init_origin(&self) -> AccountAddress { unwrap_ctx_field(self.init_origin, "init_origin") }

    fn parameter_cursor(&self) -> Self::ParamType {
        Cursor::new(unwrap_ctx_field(self.parameter, "parameter"))
    }

    fn metadata(&self) -> &Self::MetadataType { &self.metadata }
}

impl<'a> HasReceiveContext<()> for ReceiveContextTest<'a> {
    type MetadataType = ChainMetaTest;
    type ParamType = Cursor<&'a [u8]>;
    type ReceiveData = ();

    fn open(_data: Self::ReceiveData) -> Self { ReceiveContextTest::default() }

    fn parameter_cursor(&self) -> Self::ParamType {
        Cursor::new(unwrap_ctx_field(self.parameter, "parameter"))
    }

    fn metadata(&self) -> &Self::MetadataType { &self.metadata }

    fn invoker(&self) -> AccountAddress { unwrap_ctx_field(self.invoker, "invoker") }

    fn self_address(&self) -> ContractAddress {
        unwrap_ctx_field(self.self_address, "self_address")
    }

    fn self_balance(&self) -> Amount { unwrap_ctx_field(self.self_balance, "self_balance") }

    fn sender(&self) -> Address { unwrap_ctx_field(self.sender, "sender") }

    fn owner(&self) -> AccountAddress { unwrap_ctx_field(self.owner, "owner") }
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

    fn log_bytes(&mut self, event: &[u8]) { self.logs.push(event.to_vec()) }
}

/// An actions tree, used to provide a more simple presentation for testing.
#[derive(Eq, PartialEq, Debug)]
pub enum ActionsTree {
    Accept,
    SimpleTransfer {
        to:     AccountAddress,
        amount: Amount,
    },
    Send {
        to:           ContractAddress,
        receive_name: String,
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

    fn send(ca: &ContractAddress, receive_name: &str, amount: Amount, parameter: &[u8]) -> Self {
        ActionsTree::Send {
            to: *ca,
            receive_name: receive_name.to_string(),
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
