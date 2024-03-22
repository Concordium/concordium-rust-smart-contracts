//! This library provides the core API that can be used to write smart contracts
//! for the Concordium blockchain. It aims to provide safe wrappers around the
//! core primitives exposed by the chain and accessible to smart contracts.
//!
//! The library is meant to be used as a standard library for developing smart
//! contracts. For this reason it re-exports a number of definitions from other
//! libraries.
//!
//! # Versions
//!
//! The concordium blockchain at present supports two variants of smart
//! contracts. The original V0 contracts that use message-passing for
//! communication and have limited state, and V1 contracts which use synchronous
//! calls, and have extended state. Versions 1 and 2 of `concordium-std`
//! **support only V0 contracts**. Version 3 and later of `concordium-std`
//! **supports only V1 contracts**.
//!
//! Also note that `concordium-std` version 4 only works with `cargo-concordium`
//! version 2.1+.
//!
//! Version 8.1 deprecates the module [`test_infrastructure`] in favor of the
//! library [concordium_smart_contract_testing], which should be used instead.
//! For more details including how to migrate your contract, see the
//! [Deprecating the
//! `test_infrastructure`](#deprecating-the-test_infrastructure) section.
//!
//! # Panic handler
//!
//! When compiled without the `std` feature this crate sets the panic handler
//! so that it terminates the process immediately, without any unwinding or
//! prints.
//! Concretely, when compiled to the `wasm32` target panic boils down to the
//! `unreachable` instruction, which triggers a runtime failure, aborting
//! execution of the program.
//!
//! # Features
//!
//! This library has the following features:
//! [`std`](#std-build-with-the-rust-standard-library),
//! [`build-schema`](#build-schema-build-for-generating-a-module-schema),
//! [`wasm-test`](#wasm-test-build-for-testing-in-wasm),
//! [`crypto-primitives`][crypto-feature], and
//! [`bump_alloc`](#use-a-custom-allocator)
//! [`debug`](#emit-debug-information)
//!
//! [crypto-feature]:
//! #crypto-primitives-for-testing-crypto-with-actual-implementations
//!
//! ## `std`: Build with the Rust standard library
//!
//! By default this library will be linked with the
//! [std](https://doc.rust-lang.org/std/) crate, the rust standard library,
//! however to minimize code size this library supports toggling compilation
//! with the `#![no_std]` attribute via the feature `std` which is enabled by
//! default. Compilation without the `std` feature requires a nightly version of
//! rust.
//!
//! To use this library without the `std` feature you have to disable it, which
//! can be done, for example, as follows.
//! ```toml
//! [dependencies.concordium-std]
//! default-features = false
//! ```
//! In your project's `Cargo.toml` file.
//!
//! ## `build-schema`: Build for generating a module schema
//!
//! **WARNING** Building with this feature enabled is meant for tooling, and the
//! result is not intended to be deployed on chain.
//!
//! This library provides a way to automate the building of smart contract
//! module schema, by allowing the contract to be built exporting getter
//! functions for the `concordium_contracts_common::schema::Type` of Types for
//! contract state and parameters.
//! This special build is only intended to be used for generating the schema
//! and is not meant to be deployed, since the build exports functions that do
//! not conform to the expected API of smart contracts.
//! The build is enabled by setting the feature `build-schema`.
//!
//! **Note** This feature is used by `cargo-concordium`, when building with
//! schema and for most cases this feature should not be set manually.
//!
//! ## `wasm-test`: Build for testing in Wasm
//!
//! **WARNING** Building with this feature enabled is meant for tooling, and the
//! result is not intended to be deployed on chain.
//!
//! The macros [`#[concordium_test]`](attr.concordium_test.html) and
//! [`#[concordium_cfg_test]`](attr.concordium_cfg_test.html) are reduced to
//! `#[test]` and `#[cfg(test)]` unless the `wasm-test` feature is enabled.
//!
//! With the `wasm-test` feature enabled, the
//! [`#[concordium_test]`](attr.concordium_test.html) macro exports the test as
//! an `extern` function, allowing tools such as `cargo-concordium` to call the
//! test functions directly, when compiled to Wasm.
//! Without the feature it falls back to `#[test]`.
//!
//! With the 'wasm-test' feature enabled, the
//! [`#[concordium_cfg_test]`](attr.concordium_cfg_test.html) macro allows the
//! annotated code to be included in the build. Without the feature, it falls
//! back to `#[cfg(test)]`.
//!
//! **Note** This feature is used by `cargo-concordium`, when building for
//! testing and for most cases this feature should not be set manually.
//!
//! ## `crypto-primitives`: For testing crypto with actual implementations
//!
//! This features is only relevant when using the **deprecated**
//! [test_infrastructure].
//!
//! Build with this feature if you want to run smart contract tests with actual
//! (i.e., not mock) implementations of the cryptographic primitives from
//! [`HasCryptoPrimitives`].
//!
//! **WARNING**: It is not possible to build this crate on macOS with the
//! `crypto-primitives` feature when targeting `wasm32-unknown-unknown`.
//! The issue arises when compiling the [`secp256k1`](https://docs.rs/secp256k1/latest/secp256k1/) crate.
//!
//! ## Use a custom allocator
//!
//! Some operations in `concordium-std` need to dynamically allocate memory.
//! Rust programs compiled with default compiler settings have access to a
//! [standard allocator](https://doc.rust-lang.org/std/alloc/struct.System.html)
//! implemented in the Rust standard library. When using the
//! `no-std` feature there is no default allocator provided by the Rust
//! toolchain, and so one must be set explicitly.
//!
//! In the past `concordium-std` hard-coded the use of [wee_alloc](https://docs.rs/wee_alloc/)
//! however since version `5.2.0` this is no longer the case.
//! Instead no allocator is set by default, however there is a `bump_alloc`
//! feature (disabled by default) that can be enabled which sets the allocator
//! to `bump_alloc`, which ships with `concordium-std`. This can be used both
//! with and without the `std` feature.
//!
//! The main reason for using `bump_alloc` instead of the default allocator,
//! even in `std` builds, is that `bump_alloc` has a smaller code footprint,
//! i.e, the resulting smart contracts are going to be smaller by about 6-10kB,
//! which means they are cheaper to deploy and run. `bump_alloc` is designed to
//! be simple and fast, but it does not use the memory very efficiently. For
//! short-lived programs, such as smart contracts, this is usually the right
//! tradeoff. Especially for contracts such as those dealing with tokens.
//! For very complex contracts it may be beneficial to run benchmarks to see
//! whether `bump_alloc` is the best option. See the Rust [allocator](https://doc.rust-lang.org/std/alloc/index.html#the-global_allocator-attribute)
//! documentation for more context and details on using custom allocators.
//!
//! # Emit debug information
//!
//! During testing and debugging it is often useful to emit debug information to
//! narrow down the source of the problem. `concordium-std` supports this using
//! the [`concordium_dbg`] macro which will emit its arguments using a special
//! host function `debug_print` which is only available when the `debug` feature
//! is enabled. The output of this function is used by `cargo concordium run`
//! and `cargo concordium test` to display any output that was emitted.
//!
//! The `debug` feature should typically not be enabled manually. It is used
//! implicitly by `cargo concordium` when debug output is requested. It is also
//! **crucial** that the `debug` feature is **not** enabled when building the
//! contract for deployment. If it is the contract is most likely to be rejected
//! when it is being deployed to the chain. The `concordium_dbg!` macro will
//! ignore its arguments when the `debug` feature is not enabled.
//!
//! # Essential types
//!
//! This crate has a number of essential types that are used when writing smart
//! contracts. The structure of these are, at present, a bit odd without the
//! historic context, which is explained below.
//!
//! Prior to version 8.1, a number of traits and generics were used when writing
//! smart contracts, e.g. [`HasHost`], to support the usage of
//! [`crate::test_infrastructure`] for testing, where two primary
//! implementations of each trait existed. The first one is supported by
//! **host** functions, and this is the implementation that is used when
//! contracts are executed by notes. The second set of implementations supports
//! testing contracts with [`crate::test_infrastructure`], but since the
//! deprecation of this module, the preferred way of writing contracts is to use
//! the concrete types.
//!
//! The essential concrete types are:
//! - [`StateApi`] for operations possible on the contract state
//! - [`Host`] for invoking operations on the host and accessing the state
//! - [`InitContext`] for all the context data available to the init functions
//! - [`ReceiveContext`] for accessing all the context data available to the
//!   receive functions
//! - [`ExternParameter`] for accessing the contract parameter
//! - [`Logger`] for logging data during smart contract execution
//! - [`Policy`] for accessing the policy of the sender, either of the init or
//!   receive method
//! - [`CryptoPrimitives`] for using cryptographic primitives such as hashing
//!   and signature verification.
//!
//! Most of these are type aliases for similarly named structs prefixed with
//! `Extern`. The extern prefix made sense when two different implementations of
//! the traits were in play. Since that is no longer the case, we decided to
//! simplify the names with aliases.
//!
//! # Signalling errors
//!
//! On the Wasm level contracts can signal errors by returning a negative i32
//! value as a result of either initialization or invocation of the receive
//! method. If the error is a logic error and the contract executes successfully
//! then it can also produce a return value, which may provide additional detail
//! of the error to the caller. To make error handling more pleasant we provide
//! the [Reject](./struct.Reject.html) structure. The result type of a contract
//! init or a receive method is assumed to be of the form `Result<_, E>` where
//! `Reject: From<E>`.
//!
//! Producing return values is in case of errors is not yet supported by this
//! library, although smart contract writers can do this manually using the
//! [Write] implementation of the [ExternReturnValue] type.
//!
//! With respect to error **codes**, the intention is that smart contract
//! writers will write their own custom, precise, error types and either
//! manually implement `Reject: From<E>` for their type `E`, or use the [Reject
//! macro](./derive.Reject.html) which supports the common use cases.
//!
//! In addition to the custom errors that signal contract-specific error
//! conditions this library provides some common error cases that most contracts
//! will have to handle and their conversions to [Reject](./struct.Reject.html).
//! These are
//!
//! | Variant | Error code |
//! |---------|------------|
//! | [()][1] | `-2147483647` |
//! | [ParseError] | `-2147483646` |
//! | [LogError::Full] | `-2147483645` |
//! | [LogError::Malformed] | `-2147483644`
//! | [NewContractNameError::MissingInitPrefix] | `-2147483643` |
//! | [NewContractNameError::TooLong] | `-2147483642` |
//! | [NewContractNameError::ContainsDot] | `-2147483639` |
//! | [NewContractNameError::InvalidCharacters] | `-2147483638` |
//! | [NewReceiveNameError::MissingDotSeparator] | `-2147483641` |
//! | [NewReceiveNameError::TooLong] | `-2147483640` |
//! | [NewReceiveNameError::InvalidCharacters] | `-2147483637` |
//! | [NotPayableError] | `-2147483636` |
//! | [TransferError::AmountTooLarge] | `-2147483635` |
//! | [TransferError::MissingAccount] | `-2147483634` |
//! | [CallContractError::AmountTooLarge] | `-2147483633` |
//! | [CallContractError::MissingAccount] | `-2147483632` |
//! | [CallContractError::MissingContract] | `-2147483631` |
//! | [CallContractError::MissingEntrypoint] | `-2147483630` |
//! | [CallContractError::MessageFailed] | `-2147483629` |
//! | [CallContractError::LogicReject] | `-2147483628` |
//! | [CallContractError::Trap] | `-2147483627` |
//! | [UpgradeError::MissingModule] | `-2147483626` |
//! | [UpgradeError::MissingContract] | `-2147483625` |
//! | [UpgradeError::UnsupportedModuleVersion] | `-2147483624` |
//! | [QueryAccountBalanceError] | `-2147483623` |
//! | [QueryContractBalanceError] | `-2147483622` |
//!
//! Other error codes may be added in the future and custom error codes should
//! not use the range `i32::MIN` to `i32::MIN + 100`.
//!
//! # Collections
//!
//! Several collections are available for use in a smart contract and choosing
//! the right one can result in significant cost savings.
//!
//! First off, Rust's own standard library provides [several efficient data structures](https://doc.rust-lang.org/std/collections/)
//! which can be used in a smart contract.
//!
//! However, these can become costly for collections holding a large number of
//! elements, which needs to be persisted in the smart contract state across
//! contract updates.
//! The reason being these data structures are designed to be kept in-memory and
//! persisting them means reading and writing the entire collection to a single
//! entry in the smart contract key-value store on every contract update.
//! This is wasteful when only part of the collection is relevant on each
//! update.
//!
//! In the above mentioned scenarios, it is instead recommended to use one of
//! the smart contract tailored collections, as these partisions the collection
//! into multiple key-value stores, resulting in cheaper read and writes to the
//! state.
//!
//! The collections can be grouped as:
//! - Maps: [`StateMap`], [`StateBTreeMap`]
//! - Sets: [`StateSet`], [`StateBTreeSet`]
//!
//! ## When should you use which collection?
//!
//! This section presents a rough guideline for when to reach for each of the
//! collections.
//!
//! ### Use `StateMap` when:
//!
//! - You want to track which keys you have seen.
//! - Arbitrary values are associated with each of the keys.
//!
//! ### Use `StateBTreeMap` when:
//!
//! - You want to track which keys you have seen.
//! - Arbitrary values are associated with each of the keys.
//! - The keys have some _ordering_ which is relevant e.g. if you need the key
//!   which is located right above/below another key using
//!   [`higher`](StateBTreeMap::higher)/[`lower`](StateBTreeMap::lower).
//!
//! ### Use `StateSet` when:
//!
//! - You want to track which keys you have seen.
//! - There is no meaningful value to associate with your keys.
//!
//! ### Use `StateBTreeSet` when:
//!
//! - You want to track which keys you have seen.
//! - There is no meaningful value to associate with your keys.
//! - The keys have some _ordering_ which is relevant e.g. if you need the key
//!   which is located right above/below another key using
//!   [`higher`](StateBTreeMap::higher)/[`lower`](StateBTreeMap::lower).
//!
//! # Deprecating the `test_infrastructure`
//!
//! Version 8.1 deprecates the [test_infrastructure] in favor of the library
//! [concordium_smart_contract_testing]. A number of traits are also
//! deprecated at the same time since they only exist to support the
//! [test_infrastructure] and are not needed in the new testing library.
//! The primary of these traits are [`HasHost`], [`HasStateApi`],
//! [`HasInitContext`], and [`HasReceiveContext`].
//!
//! ## Migration guide
//! To migrate your contract and its tests to the new testing library, you need
//! to do the following two steps:
//!
//! 1. Replace the usage of deprecated traits with their concrete alternatives
//! and remove generics.
//!
//!    For init methods:
//!    ```no_run
//!    # use concordium_std::*;
//!    #
//!    # type State = ();
//!    #
//!    /// Before
//!    #[init(contract = "contract_before")]
//!    fn init_before<S: HasStateApi>(
//!        ctx: &impl HasInitContext,
//!        state_builder: &mut StateBuilder<S>,
//!    ) -> InitResult<State> { todo!() }
//!
//!    /// After
//!    #[init(contract = "contract_after")]
//!    fn init_after(                        // `<S: HasStateApi>` removed
//!        ctx: &InitContext,                // `impl` and `Has` removed
//!        state_builder: &mut StateBuilder, // `<S>` removed
//!    ) -> InitResult<State> { todo!() }
//!    ```
//!    For receive methods:
//!    ```no_run
//!    # use concordium_std::*;
//!    #
//!    # type State = ();
//!    # type MyReturnValue = ();
//!    #
//!    # #[init(contract = "my_contract")]
//!    # fn contract_init(                    // `<S: HasStateApi>` removed
//!    #    ctx: &InitContext,                // `impl` and `Has` removed
//!    #    state_builder: &mut StateBuilder, // `<S>` removed
//!    # ) -> InitResult<State> { todo!() }
//!    /// Before
//!    #[receive(contract = "my_contract", name = "my_receive")]
//!    fn receive_before<S: HasStateApi>(
//!        ctx: &impl HasReceiveContext,
//!        host: &impl HasHost<State, StateApiType = S>,
//!    ) -> ReceiveResult<MyReturnValue> { todo!() }
//!
//!    /// After
//!    #[receive(contract = "my_contract", name = "my_receive")]
//!    fn receive_after(           // `<S: HasStateApi>` removed
//!        ctx: &ReceiveContext,   // `impl` and `Has` removed
//!        host: &Host<State>,     // `impl Has` and `, StateApiType = S removed
//!    ) -> ReceiveResult<MyReturnValue> { todo!() }
//!    ```
//!
//!    If you use logging, crypto-primitives, or similar, you must also
//! replace those uses of traits with concrete types. E.g. replacing `&mut impl
//! HasLogger` with `&mut Logger`.
//!
//! 2. Migrate your tests to use the new testing library.
//!
//!    For an introduction to the library, see our [guide](https://developer.concordium.software/en/mainnet/smart-contracts/guides/integration-test-contract.html).
//!
//!    If you follow our [recommended structure](https://developer.concordium.software/en/mainnet/smart-contracts/best-practices/development.html#recommended-structure) in your contract,
//!    then you have a mix of unit and integrations tests:
//!    - Unit tests that call methods directly on your state struct (without any
//!      init/receive calls)
//!    - Integration tests that call the init and receive methods
//!
//! If you do not want to migrate your contract and tests yet, then you can add
//! the `#[allow(deprecated)]` attribute to your test modules to avoid the
//! deprecation warnings.
//!
//! [1]: https://doc.rust-lang.org/std/primitive.unit.html
//! [test_infrastructure]: ./test_infrastructure/index.html
//! [concordium_smart_contract_testing]: https://docs.rs/concordium-smart-contract-testing

#![cfg_attr(not(feature = "std"), no_std, feature(core_intrinsics))]

#[cfg(not(feature = "std"))]
pub extern crate alloc;

/// Terminate execution immediately without panicking.
/// When the `std` feature is enabled this is just [std::process::abort](https://doc.rust-lang.org/std/process/fn.abort.html).
/// When `std` is not present and the target architecture is `wasm32` this will
/// simply emit the [unreachable](https://doc.rust-lang.org/core/arch/wasm32/fn.unreachable.html) instruction.
#[cfg(feature = "std")]
pub use std::process::abort as trap;
#[cfg(all(not(feature = "std"), target_arch = "wasm32"))]
#[inline(always)]
pub fn trap() -> ! { core::arch::wasm32::unreachable() }
#[cfg(all(not(feature = "std"), not(target_arch = "wasm32")))]
#[inline(always)]
pub fn trap() -> ! { core::intrinsics::abort() }

#[cfg(not(feature = "std"))]
#[panic_handler]
fn abort_panic(_info: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

// Provide some re-exports to make it easier to use the library.
// This should be expanded in the future.
/// Re-export.
#[cfg(not(feature = "std"))]
pub use alloc::{
    borrow::ToOwned, boxed, boxed::Box, format, rc, string, string::String, string::ToString, vec,
    vec::Vec,
};
/// Re-export.
#[cfg(not(feature = "std"))]
pub use core::{cell, cmp, convert, fmt, hash, hint, iter, marker, mem, num, ops, result::*};
#[cfg(feature = "std")]
pub(crate) use std::vec;

/// Re-export.
#[cfg(feature = "std")]
pub use std::{
    boxed, boxed::Box, cell, cmp, convert, fmt, hash, hint, iter, marker, mem, num, ops, rc,
    string::String, vec::Vec,
};

#[cfg(all(feature = "bump_alloc", target_arch = "wasm32"))]
pub mod bump_alloc;

#[cfg(all(feature = "bump_alloc", target_arch = "wasm32"))]
#[cfg_attr(feature = "bump_alloc", global_allocator)]
static ALLOC: crate::bump_alloc::BumpAllocator = unsafe { crate::bump_alloc::BumpAllocator::new() };

/// Re-export.
pub mod collections {
    #[cfg(not(feature = "std"))]
    use alloc::collections;
    #[cfg(feature = "std")]
    use std::collections;

    pub use collections::*;
    pub use concordium_contracts_common::{HashMap, HashSet};
}

pub mod constants;
mod impls;
pub mod prims;
mod state_btree;
mod traits;
mod types;
pub use concordium_contracts_common::*;
pub use impls::*;
pub use state_btree::*;
pub use traits::*;
pub use types::*;

#[deprecated(
    since = "8.1.0",
    note = "Deprecated in favor of [concordium-smart-contract-testing](https://docs.rs/concordium-smart-contract-testing)."
)]
pub mod test_infrastructure;

#[cfg(all(feature = "debug", not(feature = "std")))]
pub use alloc::format;
#[cfg(all(feature = "debug", feature = "std"))]
pub use std::format;

#[macro_export]
#[cfg(feature = "debug")]
/// When the `debug` feature of `concordium-std` is enabled this will use the
/// `debug_print` host function to emit the provided information. The syntax is
/// the same as that of `println!` macro.
///
/// If the `debug` feature is not enabled the macro generates an empty
/// expression.
macro_rules! concordium_dbg {
    () => {
        {
            $crate::debug_print("", file!(), line!(), column!());
        }
    };
    ($($arg:tt)*) => {
        {
            let msg = $crate::format!($($arg)*);
            $crate::debug_print(&msg, file!(), line!(), column!());
        }
    };
}

#[macro_export]
#[cfg(not(feature = "debug"))]
/// When the `debug` feature of `concordium-std` is enabled this will use the
/// `debug_print` host function to emit the provided information. The syntax is
/// the same as that of `println!` macro.
///
/// If the `debug` feature is not enabled the macro generates an empty
/// expression.
macro_rules! concordium_dbg {
    () => {{}};
    ($($arg:tt)*) => {{}};
}

/// Emit a message in debug mode.
/// Used internally, not meant to be called directly by contract writers,
/// and a contract with this debug print cannot be deployed to the chain.
#[doc(hidden)]
#[cfg(feature = "debug")]
pub fn debug_print(message: &str, filename: &str, line: u32, column: u32) {
    let msg_bytes = message.as_bytes();
    let filename_bytes = filename.as_bytes();
    unsafe {
        crate::prims::debug_print(
            msg_bytes.as_ptr(),
            msg_bytes.len() as u32,
            filename_bytes.as_ptr(),
            filename_bytes.len() as u32,
            line,
            column,
        )
    };
}
