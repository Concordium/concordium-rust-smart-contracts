//! This library provides the core API that can be used to write smart contracts
//! for the Concordium blockchain. It aims to provide safe wrappers around the
//! core primitives exposed by the chain and accessible to smart contracts.
//!
//! The library is meant to be used as a standard library for developing smart
//! contracts. For this reason it re-exports a number of definitions from other
//! libraries.
//!
//! # Global allocator
//! Importing this library has a side-effect of setting  the allocator to [wee_alloc](https://docs.rs/wee_alloc/)
//! which is a memory allocator aimed at small code footprint.
//! This allocator is designed to be used in contexts where there are a few
//! large allocations up-front, and the memory is afterwards used by the program
//! without many further allocations. Frequent small allocations will have bad
//! performance, and should be avoided.
//!
//! In the future it will be possible to opt-out of the global allocator via a
//! feature.
//!
//! # Panic handler
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
//! [`wasm-test`](#wasm-test-build-for-testing-in-wasm), and
//! [`crypto-primitives`][crypto-feature].
//!
//! [crypto-feature]:
//! #crypto-primitives-for-testing-crypto-with-actual-implementations
//!
//! ## `std`: Build with the Rust standard library
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
//! Build with this feature if you want to run smart contract tests with actual
//! (i.e., not mock) implementations of the cryptographic primitives from
//! [`HasCryptoPrimitives`].
//!
//! **WARNING**: It is not possible to build this crate on macOS with the
//! `crypto-primitives` feature when targeting `wasm32-unknown-unknown`.
//! The issue arises when compiling the [`secp256k1`](https://docs.rs/secp256k1/latest/secp256k1/) crate.
//!
//! # Traits
//! To support testing of smart contracts most of the functionality is
//! accessible via traits. This library generally provides two implementations
//! of most traits. The first one is supported by **host** functions, and this
//! is the implementation that is used when contracts are executed by nodes. The
//! second set of implementations supports testing of contracts and it is
//! defined in the [test_infrastructure](./test_infrastructure/index.html)
//! module.
//!
//! - [HasParameter] for accessing the contract parameter
//! - [HasCommonData] for accessing the data that is common to both init and
//!   receive methods
//! - [HasInitContext] for all the context data available to the init functions
//!   (note that this includes all the common data)
//! - [HasReceiveContext] for accessing all the context data available to the
//!   receive functions (note that this includes all the common data)
//! - [HasLogger] for logging data during smart contract execution
//! - [HasPolicy] for accessing the policy of the sender, either of the init or
//!   receive method
//! - [HasStateApi] for operations possible on the contract state
//! - [HasHost] for invoking operations on the host and accessing the state
//! - [HasCryptoPrimitives] for using cryptographic primitives such as hashing
//!   and signature verification.
//!
//! # Signalling errors
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
//!
//! [1]: https://doc.rust-lang.org/std/primitive.unit.html
//! Other error codes may be added in the future and custom error codes should
//! not use the range `i32::MIN` to `i32::MIN + 100`.
#![cfg_attr(not(feature = "std"), no_std, feature(alloc_error_handler, core_intrinsics))]

#[cfg(not(feature = "std"))]
pub extern crate alloc;

#[cfg(not(feature = "std"))]
#[alloc_error_handler]
fn on_oom(_layout: alloc::alloc::Layout) -> ! {
    #[cfg(target_arch = "wasm32")]
    unsafe {
        core::arch::wasm32::unreachable()
    }
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

/// Terminate execution immediately without panicking.
/// When the `std` feature is enabled this is just [std::process::abort](https://doc.rust-lang.org/std/process/fn.abort.html).
/// When `std` is not present and the target architecture is `wasm32` this will
/// simply emit the [unreachable](https://doc.rust-lang.org/core/arch/wasm32/fn.unreachable.html) instruction.
#[cfg(feature = "std")]
pub use std::process::abort as trap;
#[cfg(all(not(feature = "std"), target_arch = "wasm32"))]
#[inline(always)]
pub fn trap() -> ! { unsafe { core::arch::wasm32::unreachable() } }
#[cfg(all(not(feature = "std"), not(target_arch = "wasm32")))]
#[inline(always)]
pub fn trap() -> ! { core::intrinsics::abort() }

#[cfg(not(feature = "std"))]
#[panic_handler]
fn abort_panic(_info: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    unsafe {
        core::arch::wasm32::unreachable()
    }
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

// Provide some re-exports to make it easier to use the library.
// This should be expanded in the future.
/// Re-export.
#[cfg(not(feature = "std"))]
pub use alloc::{
    borrow::ToOwned, boxed, boxed::Box, rc, string, string::String, string::ToString, vec, vec::Vec,
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
mod traits;
mod types;
pub use concordium_contracts_common::*;
pub use concordium_std_derive::*;
pub use impls::*;
pub use traits::*;
pub use types::*;

extern crate wee_alloc;
// Use `wee_alloc` as the global allocator to reduce code size.
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

pub mod test_infrastructure;
