//! This library provides the core API that can be used to write smart contracts
//! for the Concordium blockchain. It aims to provide safe wrappers around the
//! core primitives exposed by the chain and accessible to smart contracts.
//!
//! By default the library will be linked with the
//! [std](https://doc.rust-lang.org/std/) crate, the rust standard library,
//! however to minimize code size this library supports toggling compilation
//! with the `#![no_std]` attribute via the feature `std` which is enabled by
//! default. Compilation without the `std` feature requires a nightly version of
//! rust.
//!
//! To use this library without the `std` feature you have to disable it, which
//! can be done, for example, as follows.
//! ```
//! [dependencies.concordium-std]
//! default-features = false
//! ```
//! In your project's `Cargo.toml` file.
//!
//! The library is meant to be used as a standard library for developing smart
//! contracts. For this reason it re-exports a number of definitions from other
//! libraries.
//!
//! # Global allocator.
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
//! # Build for generating a module schema
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
//! # Build for testing in Wasm
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
//! # Traits
//! Most of the functionality for interacting with the host is abstracted away
//! by the traits
//! - [HasParameter](./trait.HasParameter.html) for accessing the contract
//!   parameter
//! - [HasCommonData](./trait.HasCommonData.html) for accessing the data that is
//!   common to both init and receive methods
//! - [HasInitContext](./trait.HasInitContext.html) for all the context data
//!   available to the init functions (note that this includes all the common
//!   data)
//! - [HasReceiveContext](./trait.HasReceiveContext.html) for accessing all the
//!   context data available to the receive functions (note that this includes
//!   all the common data)
//! - [HasLogger](./trait.HasLogger.html) for logging data during smart contract
//!   execution
//! - [HasPolicy](./trait.HasPolicy.html) for accessing the policy of the
//!   sender, either of the init or receive method
//! - [HasContractState](./trait.HasContractState.html) for operations possible
//!   on the contract state.
//!
//! These are provided by traits to make testing easier. There are two main
//! implementations provided for these traits. One provided by so-called
//! __host__ functions, which is the implementation that is used by Concordium
//! nodes when contracts are executed on the chain, or when tested via
//! `cargo-concordium`.
//!
//! The second implementation is on types in the
//! [test_infrastructure](./test_infrastructure/index.html) module, and is
//! intended to be used for unit-testing together with the `concordium_test`
//! infrastructure.
//!
//! # Signalling errors
//! On the Wasm level Contracts can signal errors by returning a negative i32
//! value as a result of either initialization or invocation of the receive
//! method. To make error handling more pleasant we provide the
//! [Reject](./struct.Reject.html) structure. The result type of a contract init
//! or a receive method is assumed to be of the form `Result<_, E>` where
//! `Reject: From<E>`.
//!
//! The intention is that smart contract writers will write their own custom,
//! precise, error types and either manually implement `Reject: From<E>` for
//! their type `E`, or use the [Reject macro](./derive.Reject.html) which
//! supports the common use cases.
//!
//! In addition to the custom errors that signal contract-specific error
//! conditions this library provides some common error cases that most contracts
//! will have to handle and their conversions to [Reject](./struct.Reject.html).
//! These are
//!
//! | Variant | Error code |
//! |---------|------------|
//! | [()][1] | `-2147483647` |
//! | [ParseError][2] | `-2147483646` |
//! | [LogError::Full][3] | `-2147483645` |
//! | [LogError::Malformed][4] | `-2147483644`
//! | [NewContractNameError::MissingInitPrefix][5] | `-2147483643` |
//! | [NewContractNameError::TooLong][6] | `-2147483642` |
//! | [NewContractNameError::ContainsDot][7] | `-2147483639` |
//! | [NewContractNameError::InvalidCharacters][8] | `-2147483638` |
//! | [NewReceiveNameError::MissingDotSeparator][9] | `-2147483641` |
//! | [NewReceiveNameError::TooLong][10] | `-2147483640` |
//! | [NewReceiveNameError::InvalidCharacters][11] | `-2147483637` |
//! | [NotPayableError][12] | `-2147483636` |
//!
//! [MIN]: https://doc.rust-lang.org/std/primitive.i32.html#associatedconstant.MIN
//! [1]: https://doc.rust-lang.org/std/primitive.unit.html
//! [2]: ./struct.ParseError.html
//! [3]: ./enum.LogError.html#variant.Full
//! [4]: ./enum.LogError.html#variant.Malformed
//! [5]: ./enum.LogError.html#variant.Malformed
//! [6]: ./enum.NewContractNameError.html#variant.TooLong
//! [7]: ./enum.NewContractNameError.html#variant.ContainsDot
//! [8]: ./enum.NewContractNameError.html#variant.InvalidCharacters
//! [9]: ./enum.NewReceiveNameError.html#variant.MissingDotSeparator
//! [10]: ./enum.NewReceiveNameError.html#variant.TooLong
//! [11]: ./enum.NewReceiveNameError.html#variant.InvalidCharacters
//! [12]: ./struct.NotPayableError.html
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
    borrow::ToOwned, boxed::Box, string, string::String, string::ToString, vec, vec::Vec,
};
/// Re-export.
#[cfg(not(feature = "std"))]
pub use core::{convert, hash, marker, mem, num, result::*};
#[cfg(feature = "std")]
pub(crate) use std::vec;

/// Re-export.
#[cfg(feature = "std")]
pub use std::{convert, hash, marker, mem, num, string::String, vec::Vec};

pub mod collections {
    #[cfg(not(feature = "std"))]
    use alloc::collections;
    #[cfg(feature = "std")]
    use std::collections;

    pub use collections::*;
    pub use concordium_contracts_common::{HashMap, HashSet};
}

/// Chain constants that impose limits on various aspects of smart contract
/// execution.
pub mod constants;
mod impls;
mod prims;
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
