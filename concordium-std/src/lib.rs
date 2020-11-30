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
//! [dependencies.concordium-sc-base]
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
//! large allocations up-front, and the memory later used during the lifetime of
//! the program. Frequent small allocations will have bad performance, and
//! should be avoided.
//!
//! # Panic handler
//! When compiled without the `std` feature this crate sets the panic handler
//! to a no-op.

#![cfg_attr(not(feature = "std"), no_std, feature(alloc_error_handler))]

#[cfg(not(feature = "std"))]
extern crate alloc;

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

/// Abort execution immediately.
#[cfg(feature = "std")]
pub use std::process::abort as trap;
#[cfg(all(not(feature = "std"), target_arch = "wasm32"))]
#[inline(always)]
pub fn trap() -> ! { unsafe { core::arch::wasm32::unreachable() } }

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
#[cfg(not(feature = "std"))]
pub use core::result::*;

/// Re-export.
#[cfg(not(feature = "std"))]
pub use alloc::collections;
/// Re-export.
#[cfg(not(feature = "std"))]
pub use alloc::{string, string::String, string::ToString, vec, vec::Vec};
/// Re-export.
#[cfg(not(feature = "std"))]
pub use core::convert;
/// Re-export.
#[cfg(not(feature = "std"))]
pub use core::mem;

/// Re-export.
#[cfg(feature = "std")]
pub use std::collections;
/// Re-export.
#[cfg(feature = "std")]
pub use std::convert;
/// Re-export.
#[cfg(feature = "std")]
pub use std::mem;

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
