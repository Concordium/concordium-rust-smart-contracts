//! A contract with entrypoints that exercise and test the bump allocator from
//! `concordium_std`. It does not have any value as a real contract.
//!
//! Some of the tests use the function [`black_box`] to ensure that
//! the Rust compiler doesn't optimize some of the important calls away, thereby
//! altering the test. Some of the tests fail if the black boxes are removed,
//! other's simply do not work as intended, which is only visible by logs from
//! the allocator.
#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::{collections::BTreeMap, hint::black_box, *};

type State = ();

#[init(contract = "bump_alloc_tests")]
fn contract_init(_ctx: &InitContext, _state_builder: &mut StateBuilder) -> InitResult<State> {
    Ok(())
}

/// Tests that the allocator correctly handles data structure such as a map
/// and references to that data. Takes as input a map<u64, u64>,
/// two keys, and the expected sum of corresponding values in the map.
#[receive(contract = "bump_alloc_tests", name = "memory_layout")]
fn memory_layout(ctx: &ReceiveContext, _host: &Host<State>) -> ReceiveResult<()> {
    let (map, key_1, key_2, expected_sum): (BTreeMap<u64, u64>, u64, u64, u64) =
        ctx.parameter_cursor().get()?;
    // Use a helper method to check that the references etc. also work as expected.
    // Uses black_box to ensure that it isn't inlined.
    let actual_sum = black_box(lookup_and_sum(&map, key_1, key_2));
    if expected_sum != actual_sum {
        return Err(Reject::default());
    }
    Ok(())
}

/// Helpers method for `memory_layout`, which looks up two values from a
/// map and adds them. Panics if the values aren't present.
fn lookup_and_sum(map: &BTreeMap<u64, u64>, key_1: u64, key_2: u64) -> u64 {
    let v1 = map.get(&key_1).unwrap();
    let v2 = map.get(&key_2).unwrap();
    v1 + v2
}

/// Tests that allocating an input parameter of maximum size (64KiB) works.
#[receive(contract = "bump_alloc_tests", name = "max_parameter_len")]
fn max_parameter_len(ctx: &ReceiveContext, _host: &Host<State>) -> ReceiveResult<()> {
    let param: [u8; 65535] = ctx.parameter_cursor().get()?;
    let boxed_param = Box::new(param);
    if boxed_param[0] != boxed_param[65534] {
        return Err(Reject::default());
    }
    Ok(())
}

/// Test that allocating one megabyte works correctly.
/// Uses [`black_box`] to ensure that the allocation actually occurs,
/// instead of being optimized away by the compiler.
#[receive(contract = "bump_alloc_tests", name = "allocate_one_mib")]
fn allocate_one_mib(_ctx: &ReceiveContext, _host: &Host<State>) -> ReceiveResult<()> {
    let b = black_box(Box::new([1u8; 1_024_000]));
    if b[0] != b[1_023_999] {
        return Err(Reject::default());
    }
    Ok(())
}

/// Tests the optimization in the bump allocator that reuses the last
/// memory chunk handed out in certain cases.
///
/// The test starts by allocating a single chunk of memory which is deallocated
/// at the end of the test. This is to ensure that the allocator doesn't reset
/// the `next` pointer to `heap_base` due to `allocations` being 0. As this
/// would be testing a different scenario.
///
/// Then it loops `n` times, where it allocates a vector `a`, deallocates it,
/// then allocates a vector `b` and deallocates it. Due to the optimization in
/// the allocator, the pointer addresses of `a` and `b` should be identical, as
/// the chunk memory for `a` should be reused for `b`.
#[receive(contract = "bump_alloc_tests", name = "dealloc_last_optimization")]
fn dealloc_last_optimization(ctx: &ReceiveContext, _host: &Host<State>) -> ReceiveResult<()> {
    let n: u64 = ctx.parameter_cursor().get()?;
    let mut long_lasting = black_box(Box::new(0u64));
    for i in 0..n {
        let addr_a = {
            let a = black_box(vec![i]);
            a.as_ptr() as usize
        };
        let addr_b = {
            let b = black_box(vec![i, i]);
            b.as_ptr() as usize
        };
        if addr_a != addr_b {
            *long_lasting += 1;
        }
    }
    if *long_lasting != 0 {
        return Err(Reject::default());
    }
    Ok(())
}
