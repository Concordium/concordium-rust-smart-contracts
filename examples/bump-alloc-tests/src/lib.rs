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
    let mut long_lived = black_box(Box::new(0u64));
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
            *long_lived += 1;
        }
    }
    if *long_lived != 0 {
        return Err(Reject::default());
    }
    Ok(())
}

/// Tests that the allocator does not overwrite the static and stack regions of
/// the memory.
///
/// The general idea is to create static and local variables, perform some
/// recursive calls and subsequently check the integrity of all the data.
/// The details are in written in the internal comments and in the documentation
/// for the recursive helper function `appender`.
#[receive(contract = "bump_alloc_tests", name = "stack_and_static")]
fn stack_and_static(ctx: &ReceiveContext, _host: &Host<State>) -> ReceiveResult<()> {
    // Create a static variable and some local variables.
    static ON_ODD: &str = "ODD";
    let (mut text, n, on_even): (String, u32, String) = ctx.parameter_cursor().get()?;
    let original_n = n;
    let original_text_len = text.len();
    // Allocate a long lived box on the heap.
    let long_lived: Box<Vec<u32>> = black_box(Box::new((0..n).collect()));
    // Run the appender function.
    appender(&mut text, n, &on_even, ON_ODD);
    // Use some of the local variables defined before the recursive call.
    // Abort if `n` should have been altered.
    if original_n != n {
        return Err(Reject::default());
    }
    // Abort if the text length hasn't increased when `n` is positive.
    if n != 0 && original_text_len == text.len() {
        return Err(Reject::default());
    }
    let n_usize = n as usize;
    // Use the box to ensure that it is long lived.
    if long_lived[n_usize - 100] != n - 100 {
        return Err(Reject::default());
    }
    // Calculate the expected length of the `text` and check it.
    let expected_len = original_text_len
        + (ON_ODD.len() * (n_usize / 2)) // Append `ON_ODD` half the times.
        + (on_even.len() * (n_usize / 2)) // Append `on_even` half the times.
        + (ON_ODD.len() * (n_usize % 2)); // Append an extra `ON_ODD` if `n` is odd.
    if expected_len != text.len() {
        return Err(Reject::default());
    }
    Ok(())
}

/// Recursively alternates between appending `on_even` and `on_odd` to the
/// `text` `n` times.
///
/// For example with ("ORIGINAL", 3, "EVEN", "ODD"), the final `text` becomes:
///
///         |  |   |
/// ORIGINALODDEVENODD
///         |  |   |
fn appender(text: &mut String, n: u32, on_even: &str, on_odd: &str) {
    if n == 0 {
        return;
    }
    let is_even = n.is_multiple_of(2);
    if is_even {
        text.push_str(on_even);
    } else {
        text.push_str(on_odd);
    }
    appender(text, n - 1, on_even, on_odd);
}
