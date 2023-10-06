//! This test checks that you cannot have multiple `StateRefMut` from a
//! `StateMap` alive at the same time.
//!
//! When compiling it, the borrow-checker is supposed to throw an error.
use concordium_std::*;

pub fn main() {
    let mut state_builder = StateBuilder::open(ExternStateApi::open());
    let mut map: StateMap<u8, u8, _> = state_builder.new_map();
    map.insert(0, 1);
    map.insert(1, 2);
    // Get two mutable references and unwrap the options.
    let e1 = map.get_mut(&0u8).unwrap();
    let e2 = map.get_mut(&1u8).unwrap();
    // Use them, so we are certain that their lifetimes overlap.
    assert_eq!(*e1, *e2);
}
