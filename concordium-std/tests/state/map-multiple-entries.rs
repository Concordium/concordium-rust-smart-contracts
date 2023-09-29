//! This test checks that you cannot have multiple entries from a `StateMap`
//! alive at the same time.
//!
//! When compiling it, the borrow-checker is supposed to throw an error.
use concordium_std::*;

pub fn main() {
    let mut state_builder = StateBuilder::open(ExternStateApi::open());
    let mut map: StateMap<u8, u8, _> = state_builder.new_map();
    // Get two entries.
    let e1 = map.entry(0u8);
    let e2 = map.entry(1u8);
    // Use them, so we are certain that their lifetimes overlap.
    e1.or_insert(1);
    e2.or_insert(2);
}
