//! Ensure `concordium_dbg` generates compilable code.
use concordium_std::*;

fn f() {
    let one: u32 = 3;
    let two: Option<u32> = Some(3);
    concordium_dbg!("Hello {one:?}, {}", two.unwrap());
    concordium_dbg!("Hello {one:?}, {}", two.unwrap(),);
    concordium_dbg!();
}

fn main() {}
