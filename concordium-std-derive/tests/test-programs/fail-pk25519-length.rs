//! Ensure that the macros generate compilable code.

use concordium_contracts_common::*;
use concordium_std_derive::*;

const PK_25519: PublicKeyEd25519 = public_key_ed25519!("012a7e286063ae5dfcebce40636c0546d367d8c65cd4cb69aae1af77a4d6141201");

fn f() {
    println!("{:?}", PK_25519.to_string());
}

fn main() {}
