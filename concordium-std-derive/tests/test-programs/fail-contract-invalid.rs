//! Ensure that the macros generate compilable code.

use concordium_contracts_common::*;
use concordium_std_derive::*;

const CONTRACT: ContractAddress = contract_address!("<0, 0>");

fn f() {
    println!("{:?}", CONTRACT.to_string());
}

fn main() {}
