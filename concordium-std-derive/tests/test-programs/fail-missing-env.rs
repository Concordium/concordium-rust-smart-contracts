//! Ensure that the macros generate compilable code.

use concordium_contracts_common::*;
use concordium_std_derive::*;

const ACC: AccountAddress = account_address_env!("TEST");

fn f() {
    println!("{:?}", ACC.to_string());
}

fn main() {}
