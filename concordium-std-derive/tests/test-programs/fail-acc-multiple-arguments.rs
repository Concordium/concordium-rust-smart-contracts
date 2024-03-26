 //! Ensure that the macros generate compilable code.

use concordium_contracts_common::*;
use concordium_std_derive::*;

const ACC: AccountAddress = account_address!("3kBx2h5Y2veb4hZgAJWPrr8RyQESKm5TjzF3ti1QQ4VSYLwK1G", "3kBx2h5Y2veb4hZgAJWPrr8RyQESKm5TjzF3ti1QQ4VSYLwK1G");

fn f() {
    println!("{:?}", ACC.to_string());
}

fn main() {}
