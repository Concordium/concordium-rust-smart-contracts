extern crate proc_macro;

use std::str::FromStr;
use concordium_rust_sdk::smart_contracts::common::AccountAddress;
use proc_macro::TokenStream;
use quote::quote;
use quote::ToTokens;
use syn::{parse_macro_input, LitStr};

#[proc_macro]
pub fn account_address(item: TokenStream) -> TokenStream {
    // Parse the input tokens into a string literal
    let input = parse_macro_input!(item as LitStr).value();

    let address = match AccountAddress::from_str(&input) {
        Ok(addr) => addr,
        Err(e) => panic!("lol")
    };

    // Generate the Rust code to print the uppercase string
    let expanded = quote! {
        {
            #address
        }
    };

    // Convert the generated code back into a TokenStream
    TokenStream::from(expanded)
}
