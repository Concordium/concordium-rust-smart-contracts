extern crate proc_macro;

use std::str::FromStr;
use concordium_contracts_common::AccountAddress;
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, LitStr};

#[proc_macro]
pub fn account_address(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr).value();

    let address = match AccountAddress::from_str(&input) {
        Ok(addr) => addr.0,
        Err(e) => { 
            let x = format!("Invalid account address: {}", e); 
            return quote! { compile_error!(#x) }.into() 
        },
    };

    println!("{:?}", address);
    format!("AccountAddress({:?})", address).parse().unwrap()
}
