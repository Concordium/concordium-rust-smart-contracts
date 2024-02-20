extern crate proc_macro;

use concordium_contracts_common::{
    AccountAddress, ContractAddress, ModuleReference, PublicKeyEcdsaSecp256k1, PublicKeyEd25519,
    SignatureEcdsaSecp256k1, SignatureEd25519,
};
use proc_macro::TokenStream;
use std::str::FromStr;
use syn::{parse_macro_input, LitStr};

/// Procedural macro for instantiating account addresses.
/// Input must be a valid base58-encoding.
#[proc_macro]
pub fn account_address(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    let str = input.value();

    let addr_bytes = match AccountAddress::from_str(&str) {
        Ok(addr) => addr.0,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("Invalid account address: {}", e));
            return err.to_compile_error().into();
        }
    };

    match format!("AccountAddress({:?})", addr_bytes).parse() {
        Ok(o) => o,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("LexError: {}", e));
            err.to_compile_error().into()
        }
    }
}

/// Procedural macro for instantiating `PublicKeyEcdsaSecp256k1` public keys.
/// Input must be a (case-insensitive) hex-encoding and have a length of 64
/// characters representing 32 bytes.
#[proc_macro]
pub fn public_key_ed25519(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    let str = input.value();

    let pk_bytes = match PublicKeyEd25519::from_str(&str) {
        Ok(pk) => pk.0,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("Invalid Ed25519 public key: {}", e));
            return err.to_compile_error().into();
        }
    };

    match format!("PublicKeyEd25519({:?})", pk_bytes).parse() {
        Ok(o) => o,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("LexError: {}", e));
            err.to_compile_error().into()
        }
    }
}

/// Procedural macro for instantiating `PublicKeyEcdsaSecp256k1` public keys.
/// Input must be a (case-insensitive) hex-encoding and have a length of 66
/// characters representing 33 bytes.
#[proc_macro]
pub fn public_key_ecdsa(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    let str = input.value();

    let pk_bytes = match PublicKeyEcdsaSecp256k1::from_str(&str) {
        Ok(pk) => pk.0,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("Invalid ECDSA public key: {}", e));
            return err.to_compile_error().into();
        }
    };

    match format!("PublicKeyEcdsaSecp256k1({:?})", pk_bytes).parse() {
        Ok(o) => o,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("LexError: {}", e));
            err.to_compile_error().into()
        }
    }
}

/// Procedural macro for instantiating `SignatureEd25519` signatures.
/// Input must be a (case-insensitive) hex-encoding and have a length of 128
/// characters representing 64 bytes.
#[proc_macro]
pub fn signature_ed25519(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    let str = input.value();

    let sig_bytes = match SignatureEd25519::from_str(&str) {
        Ok(sig) => sig.0,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("Invalid Ed25519 signature: {}", e));
            return err.to_compile_error().into();
        }
    };

    match format!("SignatureEd25519({:?})", sig_bytes).parse() {
        Ok(o) => o,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("LexError: {}", e));
            err.to_compile_error().into()
        }
    }
}

/// Procedural macro for instantiating `SignatureEcdsaSecp256k1` signatures.
/// Input must be a (case-insensitive) hex-encoding and have a length of 128
/// characters representing 64 bytes.
#[proc_macro]
pub fn signature_ecdsa(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    let str = input.value();

    let sig_bytes = match SignatureEcdsaSecp256k1::from_str(&str) {
        Ok(sig) => sig.0,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("Invalid ECDSA signature: {}", e));
            return err.to_compile_error().into();
        }
    };

    match format!("SignatureEcdsaSecp256k1({:?})", sig_bytes).parse() {
        Ok(o) => o,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("LexError: {}", e));
            err.to_compile_error().into()
        }
    }
}

/// Procedural macro for instantiating contract addresses.
/// Input must be of the form "<index,subindex>", where index and subindex
/// are integers.
#[proc_macro]
pub fn contract_address(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    let str = input.value();

    let contract = match ContractAddress::from_str(&str) {
        Ok(con) => con,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("Invalid contract address: {}", e));
            return err.to_compile_error().into();
        }
    };

    match format!(
        "ContractAddress {{ index: {:?}, subindex: {:?} }}",
        contract.index, contract.subindex
    )
    .parse()
    {
        Ok(o) => o,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("LexError: {}", e));
            err.to_compile_error().into()
        }
    }
}

/// Procedural macro for instantiating module references.
/// Input must be a (case-insensitive) hex-encoding and have a length of 64
/// characters representing 32 bytes.
#[proc_macro]
pub fn module_reference(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    let str = input.value();

    let module_ref = match ModuleReference::from_str(&str) {
        Ok(mod_ref) => mod_ref.bytes,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("Invalid module reference: {}", e));
            return err.to_compile_error().into();
        }
    };

    match format!("ModuleReference::new({:?})", module_ref).parse() {
        Ok(o) => o,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("LexError: {}", e));
            err.to_compile_error().into()
        }
    }
}
