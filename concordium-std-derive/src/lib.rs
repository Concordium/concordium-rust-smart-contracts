#![feature(proc_macro_quote)]

extern crate proc_macro;

use concordium_contracts_common::{
    AccountAddress, ContractAddress, ModuleReference, PublicKeyEcdsaSecp256k1, PublicKeyEd25519,
    SignatureEcdsaSecp256k1, SignatureEd25519,
};
use proc_macro::TokenStream;
use proc_macro2::{Group, Punct, Spacing, Span};
use std::str::FromStr;
use syn::{parse_macro_input, LitStr};
use quote::ToTokens;
use quote::quote;

// Tokenizes a slice of bytes
fn tokenize_slice(slice: &[u8]) -> proc_macro2::TokenStream {
    let mut t = proc_macro2::TokenStream::new();
    for byte in slice {
        byte.to_tokens(&mut t);
        Punct::new(',', Spacing::Alone).to_tokens(&mut t);
    }
    Group::new(proc_macro2::Delimiter::Bracket, t).to_token_stream()
}

fn account_address_helper(str: String, span: Span) -> TokenStream {
    let address = match AccountAddress::from_str(&str) {
        Ok(addr) => tokenize_slice(&addr.0),
        Err(e) => {
            let err = syn::Error::new(span, format!("Invalid account address: {}", e));
            return err.to_compile_error().into();
        }
    };

    quote!(AccountAddress(#address)).into()
}

/// Procedural macro for instantiating account addresses.
/// Input must be a valid base58-encoding.
#[proc_macro]
pub fn account_address(item: TokenStream) -> TokenStream {
    let input = match syn::parse::<LitStr>(item) {
        Ok(string_literal) => string_literal,
        Err(e) => {
            // TODO: What if there is another kind of error here?
            let err = syn::Error::new(e.span(), format!("{}: expected a string literal", e));
            return err.to_compile_error().into();
        }
    };

    account_address_helper(input.value(), input.span())
}

/// Procedural macro for instantiating account addresses from an environment
/// variable. Input must be the key of an environment variable whose value is
/// set to a valid base58-encoding of an account address.
#[proc_macro]
pub fn account_address_env(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    let key = input.value();

    let val = match std::env::var(key) {
        Ok(value) => value,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("Environment variable error: {:?}", e));
            return err.to_compile_error().into();
        }
    };

    // TODO: Which is better?
    //account_address_helper(val, input.span())
    account_address(val.into_token_stream().into())
}

fn public_key_ed25519_helper(str: String, span: Span) -> TokenStream {
    let public_key = match PublicKeyEd25519::from_str(&str) {
        Ok(pk) => tokenize_slice(&pk.0),
        Err(e) => {
            let err = syn::Error::new(span, format!("Invalid Ed25519 public key: {}", e));
            return err.to_compile_error().into();
        }
    };

    quote!(PublicKeyEd25519(#public_key)).into()
}

/// Procedural macro for instantiating `PublicKeyEd25519` public keys.
/// Input must be a (case-insensitive) hex-encoding and have a length of 64
/// characters representing 32 bytes.
#[proc_macro]
pub fn public_key_ed25519(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    public_key_ed25519_helper(input.value(), input.span())
}

/// Procedural macro for instantiating `PublicKeyEd25519` public keys from
/// an environment variable. Input must be the key of an environment variable
/// whose value is set to a hex-encoded public key which must have a length of
/// 64 characters representing 32 bytes.
#[proc_macro]
pub fn public_key_ed25519_env(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    let key = input.value();

    let val = match std::env::var(key) {
        Ok(value) => value,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("Environment variable error: {:?}", e));
            return err.to_compile_error().into();
        }
    };

    public_key_ed25519_helper(val, input.span())
}

fn public_key_ecdsa_helper(str: String, span: Span) -> TokenStream {
    let public_key = match PublicKeyEcdsaSecp256k1::from_str(&str) {
        Ok(pk) => tokenize_slice(&pk.0),
        Err(e) => {
            let err = syn::Error::new(span, format!("Invalid ECDSA public key: {}", e));
            return err.to_compile_error().into();
        }
    };

    quote!(PublicKeyEcdsaSecp256k1(#public_key)).into()
}

/// Procedural macro for instantiating `PublicKeyEcdsaSecp256k1` public keys.
/// Input must be a (case-insensitive) hex-encoding and have a length of 66
/// characters representing 33 bytes.
#[proc_macro]
pub fn public_key_ecdsa(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    public_key_ecdsa_helper(input.value(), input.span())
}

/// Procedural macro for instantiating `PublicKeyEcdsaSecp256k1` public keys
/// from an environment variable. Input must be the key of an environment
/// variable whose value is set to a hex-encoded public key which must have a
/// length of 66 characters representing 33 bytes.
#[proc_macro]
pub fn public_key_ecdsa_env(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    let key = input.value();

    let val = match std::env::var(key) {
        Ok(value) => value,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("Environment variable error: {:?}", e));
            return err.to_compile_error().into();
        }
    };

    public_key_ecdsa_helper(val, input.span())
}

fn signature_ed25519_helper(str: String, span: Span) -> TokenStream {
    let signature = match SignatureEd25519::from_str(&str) {
        Ok(sig) => tokenize_slice(&sig.0),
        Err(e) => {
            let err = syn::Error::new(span, format!("Invalid Ed25519 signature: {}", e));
            return err.to_compile_error().into();
        }
    };

    quote!(SignatureEd25519(#signature)).into()
}

/// Procedural macro for instantiating `SignatureEd25519` signatures.
/// Input must be a (case-insensitive) hex-encoding and have a length of 128
/// characters representing 64 bytes.
#[proc_macro]
pub fn signature_ed25519(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    signature_ed25519_helper(input.value(), input.span())
}

/// Procedural macro for instantiating `SignatureEd25519` signatures from
/// an environment variable. Input must be the key of an environment variable
/// whose value is set to a hex-encoded signature which must have a length of
/// 128 characters representing 64 bytes.
#[proc_macro]
pub fn signature_ed25519_env(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    let key = input.value();

    let val = match std::env::var(key) {
        Ok(value) => value,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("Environment variable error: {:?}", e));
            return err.to_compile_error().into();
        }
    };

    signature_ed25519_helper(val, input.span())
}

fn signature_ecdsa_helper(str: String, span: Span) -> TokenStream {
    let signature = match SignatureEcdsaSecp256k1::from_str(&str) {
        Ok(sig) => tokenize_slice(&sig.0),
        Err(e) => {
            let err = syn::Error::new(span, format!("Invalid ECDSA signature: {}", e));
            return err.to_compile_error().into();
        }
    };

    quote!(SignatureEcdsaSecp256k1(#signature)).into()
}

/// Procedural macro for instantiating `SignatureEcdsaSecp256k1` signatures.
/// Input must be a (case-insensitive) hex-encoding and have a length of 128
/// characters representing 64 bytes.
#[proc_macro]
pub fn signature_ecdsa(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    signature_ecdsa_helper(input.value(), input.span())
}

/// Procedural macro for instantiating `SignatureEcdsaSecp256k1` signatures from
/// an environment variable. Input must be the key of an environment variable
/// whose value is set to a hex-encoded signature which must have a length of
/// 128 characters representing 64 bytes.
#[proc_macro]
pub fn signature_ecdsa_env(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    let key = input.value();

    let val = match std::env::var(key) {
        Ok(value) => value,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("Environment variable error: {:?}", e));
            return err.to_compile_error().into();
        }
    };

    signature_ecdsa_helper(val, input.span())
}

fn contract_address_helper(str: String, span: Span) -> TokenStream {
    let (index, subindex) = match ContractAddress::from_str(&str) {
        Ok(con) => (con.index, con.subindex),
        Err(e) => {
            let err = syn::Error::new(span, format!("Invalid contract address: {}", e));
            return err.to_compile_error().into();
        }
    };

    quote!(ContractAddress(#index, #subindex)).into()
}

/// Procedural macro for instantiating contract addresses.
/// Input must be of the form "<index,subindex>", where index and subindex
/// are integers.
#[proc_macro]
pub fn contract_address(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    contract_address_helper(input.value(), input.span())
}

/// Procedural macro for instantiating contract addresses from an environment
/// variable. Input must be the key of an environment variable whose value is
/// set to a contract address of the form "<index,subindex>", where index and
/// subindex are integers
#[proc_macro]
pub fn contract_address_env(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    let key = input.value();

    let val = match std::env::var(key) {
        Ok(value) => value,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("Environment variable error: {:?}", e));
            return err.to_compile_error().into();
        }
    };

    contract_address_helper(val, input.span())
}

fn module_reference_helper(str: String, span: Span) -> TokenStream {
    let module_ref = match ModuleReference::from_str(&str) {
        Ok(mod_ref) => tokenize_slice(&mod_ref.bytes),
        Err(e) => {
            let err = syn::Error::new(span, format!("Invalid module reference: {}", e));
            return err.to_compile_error().into();
        }
    };

    quote!(ModuleReference(#module_ref)).into()
}

/// Procedural macro for instantiating module references.
/// Input must be a (case-insensitive) hex-encoding and have a length of 64
/// characters representing 32 bytes.
#[proc_macro]
pub fn module_reference(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    module_reference_helper(input.value(), input.span())
}

/// Procedural macro for instantiating module references from an environment
/// variable. Input must be the key of an environment variable whose value is set
/// to a hex-encoded module reference which must have a length of 64 characters
/// representing 32 bytes.
#[proc_macro]
pub fn module_reference_env(item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as LitStr);
    let key = input.value();

    let val = match std::env::var(key) {
        Ok(value) => value,
        Err(e) => {
            let err = syn::Error::new(input.span(), format!("Environment variable error: {:?}", e));
            return err.to_compile_error().into();
        }
    };

    module_reference_helper(val, input.span())
}
