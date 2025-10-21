extern crate proc_macro;

use concordium_contracts_common::{
    AccountAddress, ContractAddress, ModuleReference, PublicKeyEcdsaSecp256k1, PublicKeyEd25519,
    SignatureEcdsaSecp256k1, SignatureEd25519,
};
use proc_macro::TokenStream;
use proc_macro2::{Group, Punct, Spacing, Span};
use quote::{quote, ToTokens};
use std::str::FromStr;
use syn::LitStr;

// Helper functions:

// Tokenizes a slice of bytes.
fn tokenize_slice(slice: &[u8]) -> proc_macro2::TokenStream {
    let mut t = proc_macro2::TokenStream::new();
    for byte in slice {
        byte.to_tokens(&mut t);
        Punct::new(',', Spacing::Alone).to_tokens(&mut t);
    }
    Group::new(proc_macro2::Delimiter::Bracket, t).to_token_stream()
}

// Parses the input tokens of a proc macro and returns the given error
// message on parse error.
fn parse_input(item: TokenStream, msg: &str) -> syn::Result<LitStr> {
    match syn::parse::<LitStr>(item) {
        Ok(string_literal) => Ok(string_literal),
        Err(_) => Err(syn::Error::new(Span::call_site(), msg)),
    }
}

// Parses the given tokens and transforms them using the provided worker
// function. If parsing fails, then an error with the given message is produced.
fn get_token_res(
    item: TokenStream,
    msg: &str,
    worker_fun: impl FnOnce(String, Span) -> syn::Result<TokenStream>,
) -> syn::Result<TokenStream> {
    let input = parse_input(item, msg)?;
    worker_fun(input.value(), input.span())
}

// Parses the given tokens, looks up an environment variable with the parsed
// input as key and transforms the corresponding value using the provided worker
// function. If parsing fails, then an error with the given message is produced.
fn get_token_res_env(
    item: TokenStream,
    msg: &str,
    worker_fun: impl FnOnce(String, Span) -> syn::Result<TokenStream>,
) -> syn::Result<TokenStream> {
    let input = parse_input(item, msg)?;
    let environment_var_value = match std::env::var(input.value()) {
        Ok(value) => value,
        Err(e) => {
            return Err(syn::Error::new(
                input.span(),
                format!("Environment variable error: {:?}", e),
            ))
        }
    };
    worker_fun(environment_var_value, input.span())
}

fn unwrap_or_report(res: syn::Result<TokenStream>) -> TokenStream {
    res.unwrap_or_else(|e| e.into_compile_error().into())
}

// Worker functions

fn acc_address_worker(str: String, span: Span) -> syn::Result<TokenStream> {
    let address = match AccountAddress::from_str(&str) {
        Ok(addr) => tokenize_slice(&addr.0),
        Err(e) => {
            return Err(syn::Error::new(
                span,
                format!("Invalid account address: {}", e),
            ))
        }
    };

    Ok(quote!(concordium_std::AccountAddress(#address)).into())
}

fn pubkey_ed25519_worker(str: String, span: Span) -> syn::Result<TokenStream> {
    let public_key = match PublicKeyEd25519::from_str(&str) {
        Ok(pk) => tokenize_slice(&pk.0),
        Err(e) => {
            return Err(syn::Error::new(
                span,
                format!("Invalid Ed25519 public key: {}", e),
            ))
        }
    };

    Ok(quote!(concordium_std::PublicKeyEd25519(#public_key)).into())
}

fn pubkey_ecdsa_worker(str: String, span: Span) -> syn::Result<TokenStream> {
    let public_key = match PublicKeyEcdsaSecp256k1::from_str(&str) {
        Ok(pk) => tokenize_slice(&pk.0),
        Err(e) => {
            return Err(syn::Error::new(
                span,
                format!("Invalid ECDSA public key: {}", e),
            ))
        }
    };

    Ok(quote!(concordium_std::PublicKeyEcdsaSecp256k1(#public_key)).into())
}

fn signature_ed25519_worker(str: String, span: Span) -> syn::Result<TokenStream> {
    let signature = match SignatureEd25519::from_str(&str) {
        Ok(sig) => tokenize_slice(&sig.0),
        Err(e) => {
            return Err(syn::Error::new(
                span,
                format!("Invalid Ed25519 signature: {}", e),
            ))
        }
    };

    Ok(quote!(concordium_std::SignatureEd25519(#signature)).into())
}

fn signature_ecdsa_worker(str: String, span: Span) -> syn::Result<TokenStream> {
    let signature = match SignatureEcdsaSecp256k1::from_str(&str) {
        Ok(sig) => tokenize_slice(&sig.0),
        Err(e) => {
            return Err(syn::Error::new(
                span,
                format!("Invalid ECDSA signature: {}", e),
            ))
        }
    };

    Ok(quote!(concordium_std::SignatureEcdsaSecp256k1(#signature)).into())
}

fn contract_address_worker(str: String, span: Span) -> syn::Result<TokenStream> {
    let (index, subindex) = match ContractAddress::from_str(&str) {
        Ok(con) => (con.index, con.subindex),
        Err(e) => {
            return Err(syn::Error::new(
                span,
                format!("Invalid contract address: {}", e),
            ))
        }
    };

    Ok(quote!(concordium_std::ContractAddress::new(#index, #subindex)).into())
}

fn module_ref_worker(str: String, span: Span) -> syn::Result<TokenStream> {
    let module_ref = match ModuleReference::from_str(&str) {
        Ok(mod_ref) => tokenize_slice(&mod_ref.bytes),
        Err(e) => {
            return Err(syn::Error::new(
                span,
                format!("Invalid module reference: {}", e),
            ))
        }
    };

    Ok(quote!(concordium_std::ModuleReference::new(#module_ref)).into())
}

/// Procedural macro for instantiating account addresses.
/// Input must be a valid base58-encoding.
#[proc_macro]
pub fn account_address(item: TokenStream) -> TokenStream {
    let msg = "Expected a string literal of a hex-encoded account address";
    unwrap_or_report(get_token_res(item, msg, acc_address_worker))
}

/// Procedural macro for instantiating account addresses from an environment
/// variable. Input must be the key of an environment variable whose value is
/// set to a valid base58-encoding of an account address.
#[proc_macro]
pub fn account_address_env(item: TokenStream) -> TokenStream {
    let msg = "Expected a string literal of a hex-encoded account address";
    unwrap_or_report(get_token_res_env(item, msg, acc_address_worker))
}

/// Procedural macro for instantiating `PublicKeyEd25519` public keys.
/// Input must be a (case-insensitive) hex-encoding and have a length of 64
/// characters representing 32 bytes.
#[proc_macro]
pub fn public_key_ed25519(item: TokenStream) -> TokenStream {
    let msg = "Expected a string literal of a hex-encoded ED25519 public key";
    unwrap_or_report(get_token_res(item, msg, pubkey_ed25519_worker))
}

/// Procedural macro for instantiating `PublicKeyEd25519` public keys from
/// an environment variable. Input must be the key of an environment variable
/// whose value is set to a hex-encoded public key which must have a length of
/// 64 characters representing 32 bytes.
#[proc_macro]
pub fn public_key_ed25519_env(item: TokenStream) -> TokenStream {
    let msg = "Expected a string literal of a hex-encoded ED25519 public key";
    unwrap_or_report(get_token_res_env(item, msg, pubkey_ed25519_worker))
}

/// Procedural macro for instantiating `PublicKeyEcdsaSecp256k1` public keys.
/// Input must be a (case-insensitive) hex-encoding and have a length of 66
/// characters representing 33 bytes.
#[proc_macro]
pub fn public_key_ecdsa(item: TokenStream) -> TokenStream {
    let msg = "Expected a string literal of a hex-encoded ECDSA public key";
    unwrap_or_report(get_token_res(item, msg, pubkey_ecdsa_worker))
}

/// Procedural macro for instantiating `PublicKeyEcdsaSecp256k1` public keys
/// from an environment variable. Input must be the key of an environment
/// variable whose value is set to a hex-encoded public key which must have a
/// length of 66 characters representing 33 bytes.
#[proc_macro]
pub fn public_key_ecdsa_env(item: TokenStream) -> TokenStream {
    let msg = "Expected a string literal of a hex-encoded ECDSA public key";
    unwrap_or_report(get_token_res_env(item, msg, pubkey_ecdsa_worker))
}

/// Procedural macro for instantiating `SignatureEd25519` signatures.
/// Input must be a (case-insensitive) hex-encoding and have a length of 128
/// characters representing 64 bytes.
#[proc_macro]
pub fn signature_ed25519(item: TokenStream) -> TokenStream {
    let msg = "Expected a string literal of a hex-encoded ED25519 signature";
    unwrap_or_report(get_token_res(item, msg, signature_ed25519_worker))
}

/// Procedural macro for instantiating `SignatureEd25519` signatures from
/// an environment variable. Input must be the key of an environment variable
/// whose value is set to a hex-encoded signature which must have a length of
/// 128 characters representing 64 bytes.
#[proc_macro]
pub fn signature_ed25519_env(item: TokenStream) -> TokenStream {
    let msg = "Expected a string literal of a hex-encoded ED25519 signature";
    unwrap_or_report(get_token_res_env(item, msg, signature_ed25519_worker))
}

/// Procedural macro for instantiating `SignatureEcdsaSecp256k1` signatures.
/// Input must be a (case-insensitive) hex-encoding and have a length of 128
/// characters representing 64 bytes.
#[proc_macro]
pub fn signature_ecdsa(item: TokenStream) -> TokenStream {
    let msg = "Expected a string literal of a hex-encoded ECDSA signature";
    unwrap_or_report(get_token_res(item, msg, signature_ecdsa_worker))
}

/// Procedural macro for instantiating `SignatureEcdsaSecp256k1` signatures from
/// an environment variable. Input must be the key of an environment variable
/// whose value is set to a hex-encoded signature which must have a length of
/// 128 characters representing 64 bytes.
#[proc_macro]
pub fn signature_ecdsa_env(item: TokenStream) -> TokenStream {
    let msg = "Expected a string literal a hex-encoded ECDSA signature";
    unwrap_or_report(get_token_res_env(item, msg, signature_ecdsa_worker))
}

/// Procedural macro for instantiating contract addresses.
/// Input must be of the form "<index,subindex>", where index and subindex
/// are integers.
#[proc_macro]
pub fn contract_address(item: TokenStream) -> TokenStream {
    let msg = "Expected string literal of a contract address in the form of \"<index,subindex>\"";
    unwrap_or_report(get_token_res(item, msg, contract_address_worker))
}

/// Procedural macro for instantiating contract addresses from an environment
/// variable. Input must be the key of an environment variable whose value is
/// set to a contract address of the form "<index,subindex>", where index and
/// subindex are integers
#[proc_macro]
pub fn contract_address_env(item: TokenStream) -> TokenStream {
    let msg = "Expected string literal of a contract address in the form of \"<index,subindex>\"";
    unwrap_or_report(get_token_res_env(item, msg, contract_address_worker))
}

/// Procedural macro for instantiating module references.
/// Input must be a (case-insensitive) hex-encoding and have a length of 64
/// characters representing 32 bytes.
#[proc_macro]
pub fn module_reference(item: TokenStream) -> TokenStream {
    let msg = "Expected string literal of a hex-encoded module reference";
    unwrap_or_report(get_token_res(item, msg, module_ref_worker))
}

/// Procedural macro for instantiating module references from an environment
/// variable. Input must be the key of an environment variable whose value is
/// set to a hex-encoded module reference which must have a length of 64
/// characters representing 32 bytes.
#[proc_macro]
pub fn module_reference_env(item: TokenStream) -> TokenStream {
    let msg = "Expected string literal of a hex-encoded module reference";
    unwrap_or_report(get_token_res_env(item, msg, module_ref_worker))
}
