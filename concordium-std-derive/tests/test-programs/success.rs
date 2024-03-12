//! Ensure that the macros generate compilable code.

use concordium_contracts_common::*;
use concordium_std_derive::*;

const ACC: AccountAddress = account_address!("3kBx2h5Y2veb4hZgAJWPrr8RyQESKm5TjzF3ti1QQ4VSYLwK1G");
const REF: ModuleReference = module_reference!("0000000000000000000000000000000000000000000000000000000000000000");
const CONTRACT: ContractAddress = contract_address!("<1234,0>");
const PK_25519: PublicKeyEd25519 = public_key_ed25519!("012a7e286063ae5dfcebce40636c0546d367d8c65cd4cb69aae1af77a4d61412");
const PK_ECDSA: PublicKeyEcdsaSecp256k1 = public_key_ecdsa!("0214e6a60b8fc58ea707d8ee8fa6ca7b28626d4f6f80b170982644c95d12111853");
const SG_25519: SignatureEd25519 = signature_ed25519!("ec076ae7adaf0a8b921cf2bad86a1a5b5346226618637aa0d6b30f9616f108f9f482640a4ceb14235569cd3af05fac00be2c82dc81c6f6b4a6ba4ea7c3b51a0b");
const SG_ECDSA: SignatureEcdsaSecp256k1 = signature_ecdsa!("EC076AE7ADAF0A8B921CF2BAD86A1A5B5346226618637AA0D6B30F9616F108F9F482640A4CEB14235569CD3AF05FAC00BE2C82DC81C6F6B4A6BA4EA7C3B51A0B");

fn f() {
    println!("{:?}", ACC.to_string());
    println!("{:?}", REF.to_string());
    println!("{:?}", CONTRACT.to_string());
    println!("{:?}", PK_25519.to_string());
    println!("{:?}", PK_ECDSA.to_string());
    println!("{:?}", SG_25519.to_string());
    println!("{:?}", SG_ECDSA.to_string()); 
}

fn main() { }