//! # Concordium Smart Contract Testing
//!
//! This library supports writing integration tests in Rust for Concordium smart
//! contracts.
//!
//! To use the library, you must add it to your `Cargo.toml` file under the
//! `[dev-dependencies]` section. The library requries the rust edition `2021`
//! or greater.
//!
//! ```toml
//! [package]
//! # ...
//! edition = "2021"
//!
//! [dev-dependencies]
//! concordium-smart-contract-testing = "1.0"
//! ```
//!
//! ## Basic usage
//!
//! ```no_run
//! use concordium_smart_contract_testing::*;
//!
//! // Create a "chain" with default parameters.
//! let mut chain = Chain::new();
//!
//! // Define an account address to be used.
//! const ACC: AccountAddress = AccountAddress([0;32]);
//!
//! // Create an account with 10000 CCD in balance.
//! chain.create_account(Account::new(ACC, Amount::from_ccd(1000)));
//!
//! // Deploy a smart contract module (built with [Cargo Concordium](https://developer.concordium.software/en/mainnet/smart-contracts/guides/setup-tools.html#cargo-concordium)).
//! let deployment = chain
//!     .module_deploy_v1(
//!         Signer::with_one_key(),
//!         ACC,
//!         module_load_v1("path/to/contract.wasm.v1").unwrap())
//!     .unwrap();
//!
//! // Initialize a smart contract from the deployed module.
//! let initialization = chain
//!     .contract_init(
//!         Signer::with_one_key(), // Used for specifying the number of signatures.
//!         ACC, // Invoker account.
//!         Energy::from(10000), // Maximum energy allowed for initializing.
//!         InitContractPayload {
//!             mod_ref: deployment.module_reference, // Module to initialize from.
//!             init_name: OwnedContractName::new_unchecked("init_my_contract".into()), // Contract to init.
//!             param: OwnedParameter::from_serial(&"my_param").unwrap(), // Any type implementing [`Serial`] can be used.
//!             amount: Amount::zero(), // CCD to send the contract.
//!         }
//!     )
//!     .unwrap();
//!
//! // Update the initialized contract.
//! let update = chain
//!     .contract_update(
//!         Signer::with_one_key(), // Used for specifying the number of signatures.
//!         ACC, // Invoker account.
//!         Address::Account(ACC), // Sender (can also be a contract).
//!         Energy::from(10000),  // Maximum energy allowed for the update.
//!         UpdateContractPayload {
//!             address: initialization.contract_address, // The contract to update.
//!             receive_name: OwnedReceiveName::new_unchecked("my_contract.my_entrypoint".into()), // The receive function to call.
//!             message: OwnedParameter::from_serial(&42u8).unwrap(), // The parameter sent to the contract.
//!             amount: Amount::from_ccd(100), // Sending the contract 100 CCD.
//!         }
//!     )
//!     .unwrap();
//!
//! // Check the trace elements produced (updates, interrupts, resumes, transfers, etc.).
//! assert!(matches!(update.effective_trace_elements().collect::<Vec<_>>()[..], [ContractTraceElement::Updated{..}]));
//!
//! // Check the return value.
//! assert_eq!(update.return_value, to_bytes(&84u8));
//!
//! // Check the balances of both contracts and accounts.
//! assert_eq!(chain.contract_balance(initialization.contract_address), Some(Amount::from_ccd(100)));
//! assert_eq!(chain.account_balance_available(ACC), Some(
//!     Amount::from_ccd(1000)
//!     - Amount::from_ccd(100) // Amount sent to contract.
//!     - deployment.transaction_fee
//!     - initialization.transaction_fee
//!     - update.transaction_fee));
//!     
//! ```
mod constants;
mod impls;
mod invocation;
mod types;
pub use impls::{module_load_v1, module_load_v1_raw};
pub use types::*;

// Re-export types.
pub use concordium_base::{
    base::Energy,
    contracts_common::{
        from_bytes, to_bytes, AccountAddress, Address, Amount, ContractAddress, ContractName,
        EntrypointName, ExchangeRate, ModuleReference, OwnedContractName, OwnedEntrypointName,
        OwnedParameter, OwnedReceiveName, Parameter, ReceiveName, SlotTime,
    },
    smart_contracts::{ContractEvent, ContractTraceElement, InstanceUpdatedEvent, WasmVersion},
    transactions::{InitContractPayload, UpdateContractPayload},
};
pub use concordium_smart_contract_engine::v1::InvokeFailure;
