//! # Concordium Smart Contract Testing
//!
//! This library supports writing integration tests in Rust for Concordium smart
//! contracts.
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
//! chain.create_account(ACC, Account::new(Amount::from_ccd(1000)));
//!
//! // Deploy a smart contract module (built with [Cargo Concordium](https://developer.concordium.software/en/mainnet/smart-contracts/guides/setup-tools.html#cargo-concordium)).
//! let deployment = chain
//!     .module_deploy_v1(ACC, Chain::module_load_v1("path/to/contract.wasm.v1").unwrap())
//!     .unwrap();
//!
//! // Initialize a smart contract from the deployed module.
//! let initialization = chain
//!     .contract_init(
//!         ACC, // Invoker account.
//!         deployment.module_reference, // Module to initialize from.
//!         ContractName::new_unchecked("init_my_contract"), // Contract to init.
//!         OwnedParameter::from_serial(&"my_param").unwrap(), // Any type implementing [`Serial`] can be used.
//!         Amount::zero(), // CCD to send the contract.
//!         Energy::from(10000), // Maximum energy allowed for initializing.
//!     )
//!     .unwrap();
//!
//! // Update the initialized contract.
//! let update = chain
//!     .contract_update(
//!         ACC, // Invoker account.
//!         Address::Account(ACC), // Sender (can also be a contract).
//!         initialization.contract_address, // The contract to update.
//!         EntrypointName::new_unchecked("my_entrypoint"), // The entrypoint to call.
//!         OwnedParameter::from_serial(&42u8).unwrap(), // Another type of parameter.
//!         Amount::from_ccd(100), // Sending the contract 100 CCD.
//!         Energy::from(10000),  // Maximum energy allowed for the update.
//!     )
//!     .unwrap();
//!
//! // Check the chain events produced (updates, interrupts, resumes, transfers, etc.).
//! assert!(matches!(update.chain_events[..], [ChainEvent::Updated{..}]));
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
pub mod types;
pub use types::*;

// Re-export types.
pub use concordium_base::{
    base::Energy,
    contracts_common::{
        from_bytes, to_bytes, AccountAddress, Address, Amount, ContractAddress, ContractName,
        EntrypointName, ExchangeRate, ModuleReference, OwnedContractName, OwnedEntrypointName,
        OwnedParameter, Parameter, SlotTime,
    },
};
pub use concordium_smart_contract_engine::v1::InvokeFailure;
