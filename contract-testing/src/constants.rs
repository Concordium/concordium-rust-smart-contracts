//! Various constants.

use concordium_base::base::Energy;

// Energy constants from Cost.hs in concordium-base.

/// Cost of querying the account balance from within a smart contract instance.
pub(crate) const CONTRACT_INSTANCE_QUERY_ACCOUNT_BALANCE_COST: Energy = Energy { energy: 200 };

/// Cost of querying the contract balance from within a smart contract instance.
pub(crate) const CONTRACT_INSTANCE_QUERY_CONTRACT_BALANCE_COST: Energy = Energy { energy: 200 };

/// Cost of querying the current exchange rates from within a smart contract
/// instance.
pub(crate) const CONTRACT_INSTANCE_QUERY_EXCHANGE_RATE_COST: Energy = Energy { energy: 100 };

/// The base cost of initializing a contract instance to cover administrative
/// costs. Even if no code is run and no instance created.
pub(crate) const INITIALIZE_CONTRACT_INSTANCE_BASE_COST: Energy = Energy { energy: 300 };

/// Cost of creating an empty smart contract instance.
pub(crate) const INITIALIZE_CONTRACT_INSTANCE_CREATE_COST: Energy = Energy { energy: 200 };

/// The base cost of updating a contract instance to cover administrative
/// costs. Even if no code is run.
pub(crate) const UPDATE_CONTRACT_INSTANCE_BASE_COST: Energy = Energy { energy: 300 };
