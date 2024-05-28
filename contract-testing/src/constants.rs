//! Various constants.

use concordium_rust_sdk::base::base::Energy;

// Energy constants from Cost.hs in concordium-base.

/// Cost of querying the account balance from within a smart contract instance.
pub(crate) const CONTRACT_INSTANCE_QUERY_ACCOUNT_BALANCE_COST: Energy = Energy {
    energy: 200,
};

/// Cost of querying the contract balance from within a smart contract instance.
pub(crate) const CONTRACT_INSTANCE_QUERY_CONTRACT_BALANCE_COST: Energy = Energy {
    energy: 200,
};

/// Cost of querying the current exchange rates from within a smart contract
/// instance.
pub(crate) const CONTRACT_INSTANCE_QUERY_EXCHANGE_RATE_COST: Energy = Energy {
    energy: 100,
};

/// Base cost querying account keys. In addition to this cost there is a cost
/// based on the number of returned keys.
pub(crate) const CONTRACT_INSTANCE_QUERY_ACCOUNT_KEYS_BASE_COST: Energy = Energy {
    energy: 200,
};

/// Cost of returning the account keys, based on the number of keys.
/// Each key is 32 bytes, and there is a bit of administrative overhead.
pub(crate) fn contract_instance_query_account_keys_return_cost(num_keys: u32) -> Energy {
    Energy {
        energy: u64::from(num_keys) * 3,
    }
}

/// The cost of querying the contract module reference from a smart contract
/// instance.
pub(crate) const CONTRACT_INSTANCE_QUERY_CONTRACT_MODULE_REFERENCE_COST: Energy = Energy {
    energy: 200,
};

/// The cost of querying the contract module name from a smart contract
/// instance. While the length of a smart contract name is variable, it is at
/// most 100 characters, so there  is no real benefit to varying the cost based
/// on the length.
pub(crate) const CONTRACT_INSTANCE_QUERY_CONTRACT_NAME_COST: Energy = Energy {
    energy: 200,
};

/// Cost **in energy** of verification of an ed25519 signature.
/// This should match the cost of
/// [`verify_ed22519_cost`](concordium_smart_contract_engine::constants::verify_ed25519_cost)
/// except the latter is the cost in interpreter energy, and this on is in
/// [`Energy`].
pub(crate) fn verify_ed25519_energy_cost(num_sigs: u32, message_len: u32) -> Energy {
    Energy {
        energy: u64::from(num_sigs) * (100 + u64::from(message_len) / 10),
    }
}

/// The base cost of initializing a contract instance to cover administrative
/// costs. Even if no code is run and no instance created.
pub(crate) const INITIALIZE_CONTRACT_INSTANCE_BASE_COST: Energy = Energy {
    energy: 300,
};

/// Cost of creating an empty smart contract instance.
pub(crate) const INITIALIZE_CONTRACT_INSTANCE_CREATE_COST: Energy = Energy {
    energy: 200,
};

/// The base cost of updating a contract instance to cover administrative
/// costs. Even if no code is run.
pub(crate) const UPDATE_CONTRACT_INSTANCE_BASE_COST: Energy = Energy {
    energy: 300,
};

/// The name of the environment variable that holds the path to the contract
/// module file. To load the module, use the
/// [`module_load_output`](crate::module_load_output) function.
pub const CONTRACT_MODULE_OUTPUT_PATH_ENV_VAR: &str = "CARGO_CONCORDIUM_TEST_MODULE_OUTPUT_PATH";
