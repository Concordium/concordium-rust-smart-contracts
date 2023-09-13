use crate::{
    constants,
    invocation::{ChangeSet, EntrypointInvocationHandler, TestConfigurationError},
    types::*,
};
use anyhow::anyhow;
use concordium_base::{
    base::{AccountThreshold, Energy, InsufficientEnergy},
    constants::MAX_WASM_MODULE_SIZE,
    contracts_common::{
        self, AccountAddress, AccountBalance, Address, Amount, ChainMetadata, ContractAddress,
        Duration, ExchangeRate, ExchangeRates, ModuleReference, OwnedPolicy, SlotTime, Timestamp,
    },
    hashes::BlockHash,
    smart_contracts::{ContractEvent, ModuleSource, WasmModule, WasmVersion},
    transactions::{
        self, cost, AccountAccessStructure, InitContractPayload, UpdateContractPayload,
    },
};
use concordium_rust_sdk::{self as sdk, v2::Endpoint};
use concordium_smart_contract_engine::{
    v0,
    v1::{self, InvokeResponse},
    InterpreterEnergy,
};
use concordium_wasm::validate::ValidationConfig;
use num_bigint::BigUint;
use num_integer::Integer;
use std::{collections::BTreeMap, future::Future, path::Path, sync::Arc};
use tokio::{runtime, time::timeout};

/// The timeout duration set for queries with an external node.
const EXTERNAL_NODE_QUERY_TIMEOUT: tokio::time::Duration = tokio::time::Duration::from_secs(10);

/// The timeout duration set for connecting to an external node.
const EXTERNAL_NODE_CONNECT_TIMEOUT: tokio::time::Duration = tokio::time::Duration::from_secs(3);

impl Default for Chain {
    fn default() -> Self { Self::new() }
}

impl ChainParameters {
    /// Create a new [`ChainParameters`](Self) where
    ///  - `block_time` defaults to `0`,
    ///  - `micro_ccd_per_euro` defaults to `50000 / 1`
    ///  - `euro_per_energy` defaults to `1 / 50000`.
    ///
    /// With these exchange rates, one energy costs one microCCD.
    pub fn new() -> Self {
        Self::new_with_time_and_rates(
            Timestamp::from_timestamp_millis(0),
            ExchangeRate::new_unchecked(50000, 1),
            ExchangeRate::new_unchecked(1, 50000),
        )
        .expect("Parameters are in range.")
    }

    /// Create a new [`ChainParameters`](Self) with a specified `block_time`
    /// where
    ///  - `micro_ccd_per_euro` defaults to `50000 / 1`
    ///  - `euro_per_energy` defaults to `1 / 50000`.
    pub fn new_with_time(block_time: SlotTime) -> Self {
        Self {
            block_time,
            ..Self::new()
        }
    }

    /// Create a new [`ChainParameters`](Self) where all the configurable
    /// parameters are provided.
    ///
    /// Returns an error if the exchange rates provided makes one energy cost
    /// more than `u64::MAX / 100_000_000_000`.
    pub fn new_with_time_and_rates(
        block_time: SlotTime,
        micro_ccd_per_euro: ExchangeRate,
        euro_per_energy: ExchangeRate,
    ) -> Result<Self, ExchangeRateError> {
        // Ensure the exchange rates are within a valid range.
        check_exchange_rates(euro_per_energy, micro_ccd_per_euro)?;

        Ok(Self {
            block_time,
            micro_ccd_per_euro,
            euro_per_energy,
        })
    }

    /// Helper function for converting [`Energy`] to [`Amount`] using the two
    /// [`ExchangeRate`]s `euro_per_energy` and `micro_ccd_per_euro`.
    pub fn calculate_energy_cost(&self, energy: Energy) -> Amount {
        energy_to_amount(energy, self.euro_per_energy, self.micro_ccd_per_euro)
    }
}

impl ChainBuilder {
    /// Create a new [`ChainBuilder`] for constructing the [`Chain`].
    ///
    /// Can also be created via the [`Chain::builder`] method.
    ///
    /// To complete the building process, use [`ChainBuilder::build`], see the
    /// example below.
    ///
    /// # Example
    /// ```
    /// # use concordium_smart_contract_testing::*;
    ///
    /// let chain = ChainBuilder::new()
    ///             // Use zero or more builder methods, for example:
    ///             .micro_ccd_per_euro(ExchangeRate::new_unchecked(50000, 1))
    ///             .block_time(Timestamp::from_timestamp_millis(123))
    ///             // Then build:
    ///             .build()
    ///             .unwrap();
    /// ```
    pub fn new() -> Self {
        Self {
            external_node_endpoint: None,
            external_query_block: None,
            micro_ccd_per_euro: None,
            micro_ccd_per_euro_from_external: false,
            euro_per_energy: None,
            euro_per_energy_from_external: false,
            block_time: None,
            block_time_from_external: false,
        }
    }

    /// Configure a connection to an external Concordium node.
    ///
    /// The connection can be used for getting the current exchange rates
    /// between CCD, Euro and Energy.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use concordium_smart_contract_testing::*;
    /// let chain = Chain::builder()
    ///     .external_node_connection(Endpoint::from_static(
    ///         "http://node.testnet.concordium.com:20000",
    ///     ))
    ///     .build()
    ///     .unwrap();
    /// ```
    pub fn external_node_connection(mut self, endpoint: impl Into<Endpoint>) -> Self {
        self.external_node_endpoint = Some(endpoint.into());
        self
    }

    /// Configure the block to be used for all external queries.
    ///
    /// If this is not set, then the last final block will be queried during
    /// [`ChainBuilder::build`] and saved, so it can be used for future queries.
    ///
    /// This can only be used in combination with
    /// [`external_node_connection`][Self::external_node_connection].
    ///
    /// To view the configured block, see [`Chain::external_query_block`].
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use concordium_smart_contract_testing::*;
    /// let chain = Chain::builder()
    ///     .external_node_connection(Endpoint::from_static(
    ///         "http://node.testnet.concordium.com:20000",
    ///     ))
    ///     .external_query_block(
    ///         "95ff82f26892a2327c3e7ac582224a54d75c367341fbff209bce552d81349eb0"
    ///             .parse()
    ///             .unwrap(),
    ///     )
    ///     .build()
    ///     .unwrap();
    /// ```
    pub fn external_query_block(mut self, query_block: BlockHash) -> Self {
        self.external_query_block = Some(query_block);
        self
    }

    /// Configure the exchange rate between microCCD and euro.
    ///
    /// By default the rate is `50000 / 1`.
    ///
    /// This cannot be used together with
    /// [`ChainBuilder::micro_ccd_per_euro_from_external`].
    ///
    /// # Example
    /// ```
    /// # use concordium_smart_contract_testing::*;
    /// let chain = ChainBuilder::new()
    ///     .micro_ccd_per_euro(ExchangeRate::new_unchecked(50000, 1))
    ///     .build()
    ///     .unwrap();
    /// ```
    pub fn micro_ccd_per_euro(mut self, exchange_rate: ExchangeRate) -> Self {
        self.micro_ccd_per_euro = Some(exchange_rate);
        self
    }

    /// Configure the exchange rate between microCCD and euro.
    ///
    /// By default the rate is `1 / 50000`.
    ///
    /// This cannot be used together with
    /// [`ChainBuilder::euro_per_energy_from_external`].
    ///
    /// # Example
    /// ```
    /// # use concordium_smart_contract_testing::*;
    /// let chain = ChainBuilder::new()
    ///     .euro_per_energy(ExchangeRate::new_unchecked(1, 50000))
    ///     .build()
    ///     .unwrap();
    /// ```
    pub fn euro_per_energy(mut self, exchange_rate: ExchangeRate) -> Self {
        self.euro_per_energy = Some(exchange_rate);
        self
    }

    /// Configure the exchange rate between microCCD and euro using the external
    /// node connection.
    ///
    /// This can only be used in combination with
    /// [`external_node_connection`][Self::external_node_connection], and it
    /// cannot be used together with
    /// [`micro_ccd_per_euro`][Self::micro_ccd_per_euro].
    ///
    /// # Example
    /// ```
    /// # use concordium_smart_contract_testing::*;
    /// let chain = ChainBuilder::new()
    ///     .external_node_connection(Endpoint::from_static(
    ///         "http://node.testnet.concordium.com:20000",
    ///     ))
    ///     .micro_ccd_per_euro_from_external()
    ///     .build()
    ///     .unwrap();
    /// ```
    pub fn micro_ccd_per_euro_from_external(mut self) -> Self {
        self.micro_ccd_per_euro_from_external = true;
        self
    }

    /// Configure the exchange rate between euro and energy using the external
    /// node connection.
    ///
    /// This can only be used in combination with
    /// [`external_node_connection`][Self::external_node_connection], and it
    /// cannot be used together with
    /// [`euro_per_energy`][Self::euro_per_energy].
    ///
    /// # Example
    /// ```
    /// # use concordium_smart_contract_testing::*;
    /// let chain = ChainBuilder::new()
    ///     .external_node_connection(Endpoint::from_static(
    ///         "http://node.testnet.concordium.com:20000",
    ///     ))
    ///     .euro_per_energy_from_external()
    ///     .build()
    ///     .unwrap();
    /// ```
    pub fn euro_per_energy_from_external(mut self) -> Self {
        self.euro_per_energy_from_external = true;
        self
    }

    /// Configure the block time.
    ///
    /// By default the block time is `0`.
    ///
    /// This cannot be used in combination with
    /// [`ChainBuilder::block_time_from_external`].
    ///
    /// # Example
    /// ```
    /// # use concordium_smart_contract_testing::*;
    /// let chain = ChainBuilder::new()
    ///     .block_time(Timestamp::from_timestamp_millis(1687440701000))
    ///     .build()
    ///     .unwrap();
    /// ```
    pub fn block_time(mut self, block_time: Timestamp) -> Self {
        self.block_time = Some(block_time);
        self
    }

    /// Configure the block time using the external node connection.
    ///
    /// This can only be used in combination with
    /// [`external_node_connection`][Self::external_node_connection], and it
    /// cannot be used together with
    /// [`block_time`][Self::block_time].
    ///
    /// # Example
    /// ```
    /// # use concordium_smart_contract_testing::*;
    /// let chain = ChainBuilder::new()
    ///     .external_node_connection(Endpoint::from_static(
    ///         "http://node.testnet.concordium.com:20000",
    ///     ))
    ///     .block_time_from_external()
    ///     .build()
    ///     .unwrap();
    /// ```
    pub fn block_time_from_external(mut self) -> Self {
        self.block_time_from_external = true;
        self
    }

    /// Build the [`Chain`] with the configured options.
    ///
    /// # Example
    /// ```
    /// # use concordium_smart_contract_testing::*;
    ///
    /// let chain = Chain::builder()
    ///             // Use zero or more builder methods, for example:
    ///             .euro_per_energy(ExchangeRate::new_unchecked(1, 50000))
    ///             .micro_ccd_per_euro(ExchangeRate::new_unchecked(50000, 1))
    ///             // Then build:
    ///             .build()
    ///             .unwrap();
    /// ```
    pub fn build(self) -> Result<Chain, ChainBuilderError> {
        // Create the chain with default parameters.
        let mut chain = Chain::new();

        // Setup the external node connection if provided. This also forwards and sets
        // the external query block.
        if let Some(endpoint) = self.external_node_endpoint {
            chain.setup_external_node_connection(endpoint, self.external_query_block)?;
        }

        // Check for conflicting exchange rate configurations.
        if self.micro_ccd_per_euro.is_some() && self.micro_ccd_per_euro_from_external {
            return Err(ChainBuilderError::ConflictingMicroCCDPerEuro);
        }
        if self.euro_per_energy.is_some() && self.euro_per_energy_from_external {
            return Err(ChainBuilderError::ConflictingEuroPerEnergy);
        }

        // Set the exchange rates via an external query.
        if self.micro_ccd_per_euro_from_external || self.euro_per_energy_from_external {
            let exchange_rates = chain.get_exchange_rates_via_external_node()?;
            if self.micro_ccd_per_euro_from_external {
                chain.parameters.micro_ccd_per_euro = exchange_rates.micro_ccd_per_euro;
            }
            if self.euro_per_energy_from_external {
                chain.parameters.euro_per_energy = exchange_rates.euro_per_energy;
            }
        }

        // Set the exchange rates directly.
        if let Some(micro_ccd_per_euro) = self.micro_ccd_per_euro {
            chain.parameters.micro_ccd_per_euro = micro_ccd_per_euro;
        }
        if let Some(euro_per_energy) = self.euro_per_energy {
            chain.parameters.euro_per_energy = euro_per_energy;
        }

        // Check the exchange rates and return early if they are invalid.
        check_exchange_rates(
            chain.parameters.euro_per_energy,
            chain.parameters.micro_ccd_per_euro,
        )?;

        match (self.block_time, self.block_time_from_external) {
            (Some(_), true) => return Err(ChainBuilderError::ConflictingBlockTime),
            (Some(block_time), _) => {
                chain.parameters.block_time = block_time;
            }
            (_, true) => {
                chain.set_block_time_via_external_node()?;
            }
            _ => (),
        }

        // Replace the default block time if provided.
        if let Some(block_time) = self.block_time {
            chain.parameters.block_time = block_time;
        }

        Ok(chain)
    }
}

impl Default for ChainBuilder {
    fn default() -> Self { Self::new() }
}

impl Chain {
    /// Get a [`ChainBuilder`] for constructing a new [`Chain`] with a builder
    /// pattern.
    ///
    /// See the [`ChainBuilder`] for more details.
    pub fn builder() -> ChainBuilder { ChainBuilder::new() }

    /// Create a new [`Chain`](Self) where all the configurable parameters are
    /// provided.
    ///
    /// Returns an error if the exchange rates provided makes one energy cost
    /// more than `u64::MAX / 100_000_000_000`.
    ///
    /// *For more configuration options and flexibility, use the builder
    /// pattern. See [`Chain::builder`].*
    pub fn new_with_time_and_rates(
        block_time: SlotTime,
        micro_ccd_per_euro: ExchangeRate,
        euro_per_energy: ExchangeRate,
    ) -> Result<Self, ExchangeRateError> {
        Ok(Self {
            parameters:               ChainParameters::new_with_time_and_rates(
                block_time,
                micro_ccd_per_euro,
                euro_per_energy,
            )?,
            accounts:                 BTreeMap::new(),
            modules:                  BTreeMap::new(),
            contracts:                BTreeMap::new(),
            next_contract_index:      0,
            external_node_connection: None,
        })
    }

    /// Create a new [`Chain`](Self) with a specified `block_time` where
    ///  - `micro_ccd_per_euro` defaults to `50000 / 1`
    ///  - `euro_per_energy` defaults to `1 / 50000`.
    ///
    /// *For more configuration options and flexibility, use the builder
    /// pattern. See [`Chain::builder`].*
    pub fn new_with_time(block_time: SlotTime) -> Self {
        Self {
            parameters: ChainParameters::new_with_time(block_time),
            ..Self::new()
        }
    }

    /// Create a new [`Chain`](Self) where
    ///  - `block_time` defaults to `0`,
    ///  - `micro_ccd_per_euro` defaults to `50000 / 1`
    ///  - `euro_per_energy` defaults to `1 / 50000`.
    ///
    /// With these exchange rates, one energy costs one microCCD.
    ///
    /// *For more configuration options and flexibility, use the builder
    /// pattern. See [`Chain::builder`].*
    pub fn new() -> Self {
        Self::new_with_time_and_rates(
            Timestamp::from_timestamp_millis(0),
            ExchangeRate::new_unchecked(50000, 1),
            ExchangeRate::new_unchecked(1, 50000),
        )
        .expect("Rates known to be within range.")
    }

    /// Helper function for converting [`Energy`] to [`Amount`] using the two
    /// [`ExchangeRate`]s `euro_per_energy` and `micro_ccd_per_euro`.
    pub fn calculate_energy_cost(&self, energy: Energy) -> Amount {
        self.parameters.calculate_energy_cost(energy)
    }

    /// Get the state of the contract if it exists in the [`Chain`](Self).
    pub fn get_contract(&self, address: ContractAddress) -> Option<&Contract> {
        self.contracts.get(&address)
    }

    /// Get the the module if it exists in the [`Chain`](Self).
    pub fn get_module(&self, module: ModuleReference) -> Option<&ContractModule> {
        self.modules.get(&module)
    }

    /// Get the state of the account if it exists in the [`Chain`](Self).
    /// Account addresses that are aliases will return the same account.
    pub fn get_account(&self, address: AccountAddress) -> Option<&Account> {
        self.accounts.get(&address.into())
    }

    /// Deploy a smart contract module.
    ///
    /// The `WasmModule` can be loaded from disk with either
    /// [`module_load_v1`] or [`module_load_v1_raw`].
    ///
    /// Parameters:
    ///  - `signer`: the signer with a number of keys, which affects the cost.
    ///  - `sender`: the sender account.
    ///  - `module`: the v1 wasm module.
    pub fn module_deploy_v1(
        &mut self,
        signer: Signer,
        sender: AccountAddress,
        wasm_module: WasmModule,
    ) -> Result<ModuleDeploySuccess, ModuleDeployError> {
        // For maintainers:
        //
        // This function does not correspond exactly to what happens in the node.
        // There a user is also expected to give a max energy bound and the failures are
        // slightly different. There it is possible to fail with "out of energy"
        // error whereas here we only fail with "insufficient funds" if the user does
        // not have enough CCD to pay.
        //
        // If users use our tools to deploy modules the costs are calculated for them so
        // that deployment should never fail with out of energy. Not requiring energy
        // provides a more ergonomic experience.
        let Ok(sender_account) = self.accounts
            .get_mut(&sender.into())
            .ok_or(AccountDoesNotExist { address: sender }) else {
            // Ensure sender account exists.
            return Err(ModuleDeployError {
                kind:            ModuleDeployErrorKind::SenderDoesNotExist(AccountDoesNotExist {
                    address: sender,
                }),
                energy_used:     0.into(),
                transaction_fee: Amount::zero(),
            });
        };

        // Only v1 modules are supported in this testing library.
        // This error case does not exist in the node, so we don't need to match a
        // specific cost. We charge 0 for it.
        if wasm_module.version != WasmVersion::V1 {
            return Err(ModuleDeployError {
                kind:            ModuleDeployErrorKind::UnsupportedModuleVersion(
                    wasm_module.version,
                ),
                energy_used:     0.into(),
                transaction_fee: Amount::zero(),
            });
        }

        let parameters = &self.parameters;
        let check_header_energy = {
            // +1 for the tag, +8 for size and version
            let payload_size = 1
                + 8
                + wasm_module.source.size()
                + transactions::construct::TRANSACTION_HEADER_SIZE;
            cost::base_cost(payload_size, signer.num_keys)
        };

        // Calculate the deploy module cost.
        let deploy_module_energy = cost::deploy_module(wasm_module.source.size());
        let energy_used = check_header_energy + deploy_module_energy;
        let transaction_fee = parameters.calculate_energy_cost(energy_used);

        // Check if the account has sufficient balance to cover the transaction fee.
        // This fee corresponds to the energy_reserved that our tools calculate when
        // sending the transaction to the node. The account is not charged in the node
        // unless it has sufficient balance to pay for the full deployment (and thus all
        // the energy).
        if sender_account.balance.available() < transaction_fee {
            return Err(ModuleDeployError {
                kind:            ModuleDeployErrorKind::InsufficientFunds,
                energy_used:     0.into(),
                transaction_fee: Amount::zero(),
            });
        };

        // Charge the account.
        sender_account.balance.total -= transaction_fee;

        // Construct the artifact.
        let artifact =
            match concordium_wasm::utils::instantiate_with_metering::<v1::ProcessedImports, _>(
                ValidationConfig::V1,
                &v1::ConcordiumAllowedImports {
                    support_upgrade: true,
                },
                wasm_module.source.as_ref(),
            ) {
                Ok(artifact) => artifact,
                Err(err) => {
                    return Err(ModuleDeployError {
                        kind: ModuleInvalidError(err).into(),
                        energy_used,
                        transaction_fee,
                    })
                }
            };

        let module_reference: ModuleReference = wasm_module.get_module_ref();

        // Ensure module hasn't been deployed before.
        if self.modules.contains_key(&module_reference) {
            return Err(ModuleDeployError {
                kind: ModuleDeployErrorKind::DuplicateModule(module_reference),
                energy_used,
                transaction_fee,
            });
        }
        self.modules.insert(module_reference, ContractModule {
            // we follow protocol 6 semantics, and don't count the custom section size towards
            // module size.
            size:     wasm_module
                .source
                .size()
                .saturating_sub(artifact.custom_sections_size),
            artifact: Arc::new(artifact.artifact),
        });
        Ok(ModuleDeploySuccess {
            module_reference,
            energy_used,
            transaction_fee,
        })
    }

    /// Initialize a contract.
    ///
    /// **Parameters:**
    ///  - `signer`: the signer with a number of keys, which affects the cost.
    ///  - `sender`: The account paying for the transaction. Will also become
    ///    the owner of the contract created.
    ///  - `energy_reserved`: Amount of energy reserved for executing the init
    ///   method.
    ///  - `payload`:
    ///    - `amount`: The initial balance of the contract. Subtracted from the
    ///      `sender` account.
    ///    - `mod_ref`: The reference to the a module that has already been
    ///      deployed.
    ///    - `init_name`: Name of the contract to initialize.
    ///    - `param`: Parameter provided to the init method.
    pub fn contract_init(
        &mut self,
        signer: Signer,
        sender: AccountAddress,
        energy_reserved: Energy,
        payload: InitContractPayload,
    ) -> Result<ContractInitSuccess, ContractInitError> {
        let mut remaining_energy = energy_reserved;
        if !self.account_exists(sender) {
            return Err(self.convert_to_init_error(
                ContractInitErrorKind::SenderDoesNotExist(AccountDoesNotExist { address: sender }),
                energy_reserved,
                remaining_energy,
            ));
        }

        let res = self.contract_init_worker(
            signer,
            sender,
            energy_reserved,
            payload,
            &mut remaining_energy,
        );

        let (res, transaction_fee) = match res {
            Ok(s) => {
                let transaction_fee = s.transaction_fee;
                (Ok(s), transaction_fee)
            }
            Err(e) => {
                let err = self.convert_to_init_error(e, energy_reserved, remaining_energy);
                let transaction_fee = err.transaction_fee;
                (Err(err), transaction_fee)
            }
        };

        // Charge the account.
        self.account_mut(sender)
            .expect("existence already checked")
            .balance
            .total -= transaction_fee;
        res
    }

    /// Helper method for initializing contracts, which does most of the actual
    /// work.
    ///
    /// The main reason for splitting init in two is to have this method return
    /// early if it runs out of energy. `contract_init` will then always
    /// ensure to charge the account for the energy used.
    fn contract_init_worker(
        &mut self,
        signer: Signer,
        sender: AccountAddress,
        energy_reserved: Energy,
        payload: InitContractPayload,
        remaining_energy: &mut Energy,
    ) -> Result<ContractInitSuccess, ContractInitErrorKind> {
        // Get the account and check that it has sufficient balance to pay for the
        // reserved_energy and amount.
        let account_info = self.account(sender)?;

        let energy_reserved_cost = self.parameters.calculate_energy_cost(energy_reserved);

        // Check that the account can pay for the reserved energy.
        if account_info.balance.available() < energy_reserved_cost {
            return Err(ContractInitErrorKind::InsufficientFunds);
        }

        // Compute the base cost for checking the transaction header.
        let check_header_cost = {
            // 1 byte for the tag.
            let transaction_size =
                transactions::construct::TRANSACTION_HEADER_SIZE + 1 + payload.size() as u64;
            transactions::cost::base_cost(transaction_size, signer.num_keys)
        };

        // Charge the header cost.
        remaining_energy.tick_energy(check_header_cost)?;

        // Ensure that the parameter has a valid size.
        if payload.param.as_ref().len() > contracts_common::constants::MAX_PARAMETER_LEN {
            return Err(ContractInitErrorKind::ParameterTooLarge);
        }

        // Charge the base cost for initializing a contract.
        remaining_energy.tick_energy(constants::INITIALIZE_CONTRACT_INSTANCE_BASE_COST)?;

        // Check that the account also has enough funds to pay for the amount (in
        // addition to the reserved energy).
        if account_info.balance.available() < energy_reserved_cost + payload.amount {
            return Err(ContractInitErrorKind::AmountTooLarge);
        }

        // Lookup module.
        let module = self.contract_module(payload.mod_ref)?;
        let lookup_cost = lookup_module_cost(&module);

        // Charge the cost for looking up the module.
        remaining_energy.tick_energy(lookup_cost)?;

        // Ensure the module contains the provided init name.
        let init_name = payload.init_name.as_contract_name().get_chain_name();
        if module.artifact.export.get(init_name).is_none() {
            return Err(ContractInitErrorKind::ContractNotPresentInModule {
                name: payload.init_name,
            });
        }

        // Sender policies have a very bespoke serialization in
        // order to allow skipping portions of them in smart contracts.
        let sender_policies = {
            let mut out = Vec::new();
            account_info
                .policy
                .serial_for_smart_contract(&mut out)
                .expect("Writing to a vector should succeed.");
            out
        };

        // Construct the context.
        let init_ctx = v0::InitContext {
            metadata: ChainMetadata {
                slot_time: self.parameters.block_time,
            },
            init_origin: sender,
            sender_policies,
        };
        // Initialize contract
        // We create an empty loader as no caching is used in this testing library
        // presently, so the loader is not used.
        let mut loader = v1::trie::Loader::new(&[][..]);

        let energy_given_to_interpreter = to_interpreter_energy(*remaining_energy);
        let res = v1::invoke_init(
            module.artifact,
            init_ctx,
            v1::InitInvocation {
                amount: payload.amount,
                init_name,
                parameter: payload.param.as_ref(),
                energy: energy_given_to_interpreter,
            },
            false, // We only support protocol P5 and up, so no limiting.
            loader,
        );
        // Handle the result
        match res {
            Ok(v1::InitResult::Success {
                logs,
                return_value: _, /* Ignore return value for now, since our tools do not support
                                  * it for inits, currently. */
                remaining_energy: remaining_interpreter_energy,
                mut state,
            }) => {
                let contract_address = self.create_contract_address();
                let mut collector = v1::trie::SizeCollector::default();

                let persisted_state = state.freeze(&mut loader, &mut collector);

                // Perform the subtraction in the more finegrained (*1000) `InterpreterEnergy`,
                // and *then* convert to `Energy`. This is how it is done in the node, and if we
                // swap the operations, it can result in a small discrepancy due to rounding.
                let energy_used_in_interpreter = from_interpreter_energy(
                    energy_given_to_interpreter.saturating_sub(remaining_interpreter_energy),
                );
                remaining_energy.tick_energy(energy_used_in_interpreter)?;

                // Charge one energy per stored state byte.
                let energy_for_state_storage = Energy::from(collector.collect());
                remaining_energy.tick_energy(energy_for_state_storage)?;

                // Charge the constant cost for initializing a contract.
                remaining_energy
                    .tick_energy(constants::INITIALIZE_CONTRACT_INSTANCE_CREATE_COST)?;

                let contract = Contract {
                    module_reference: payload.mod_ref,
                    contract_name:    payload.init_name,
                    state:            persisted_state,
                    owner:            sender,
                    self_balance:     payload.amount,
                    address:          contract_address,
                };

                // Save the contract.
                self.contracts.insert(contract_address, contract);

                // Subtract the amount from the invoker.
                self.account_mut(sender)
                    .expect("Account known to exist")
                    .balance
                    .total -= payload.amount;

                let energy_used = energy_reserved - *remaining_energy;
                let transaction_fee = self.parameters.calculate_energy_cost(energy_used);

                Ok(ContractInitSuccess {
                    contract_address,
                    events: contract_events_from_logs(logs),
                    energy_used,
                    transaction_fee,
                })
            }
            Ok(v1::InitResult::Reject {
                reason,
                return_value,
                remaining_energy: remaining_interpreter_energy,
            }) => {
                let energy_used_in_interpreter = from_interpreter_energy(
                    energy_given_to_interpreter.saturating_sub(remaining_interpreter_energy),
                );
                remaining_energy.tick_energy(energy_used_in_interpreter)?;
                Err(ContractInitErrorKind::ExecutionError {
                    error: InitExecutionError::Reject {
                        reason,
                        return_value,
                    },
                })
            }
            Ok(v1::InitResult::Trap {
                error,
                remaining_energy: remaining_interpreter_energy,
            }) => {
                let energy_used_in_interpreter = from_interpreter_energy(
                    energy_given_to_interpreter.saturating_sub(remaining_interpreter_energy),
                );
                remaining_energy.tick_energy(energy_used_in_interpreter)?;
                Err(ContractInitErrorKind::ExecutionError {
                    error: InitExecutionError::Trap {
                        error: error.into(),
                    },
                })
            }
            Ok(v1::InitResult::OutOfEnergy) => {
                *remaining_energy = Energy::from(0);
                Err(ContractInitErrorKind::ExecutionError {
                    error: InitExecutionError::OutOfEnergy,
                })
            }
            Err(error) => Err(ContractInitErrorKind::ExecutionError {
                error: InitExecutionError::Trap {
                    error: error.into(),
                },
            }),
        }
    }

    /// Helper method that handles contract invocation.
    ///
    /// *Preconditions:*
    ///  - `invoker` exists.
    ///  - `sender` exists.
    ///  - `invoker` has sufficient balance to pay for `energy_reserved`.
    fn contract_invocation_worker(
        &self,
        invoker: AccountAddress,
        sender: Address,
        energy_reserved: Energy,
        amount_reserved_for_energy: Amount,
        payload: UpdateContractPayload,
        remaining_energy: &mut Energy,
    ) -> Result<(InvokeResponse, ChangeSet, Vec<DebugTraceElement>), ContractInvokeError> {
        // Check if the contract to invoke exists.
        if !self.contract_exists(payload.address) {
            return Err(self.convert_to_invoke_error(
                ContractDoesNotExist {
                    address: payload.address,
                }
                .into(),
                Vec::new(),
                energy_reserved,
                *remaining_energy,
            ));
        }

        // Ensure that the parameter has a valid size.
        if payload.message.as_ref().len() > contracts_common::constants::MAX_PARAMETER_LEN {
            return Err(self.convert_to_invoke_error(
                ContractInvokeErrorKind::ParameterTooLarge,
                Vec::new(),
                energy_reserved,
                *remaining_energy,
            ));
        }

        // Check that the invoker has sufficient funds to pay for amount (in addition to
        // the energy reserved, which is already checked).
        if self
            .account(invoker)
            .expect("Precondition violation: must already exist")
            .balance
            .available()
            < amount_reserved_for_energy + payload.amount
        {
            return Err(self.convert_to_invoke_error(
                ContractInvokeErrorKind::AmountTooLarge,
                Vec::new(),
                energy_reserved,
                *remaining_energy,
            ));
        }

        let mut contract_invocation = EntrypointInvocationHandler {
            changeset: ChangeSet::new(),
            remaining_energy,
            energy_reserved,
            chain: self,
            reserved_amount: amount_reserved_for_energy,
            invoker,
            // Starts at 1 since 0 is the "initial state" of all contracts in the current
            // transaction.
            next_contract_modification_index: 1,
        };

        match contract_invocation.invoke_entrypoint(invoker, sender, payload) {
            Ok((result, trace_elements)) => {
                Ok((result, contract_invocation.changeset, trace_elements))
            }
            Err(err) => Err(self.convert_to_invoke_error(
                err.into(),
                Vec::new(),
                energy_reserved,
                *remaining_energy,
            )),
        }
    }

    fn contract_invocation_process_response(
        &self,
        result: InvokeResponse,
        trace_elements: Vec<DebugTraceElement>,
        energy_reserved: Energy,
        remaining_energy: Energy,
        state_changed: bool,
    ) -> Result<ContractInvokeSuccess, ContractInvokeError> {
        match result {
            v1::InvokeResponse::Success { new_balance, data } => {
                let energy_used = energy_reserved - remaining_energy;
                let transaction_fee = self.parameters.calculate_energy_cost(energy_used);
                Ok(ContractInvokeSuccess {
                    trace_elements,
                    energy_used,
                    transaction_fee,
                    return_value: data.unwrap_or_default(),
                    state_changed,
                    new_balance,
                })
            }
            v1::InvokeResponse::Failure { kind } => Err(self.convert_to_invoke_error(
                ContractInvokeErrorKind::ExecutionError { failure_kind: kind },
                trace_elements,
                energy_reserved,
                remaining_energy,
            )),
        }
    }

    /// Update a contract by calling one of its entrypoints.
    ///
    /// If successful, all changes will be saved.
    ///
    /// **Parameters:**
    ///  - `invoker`: the account paying for the transaction.
    ///  - `sender`: the sender of the message, can be an account or contract.
    ///    For top-level invocations, such as those caused by sending a contract
    ///    update transaction on the chain, the `sender` is always the
    ///    `invoker`. Here we provide extra freedom for testing invocations
    ///    where the sender differs.
    ///  - `contract_address`: the contract to update.
    ///  - `entrypoint`: the entrypoint to call.
    ///  - `parameter`: the contract parameter.
    ///  - `amount`: the amount sent to the contract.
    ///  - `energy_reserved`: the maximum energy that can be used in the update.
    pub fn contract_update(
        &mut self,
        signer: Signer,
        invoker: AccountAddress,
        sender: Address,
        energy_reserved: Energy,
        payload: UpdateContractPayload,
    ) -> Result<ContractInvokeSuccess, ContractInvokeError> {
        // Ensure the sender exists.
        if !self.address_exists(sender) {
            // This situation never happens on the chain since to send a message the sender
            // is verified upfront. So what we do here is custom behaviour, and we reject
            // without consuming any energy.
            return Err(ContractInvokeError {
                energy_used:     Energy::from(0),
                transaction_fee: Amount::zero(),
                trace_elements:  Vec::new(),
                kind:            ContractInvokeErrorKind::SenderDoesNotExist(sender),
            });
        }

        // Ensure the invoker exists.
        let Ok(account_info) = self.account(invoker) else {
            return Err(ContractInvokeError {
                energy_used:     Energy::from(0),
                transaction_fee: Amount::zero(),
                trace_elements:  Vec::new(),
                kind:            ContractInvokeErrorKind::InvokerDoesNotExist(
                    AccountDoesNotExist { address: invoker },
                ),
            });
        };

        // Compute the base cost for checking the transaction header.
        let check_header_cost = {
            // 1 byte for the tag.
            let transaction_size =
                transactions::construct::TRANSACTION_HEADER_SIZE + 1 + payload.size() as u64;
            transactions::cost::base_cost(transaction_size, signer.num_keys)
        };

        // Charge the header cost.
        let mut remaining_energy =
            energy_reserved
                .checked_sub(check_header_cost)
                .ok_or(ContractInvokeError {
                    energy_used:     Energy::from(0),
                    transaction_fee: Amount::zero(),
                    trace_elements:  Vec::new(),
                    kind:            ContractInvokeErrorKind::OutOfEnergy,
                })?;

        let invoker_amount_reserved_for_nrg =
            self.parameters.calculate_energy_cost(energy_reserved);

        // Ensure the account has sufficient funds to pay for the energy.
        if account_info.balance.available() < invoker_amount_reserved_for_nrg {
            let energy_used = energy_reserved - remaining_energy;
            return Err(ContractInvokeError {
                energy_used,
                transaction_fee: self.parameters.calculate_energy_cost(energy_used),
                trace_elements: Vec::new(),
                kind: ContractInvokeErrorKind::InsufficientFunds,
            });
        }

        let contract_address = payload.address;
        let res = self.contract_invocation_worker(
            invoker,
            sender,
            energy_reserved,
            invoker_amount_reserved_for_nrg,
            payload,
            &mut remaining_energy,
        );
        let res = match res {
            Ok((result, changeset, trace_elements)) => {
                // Charge energy for contract storage. Or return an error if out
                // of energy.
                let state_changed = if matches!(result, v1::InvokeResponse::Success { .. }) {
                    let res = changeset.persist(
                        &mut remaining_energy,
                        contract_address,
                        &mut self.accounts,
                        &mut self.contracts,
                    );
                    res.map_err(|_| self.invocation_out_of_energy_error(energy_reserved))?
                } else {
                    // An error occurred, so state hasn't changed.
                    false
                };
                self.contract_invocation_process_response(
                    result,
                    trace_elements,
                    energy_reserved,
                    remaining_energy,
                    state_changed,
                )
            }
            Err(e) => Err(e),
        };

        let transaction_fee = match &res {
            Ok(s) => s.transaction_fee,
            Err(e) => e.transaction_fee,
        };
        // Charge for execution.
        self.account_mut(invoker)
            .expect("existence already checked")
            .balance
            .total -= transaction_fee;
        res
    }

    /// Invoke a contract by calling an entrypoint.
    ///
    /// Similar to [`Chain::contract_update`](Self::contract_update) except that
    /// all changes are discarded afterwards. Typically used for "view"
    /// functions.
    ///
    /// **Parameters:**
    ///  - `invoker`: the account paying for the transaction.
    ///  - `sender`: the sender of the transaction, can also be a contract.
    ///  - `contract_address`: the contract to update.
    ///  - `entrypoint`: the entrypoint to call.
    ///  - `parameter`: the contract parameter.
    ///  - `amount`: the amount sent to the contract.
    ///  - `energy_reserved`: the maximum energy that can be used in the update.
    pub fn contract_invoke(
        &self,
        invoker: AccountAddress,
        sender: Address,
        energy_reserved: Energy,
        payload: UpdateContractPayload,
    ) -> Result<ContractInvokeSuccess, ContractInvokeError> {
        // Ensure the sender exists.
        if !self.address_exists(sender) {
            return Err(ContractInvokeError {
                energy_used:     Energy::from(0),
                transaction_fee: Amount::zero(),
                trace_elements:  Vec::new(),
                kind:            ContractInvokeErrorKind::SenderDoesNotExist(sender),
            });
        }

        let Some(account_info) = self.accounts.get(&invoker.into()) else {
            return Err(ContractInvokeError {
                energy_used:     Energy::from(0),
                transaction_fee: Amount::zero(),
                trace_elements:  Vec::new(),
                kind:            ContractInvokeErrorKind::InvokerDoesNotExist(
                    AccountDoesNotExist { address: invoker },
                ),
            });
        };

        let invoker_amount_reserved_for_nrg =
            self.parameters.calculate_energy_cost(energy_reserved);

        if account_info.balance.available() < invoker_amount_reserved_for_nrg {
            let energy_used = Energy::from(0);
            return Err(ContractInvokeError {
                energy_used,
                transaction_fee: self.parameters.calculate_energy_cost(energy_used),
                trace_elements: Vec::new(),
                kind: ContractInvokeErrorKind::InsufficientFunds,
            });
        }

        let mut remaining_energy = energy_reserved;

        let contract_address = payload.address;

        let res = self.contract_invocation_worker(
            invoker,
            sender,
            energy_reserved,
            invoker_amount_reserved_for_nrg,
            payload,
            &mut remaining_energy,
        );
        match res {
            Ok((result, changeset, trace_elements)) => {
                // Charge energy for contract storage. Or return an error if out
                // of energy.
                let state_changed = if matches!(result, v1::InvokeResponse::Success { .. }) {
                    changeset
                        .collect_energy_for_state(&mut remaining_energy, contract_address)
                        .map_err(|_| self.invocation_out_of_energy_error(energy_reserved))?
                } else {
                    // An error occurred, so state hasn't changed.
                    false
                };
                self.contract_invocation_process_response(
                    result,
                    trace_elements,
                    energy_reserved,
                    remaining_energy,
                    state_changed,
                )
            }
            Err(e) => Err(e),
        }
    }

    /// Create an account.
    ///
    /// If an account with a matching address already exists this method will
    /// replace it and return the old account.
    ///
    /// Note that if the first 29-bytes of an account are identical, then
    /// they are *considered aliases* on each other in all methods.
    /// See the example below:
    ///
    /// ```
    /// # use concordium_smart_contract_testing::*;
    /// let mut chain = Chain::new();
    /// let acc = AccountAddress([
    ///     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ///     0, 0,
    /// ]);
    /// let acc_alias = AccountAddress([
    ///     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    ///     2, 3, // Only last three bytes differ.
    /// ]);
    ///
    /// chain.create_account(Account::new(acc, Amount::from_ccd(123)));
    /// assert_eq!(
    ///     chain.account_balance_available(acc_alias), // Using the alias for lookup.
    ///     Some(Amount::from_ccd(123))
    /// );
    /// ```
    pub fn create_account(&mut self, account: Account) -> Option<Account> {
        self.accounts.insert(account.address.into(), account)
    }

    /// Create a contract address by giving it the next available index.
    fn create_contract_address(&mut self) -> ContractAddress {
        let index = self.next_contract_index;
        let subindex = 0;
        self.next_contract_index += 1;
        ContractAddress::new(index, subindex)
    }

    /// Returns the balance of an account if it exists.
    pub fn account_balance(&self, address: AccountAddress) -> Option<AccountBalance> {
        self.accounts.get(&address.into()).map(|ai| ai.balance)
    }

    /// Returns the available balance of an account if it exists.
    pub fn account_balance_available(&self, address: AccountAddress) -> Option<Amount> {
        self.accounts
            .get(&address.into())
            .map(|ai| ai.balance.available())
    }

    /// Returns the balance of an contract if it exists.
    pub fn contract_balance(&self, address: ContractAddress) -> Option<Amount> {
        self.contracts.get(&address).map(|ci| ci.self_balance)
    }

    /// Helper method for looking up part of the state of a smart contract,
    /// which is a key-value store.
    pub fn contract_state_lookup(&self, address: ContractAddress, key: &[u8]) -> Option<Vec<u8>> {
        let mut loader = v1::trie::Loader::new(&[][..]);
        self.contracts.get(&address)?.state.lookup(&mut loader, key)
    }

    /// Return a clone of the [`ContractModule`] (which has an `Arc` around the
    /// artifact so cloning is cheap).
    fn contract_module(
        &self,
        module_ref: ModuleReference,
    ) -> Result<ContractModule, ModuleDoesNotExist> {
        let module = self.modules.get(&module_ref).ok_or(ModuleDoesNotExist {
            module_reference: module_ref,
        })?;
        Ok(module.clone())
    }

    /// Returns an immutable reference to an [`Account`].
    pub fn account(&self, address: AccountAddress) -> Result<&Account, AccountDoesNotExist> {
        self.accounts
            .get(&address.into())
            .ok_or(AccountDoesNotExist { address })
    }

    /// Returns a mutable reference to [`Account`].
    fn account_mut(
        &mut self,
        address: AccountAddress,
    ) -> Result<&mut Account, AccountDoesNotExist> {
        self.accounts
            .get_mut(&address.into())
            .ok_or(AccountDoesNotExist { address })
    }

    /// Check whether an [`Account`] exists.
    pub fn account_exists(&self, address: AccountAddress) -> bool {
        self.accounts.contains_key(&address.into())
    }

    /// Check whether a [`Contract`] exists.
    pub fn contract_exists(&self, address: ContractAddress) -> bool {
        self.contracts.contains_key(&address)
    }

    /// Check whether an object with the [`Address`] exists.
    ///
    /// That is, if it is an account address, whether the account exists,
    /// and if it is a contract address, whether the contract exists.
    fn address_exists(&self, address: Address) -> bool {
        match address {
            Address::Account(acc) => self.account_exists(acc),
            Address::Contract(contr) => self.contract_exists(contr),
        }
    }

    /// Convert a [`ContractInvokeErrorKind`] to a
    /// [`ContractInvokeError`] by calculating the `energy_used` and
    /// `transaction_fee`.
    ///
    /// If the `kind` is an out of energy, then `0` is used instead of the
    /// `remaining_energy` parameter, as it will likely not be `0` due to short
    /// circuiting during execution.
    fn convert_to_invoke_error(
        &self,
        kind: ContractInvokeErrorKind,
        trace_elements: Vec<DebugTraceElement>,
        energy_reserved: Energy,
        remaining_energy: Energy,
    ) -> ContractInvokeError {
        let remaining_energy = if matches!(kind, ContractInvokeErrorKind::OutOfEnergy) {
            0.into()
        } else {
            remaining_energy
        };
        let energy_used = energy_reserved - remaining_energy;
        let transaction_fee = self.parameters.calculate_energy_cost(energy_used);
        ContractInvokeError {
            energy_used,
            transaction_fee,
            trace_elements,
            kind,
        }
    }

    /// Construct a [`ContractInvokeErrorKind`] of the `OutOfEnergy` kind with
    /// the energy and transaction fee fields based on the `energy_reserved`
    /// parameter.
    fn invocation_out_of_energy_error(&self, energy_reserved: Energy) -> ContractInvokeError {
        self.convert_to_invoke_error(
            ContractInvokeErrorKind::OutOfEnergy,
            Vec::new(),
            energy_reserved,
            Energy::from(0),
        )
    }

    /// Convert a [`ContractInitErrorKind`] to a
    /// [`ContractInitError`] by calculating the `energy_used` and
    /// `transaction_fee`.
    fn convert_to_init_error(
        &self,
        kind: ContractInitErrorKind,
        energy_reserved: Energy,
        remaining_energy: Energy,
    ) -> ContractInitError {
        let energy_used = energy_reserved - remaining_energy;
        let transaction_fee = self.parameters.calculate_energy_cost(energy_used);
        ContractInitError {
            energy_used,
            transaction_fee,
            kind,
        }
    }

    /// Try to set the exchange rates on the chain.
    ///
    /// Will fail if they result in the cost of one energy being larger than
    /// `u64::MAX / 100_000_000_000`.
    pub fn set_exchange_rates(
        &mut self,
        micro_ccd_per_euro: ExchangeRate,
        euro_per_energy: ExchangeRate,
    ) -> Result<(), ExchangeRateError> {
        // Ensure the exchange rates are within a valid range.
        check_exchange_rates(euro_per_energy, micro_ccd_per_euro)?;
        self.parameters.micro_ccd_per_euro = micro_ccd_per_euro;
        self.parameters.euro_per_energy = euro_per_energy;
        Ok(())
    }

    /// Get the microCCD per euro and euro per energy exchange rates by querying
    /// an external node using the external query block.
    fn get_exchange_rates_via_external_node(&self) -> Result<ExchangeRates, ExternalNodeError> {
        let connection = self.external_node_connection()?;

        // Get the values from the external node.
        connection.with_client(None, |block_identifier, mut client| async move {
            let (euro_per_energy, micro_ccd_per_euro) = match client
                .get_block_chain_parameters(block_identifier)
                .await?
                .response
            {
                sdk::v2::ChainParameters::V0(p) => (p.euro_per_energy, p.micro_ccd_per_euro),
                sdk::v2::ChainParameters::V1(p) => (p.euro_per_energy, p.micro_ccd_per_euro),
                sdk::v2::ChainParameters::V2(p) => (p.euro_per_energy, p.micro_ccd_per_euro),
            };
            Ok(ExchangeRates {
                euro_per_energy,
                micro_ccd_per_euro,
            })
        })
    }

    /// Tick the block time on the [`Chain`] by a [`Duration`].
    ///
    /// Returns an error if ticking causes the block time to overflow.
    ///
    /// # Example
    ///
    /// ```
    /// # use concordium_smart_contract_testing::*;
    ///
    /// // Block time defaults to 0.
    /// let mut chain = Chain::new();
    ///
    /// // Increase block time by 123 milliseconds.
    /// chain.tick_block_time(Duration::from_millis(123)).unwrap();
    ///
    /// // Block time has now increased.
    /// assert_eq!(chain.block_time(), Timestamp::from_timestamp_millis(123));
    /// ```
    pub fn tick_block_time(&mut self, duration: Duration) -> Result<(), BlockTimeOverflow> {
        self.parameters.block_time = self
            .parameters
            .block_time
            .checked_add(duration)
            .ok_or(BlockTimeOverflow)?;
        Ok(())
    }

    /// Set the block time by querying the external node.
    ///
    /// The default query block is always used.
    ///
    /// The external node must be setup prior to this call via the method
    /// [`Chain::setup_external_node_connection`], otherwise an error is
    /// returned.
    fn set_block_time_via_external_node(&mut self) -> Result<(), ExternalNodeError> {
        let connection = self.external_node_connection_mut()?;

        // Get the timestamp in milliseconds.
        let timestamp =
            connection.with_client(None, |block_identifier, mut client| async move {
                Ok(client
                    .get_block_info(block_identifier)
                    .await?
                    .response
                    .block_slot_time
                    .timestamp_millis() as u64) // The node never returns
                                                // timestamps < 0, so it is safe
                                                // to cast it to `u64`.
            })?;
        // Update the block time.
        self.parameters.block_time = Timestamp::from_timestamp_millis(timestamp);

        Ok(())
    }

    /// Set up a connection to an external Concordium node.
    ///
    /// This method also queries the block info for one of two reasons:
    /// 1) If `query_block` is provided, its existence is checked.
    /// 2) Otherwise, the last final block is queried to get its blockhash which
    /// will be saved in [`ExternalNodeConnection`].
    fn setup_external_node_connection(
        &mut self,
        endpoint: Endpoint,
        query_block: Option<BlockHash>,
    ) -> Result<(), SetupExternalNodeError> {
        // Create the Tokio runtime. This should never fail, unless nested runtimes are
        // created.
        let runtime = runtime::Builder::new_multi_thread()
            // Enable time, so timeouts can be used.
            .enable_time()
            // Enable I/O, so networking and other types of calls are possible.
            .enable_io()
            .build()
            .expect("Internal error: Could not create Tokio runtime.");

        // A future for getting the client. Executed below.
        let get_client = async {
            // Try to create the client, which also checks that the connection is valid.
            let client = sdk::v2::Client::new(endpoint).await?;
            Ok::<sdk::v2::Client, SetupExternalNodeError>(client)
        };

        // A future for checking the block.
        let get_block_info = |mut client: sdk::v2::Client| async move {
            let block_identifier = if let Some(query_block) = query_block {
                sdk::v2::BlockIdentifier::Given(query_block)
            } else {
                sdk::v2::BlockIdentifier::LastFinal
            };

            let block_hash = match client.get_block_info(block_identifier).await {
                Ok(res) => res.block_hash,
                Err(sdk::v2::QueryError::NotFound) => {
                    return Err(SetupExternalNodeError::QueryBlockDoesNotExist {
                        // It should never be possible to get `NotFound` when querying `LastFinal`,
                        // and so, the `query_block` must be `Some`.
                        query_block: query_block.expect(
                            "Internal error: Got `QueryError::NotFound` for when querying last \
                             final block.",
                        ),
                    });
                }
                Err(sdk::v2::QueryError::RPCError(error)) => {
                    return Err(SetupExternalNodeError::CannotCheckQueryBlockExistence { error })
                }
            };
            Ok(block_hash)
        };

        // Get the client synchronously by blocking until the async returns.
        let (client, checked_query_block) = runtime.block_on(async {
            let client = timeout(EXTERNAL_NODE_CONNECT_TIMEOUT, get_client)
                .await
                .map_err(|_| SetupExternalNodeError::ConnectTimeout)??;
            let checked_query_block =
                timeout(EXTERNAL_NODE_QUERY_TIMEOUT, get_block_info(client.clone()))
                    .await
                    .map_err(|_| SetupExternalNodeError::CheckQueryBlockTimeout)??;
            Ok::<_, SetupExternalNodeError>((client, checked_query_block))
        })?;

        // Set or replace the node connection.
        self.external_node_connection = Some(ExternalNodeConnection {
            client,
            runtime,
            query_block: checked_query_block,
        });

        Ok(())
    }

    /// Try to get a mutable reference to [`ExternalNodeConnection`] or return
    /// an error.
    ///
    /// The connection is only available, if the [`Chain`] has been set up with
    /// an external node connection via
    /// [`ChainBuilder::external_node_connection`] in the [`ChainBuilder`].
    fn external_node_connection_mut(
        &mut self,
    ) -> Result<&mut ExternalNodeConnection, ExternalNodeNotConfigured> {
        match &mut self.external_node_connection {
            None => Err(ExternalNodeNotConfigured),
            Some(data) => Ok(data),
        }
    }

    /// Try to get an immutable reference to [`ExternalNodeConnection`] or
    /// return an error.
    ///
    /// The connection is only available, if the [`Chain`] has been set up with
    /// an external node connection via
    /// [`ChainBuilder::external_node_connection`] in the [`ChainBuilder`].
    fn external_node_connection(
        &self,
    ) -> Result<&ExternalNodeConnection, ExternalNodeNotConfigured> {
        match &self.external_node_connection {
            None => Err(ExternalNodeNotConfigured),
            Some(data) => Ok(data),
        }
    }

    /// Return the current microCCD per euro exchange rate.
    pub fn micro_ccd_per_euro(&self) -> ExchangeRate { self.parameters.micro_ccd_per_euro }

    /// Return the current euro per energy exchange rate.
    pub fn euro_per_energy(&self) -> ExchangeRate { self.parameters.euro_per_energy }

    /// Return the current block time.
    pub fn block_time(&self) -> Timestamp { self.parameters.block_time }

    /// Return the block used for external queries by default.
    ///
    /// The block can be set with [`ChainBuilder::external_query_block`] when
    /// building the [`Chain`].
    ///
    /// This method returns an error if the external node has not been
    /// configured.
    pub fn external_query_block(&self) -> Result<BlockHash, ExternalNodeNotConfigured> {
        self.external_node_connection().map(|conn| conn.query_block)
    }
}

impl ExternalNodeConnection {
    /// Execute an async task with the [`sdk::v2::Client`].
    ///
    /// If a block is provided, it will be used for the query. Otherwise, it
    /// will use the default query block.
    ///
    /// If the task takes longer than [`EXTERNAL_NODE_TIMEOUT_DURATION`] then
    /// the connection times out and an [`Err(ExternalNodeError::Timeout)`] is
    /// returned.
    ///
    /// *This method cannot be nested, as that will cause a panic.*
    fn with_client<T, F, Fut>(
        &self,
        block: Option<BlockHash>,
        f: F,
    ) -> Result<T, ExternalNodeError>
    where
        F: FnOnce(sdk::v2::BlockIdentifier, sdk::v2::Client) -> Fut,
        Fut: Future<Output = Result<T, ExternalNodeError>>, {
        // Get the block identifier, either using the provided block or the default
        // query block.
        let block_identifier = if let Some(block) = block {
            sdk::v2::BlockIdentifier::Given(block)
        } else {
            sdk::v2::BlockIdentifier::Given(self.query_block)
        };
        // Clone the client so it can be moved to the async block.
        let client = self.client.clone();
        // Run the future and timeout if it takes too long.
        self.runtime.block_on(async move {
            timeout(EXTERNAL_NODE_QUERY_TIMEOUT, f(block_identifier, client))
                .await
                .map_err(|_| ExternalNodeError::QueryTimeout)?
        })
    }
}

impl Account {
    /// Create new [`Account`](Self) with the provided account policy and keys.
    pub fn new_with_policy_and_keys(
        address: AccountAddress,
        balance: AccountBalance,
        policy: OwnedPolicy,
        keys: AccountAccessStructure,
    ) -> Self {
        Self {
            balance,
            policy,
            address,
            keys,
        }
    }

    /// Create new [`Account`](Self) with the provided account keys and balance.
    /// See [`new`][Self::new] for what the default policy is.
    pub fn new_with_keys(
        address: AccountAddress,
        balance: AccountBalance,
        keys: AccountAccessStructure,
    ) -> Self {
        Self {
            balance,
            policy: Self::empty_policy(),
            address,
            keys,
        }
    }

    /// Create new [`Account`](Self) with the provided account policy.
    /// The account keys are initialized with an [`AccountAccessStructure`]
    /// with a threshold of 1, and no keys. So it is impossible to verify any
    /// signatures with the access structure.
    pub fn new_with_policy(
        address: AccountAddress,
        balance: AccountBalance,
        policy: OwnedPolicy,
    ) -> Self {
        Self::new_with_policy_and_keys(address, balance, policy, AccountAccessStructure {
            threshold: AccountThreshold::try_from(1u8).expect("1 is a valid threshold."),
            keys:      BTreeMap::new(),
        })
    }

    /// Create a new [`Account`](Self) with the provided balance and a default
    /// account policy and default account access structure.
    ///
    /// See [`new`][Self::new] for what the default policy is.
    pub fn new_with_balance(address: AccountAddress, balance: AccountBalance) -> Self {
        Self::new_with_policy(address, balance, Self::empty_policy())
    }

    /// Create new [`Account`](Self) with the provided total balance.
    ///
    /// The `policy` will have:
    ///   - `identity_provider`: 0,
    ///   - `created_at`: unix epoch,
    ///   - `valid_to`: unix epoch + `u64::MAX` milliseconds,
    ///   - `items`: none,
    ///
    /// The account keys are initialized with an [`AccountAccessStructure`]
    /// with a threshold of 1, and no keys. So it is impossible to verify any
    /// signatures with the access structure.
    ///
    /// The [`AccountBalance`] will be created with the provided
    /// `total_balance`.
    pub fn new(address: AccountAddress, total_balance: Amount) -> Self {
        Self::new_with_policy(
            address,
            AccountBalance {
                total:  total_balance,
                staked: Amount::zero(),
                locked: Amount::zero(),
            },
            Self::empty_policy(),
        )
    }

    /// Helper for creating an empty policy.
    ///
    /// It has identity provider `0`, no items, and is valid from unix epoch
    /// until unix epoch + u64::MAX milliseconds.
    fn empty_policy() -> OwnedPolicy {
        OwnedPolicy {
            identity_provider: 0,
            created_at:        Timestamp::from_timestamp_millis(0),
            valid_to:          Timestamp::from_timestamp_millis(u64::MAX),
            items:             Vec::new(),
        }
    }
}

/// Load a raw wasm module, i.e. one **without** the prefix of 4 version
/// bytes and 4 module length bytes.
/// The module still has to be a valid V1 smart contract module.
pub fn module_load_v1_raw(module_path: impl AsRef<Path>) -> Result<WasmModule, ModuleLoadError> {
    let module_path = module_path.as_ref();
    // To avoid reading a giant file, we open the file for reading, check its size
    // and then load the contents.
    let (mut reader, metadata) = std::fs::File::open(module_path)
        .and_then(|reader| reader.metadata().map(|metadata| (reader, metadata)))
        .map_err(|e| ModuleLoadError {
            path: module_path.to_path_buf(),
            kind: e.into(),
        })?;
    if metadata.len() > MAX_WASM_MODULE_SIZE.into() {
        return Err(ModuleLoadError {
            path: module_path.to_path_buf(),
            kind: ModuleLoadErrorKind::ReadModule(
                anyhow!("Maximum size of a Wasm module is {}", MAX_WASM_MODULE_SIZE).into(),
            ),
        });
    }
    // We cannot deserialize directly to [`ModuleSource`] as it expects the first
    // four bytes to be the length, which it isn't for this raw file.
    let mut buffer = Vec::new();
    std::io::Read::read_to_end(&mut reader, &mut buffer).map_err(|e| ModuleLoadError {
        path: module_path.to_path_buf(),
        kind: ModuleLoadErrorKind::OpenFile(e), /* This is unlikely to happen, since
                                                 * we already opened it. */
    })?;
    Ok(WasmModule {
        version: WasmVersion::V1,
        source:  ModuleSource::from(buffer),
    })
}

/// Load a v1 wasm module as it is output from `cargo concordium build`,
/// i.e. **including** the prefix of 4 version bytes and 4 module length
/// bytes.
pub fn module_load_v1(module_path: impl AsRef<Path>) -> Result<WasmModule, ModuleLoadError> {
    let module_path = module_path.as_ref();
    // To avoid reading a giant file, we just open the file for reading and then
    // parse it as a wasm module, which checks the length up front.
    let mut reader = std::fs::File::open(module_path).map_err(|e| ModuleLoadError {
        path: module_path.to_path_buf(),
        kind: e.into(),
    })?;
    let module: WasmModule =
        concordium_base::common::from_bytes(&mut reader).map_err(|e| ModuleLoadError {
            path: module_path.to_path_buf(),
            kind: ModuleLoadErrorKind::ReadModule(e.into()),
        })?;
    if module.version != WasmVersion::V1 {
        return Err(ModuleLoadError {
            path: module_path.to_path_buf(),
            kind: ModuleLoadErrorKind::UnsupportedModuleVersion(module.version),
        });
    }
    Ok(module)
}

impl Signer {
    /// Create a signer which always signs with one key.
    pub const fn with_one_key() -> Self { Self { num_keys: 1 } }

    /// Create a signer with a non-zero number of keys.
    pub const fn with_keys(num_keys: u32) -> Result<Self, ZeroKeysError> {
        if num_keys == 0 {
            return Err(ZeroKeysError);
        }
        Ok(Self { num_keys })
    }
}

impl ContractInvokeError {
    /// Try to extract the value returned.
    ///
    /// This only returns `Some` if the contract rejected on its own.
    /// As opposed to when it runs out of energy, traps, or similar, in which
    /// case there won't be a return value.
    pub fn return_value(&self) -> Option<&[u8]> {
        match &self.kind {
            ContractInvokeErrorKind::ExecutionError {
                failure_kind: v1::InvokeFailure::ContractReject { data, .. },
            } => Some(data),
            _ => None,
        }
    }
}

impl From<InsufficientEnergy> for ContractInitErrorKind {
    #[inline(always)]
    fn from(_: InsufficientEnergy) -> Self { Self::OutOfEnergy }
}

impl From<TestConfigurationError> for ContractInvokeErrorKind {
    fn from(err: TestConfigurationError) -> Self {
        match err {
            TestConfigurationError::OutOfEnergy => Self::OutOfEnergy,
            TestConfigurationError::BalanceOverflow => Self::BalanceOverflow,
        }
    }
}

/// Convert [`Energy`] to [`InterpreterEnergy`] by multiplying by `1000`.
pub(crate) fn to_interpreter_energy(energy: Energy) -> InterpreterEnergy {
    InterpreterEnergy::from(energy.energy * 1000)
}

/// Convert [`InterpreterEnergy`] to [`Energy`] by dividing by `1000`.
pub(crate) fn from_interpreter_energy(interpreter_energy: InterpreterEnergy) -> Energy {
    Energy::from(interpreter_energy.energy / 1000)
}

/// Calculate the energy for looking up a [`ContractModule`].
pub(crate) fn lookup_module_cost(module: &ContractModule) -> Energy {
    // The ratio is from Concordium/Cost.hs::lookupModule
    Energy::from(module.size / 50)
}

/// Calculate the microCCD(mCCD) cost of energy(NRG) using the two exchange
/// rates provided.
///
/// To find the mCCD/NRG exchange rate:
/// ```markdown
///  euro     mCCD   euro * mCCD   mCCD
///  ----  *  ---- = ----------- = ----
///  NRG      euro   NRG * euro    NRG
/// ```
///
/// To convert the `energy` parameter to mCCD (the vertical lines represent
/// ceiling):
/// ```markdown
/// ⌈       mCCD  ⌉    ⌈ NRG * mCCD ⌉
/// | NRG * ----  | = | ---------- | = mCCD
/// |       NRG   |   |    NRG     |
/// ```
pub fn energy_to_amount(
    energy: Energy,
    euro_per_energy: ExchangeRate,
    micro_ccd_per_euro: ExchangeRate,
) -> Amount {
    let micro_ccd_per_energy_numerator: BigUint =
        BigUint::from(euro_per_energy.numerator()) * micro_ccd_per_euro.numerator();
    let micro_ccd_per_energy_denominator: BigUint =
        BigUint::from(euro_per_energy.denominator()) * micro_ccd_per_euro.denominator();
    let cost: BigUint = (micro_ccd_per_energy_numerator * energy.energy)
        .div_ceil(&micro_ccd_per_energy_denominator);
    let cost: u64 = u64::try_from(cost).expect(
        "Should never overflow since reasonable exchange rates are ensured when constructing the \
         [`Chain`].",
    );
    Amount::from_micro_ccd(cost)
}

/// Helper function that checks the validity of the exchange rates.
///
/// More specifically, it checks that the cost of one energy is <= `u64::MAX /
/// `100_000_000_000`, which ensures that overflows won't occur.
fn check_exchange_rates(
    euro_per_energy: ExchangeRate,
    micro_ccd_per_euro: ExchangeRate,
) -> Result<(), ExchangeRateError> {
    let micro_ccd_per_energy_numerator: BigUint =
        BigUint::from(euro_per_energy.numerator()) * micro_ccd_per_euro.numerator();
    let micro_ccd_per_energy_denominator: BigUint =
        BigUint::from(euro_per_energy.denominator()) * micro_ccd_per_euro.denominator();
    let max_allowed_micro_ccd_to_energy = u64::MAX / 100_000_000_000u64;
    let micro_ccd_per_energy =
        u64::try_from(micro_ccd_per_energy_numerator / micro_ccd_per_energy_denominator)
            .map_err(|_| ExchangeRateError)?;
    if micro_ccd_per_energy > max_allowed_micro_ccd_to_energy {
        return Err(ExchangeRateError);
    }
    Ok(())
}

/// A helper function for converting `[v0::Logs]` into [`Vec<ContractEvent>`].
pub(crate) fn contract_events_from_logs(logs: v0::Logs) -> Vec<ContractEvent> {
    logs.logs.into_iter().map(ContractEvent::from).collect()
}

impl From<ExternalNodeNotConfigured> for ExternalNodeError {
    fn from(_: ExternalNodeNotConfigured) -> Self { Self::NotConfigured }
}

impl From<ExchangeRateError> for ChainBuilderError {
    fn from(_: ExchangeRateError) -> Self { Self::ExchangeRateError }
}

#[cfg(test)]
mod tests {
    use concordium_base::base::AccountAddressEq;

    use super::*;

    /// A few checks that test whether the function behavior matches its doc
    /// comments.
    #[test]
    fn check_exchange_rates_works() {
        let max_allowed_micro_ccd_per_energy = u64::MAX / 100_000_000_000;
        check_exchange_rates(
            ExchangeRate::new_unchecked(max_allowed_micro_ccd_per_energy + 1, 1),
            ExchangeRate::new_unchecked(1, 1),
        )
        .expect_err("should fail");

        check_exchange_rates(
            ExchangeRate::new_unchecked(max_allowed_micro_ccd_per_energy / 2 + 1, 1),
            ExchangeRate::new_unchecked(2, 1),
        )
        .expect_err("should fail");

        check_exchange_rates(
            ExchangeRate::new_unchecked(max_allowed_micro_ccd_per_energy, 1),
            ExchangeRate::new_unchecked(1, 1),
        )
        .expect("should succeed");

        check_exchange_rates(
            ExchangeRate::new_unchecked(50000, 1),
            ExchangeRate::new_unchecked(1, 50000),
        )
        .expect("should succeed");
    }

    /// Test that account aliases are seen as one account.
    #[test]
    fn test_account_aliases() {
        let mut chain = Chain::new();
        let acc = AccountAddress([
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ]);
        let acc_alias = AccountAddress([
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            1, 2, 3, // Last three bytes can differ for aliases.
        ]);
        let acc_other = AccountAddress([
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
            2, 3, 4, // This differs on last four bytes, so it is a different account.
        ]);
        let acc_eq: AccountAddressEq = acc.into();
        let acc_alias_eq: AccountAddressEq = acc_alias.into();
        let acc_other_eq: AccountAddressEq = acc_other.into();

        let expected_amount = Amount::from_ccd(10);
        let expected_amount_other = Amount::from_ccd(123);

        chain.create_account(Account::new(acc, expected_amount));
        chain.create_account(Account::new(acc_other, expected_amount_other));

        assert_eq!(acc_eq, acc_alias_eq);
        assert_ne!(acc_eq, acc_other_eq);

        assert_eq!(acc_eq.cmp(&acc_alias_eq), std::cmp::Ordering::Equal);
        assert_eq!(acc_eq.cmp(&acc_other_eq), std::cmp::Ordering::Less);

        assert_eq!(
            chain.account_balance_available(acc_alias),
            Some(expected_amount)
        );
        assert_eq!(
            chain.account_balance_available(acc_other),
            Some(expected_amount_other)
        );
    }

    /// Test that building a chain with valid parameters succeeds.
    ///
    /// This test does *not* include external node endpoint, see
    /// [`test_chain_builder_with_valid_parameters_and_with_io`] for the reason.
    #[test]
    fn test_chain_builder_with_valid_parameters() {
        let micro_ccd_per_euro = ExchangeRate::new_unchecked(123, 1);
        let euro_per_energy = ExchangeRate::new_unchecked(1, 1234);
        let block_time = Timestamp::from_timestamp_millis(12345);
        let chain = Chain::builder()
            .micro_ccd_per_euro(micro_ccd_per_euro)
            .euro_per_energy(euro_per_energy)
            .block_time(block_time)
            .build()
            .unwrap();

        assert_eq!(chain.micro_ccd_per_euro(), micro_ccd_per_euro);
        assert_eq!(chain.euro_per_energy(), euro_per_energy);
        assert_eq!(chain.block_time(), block_time);
    }

    /// Test that building a chain with exchange rates that are out of bounds
    /// fails with the right error.
    #[test]
    fn test_chain_builder_with_invalid_exchange_rates() {
        let micro_ccd_per_euro = ExchangeRate::new_unchecked(1000000, 1);
        let euro_per_energy = ExchangeRate::new_unchecked(100000000, 1);
        let error = Chain::builder()
            .micro_ccd_per_euro(micro_ccd_per_euro)
            .euro_per_energy(euro_per_energy)
            .build()
            .unwrap_err();

        assert!(matches!(error, ChainBuilderError::ExchangeRateError));
    }
}

/// Tests that use I/O (network) and should therefore *not* be run in the CI.
///
/// To skip the tests use `cargo test -- --skip io_tests`
#[cfg(test)]
mod io_tests {
    use super::*;

    /// Test that building a chain using the external node parameters works.
    #[test]
    fn test_chain_builder_with_valid_parameters_and_external_node() {
        let chain = Chain::builder()
            .micro_ccd_per_euro_from_external()
            .euro_per_energy_from_external()
            .external_query_block(
                "45c53a19cd782a8de981941feb5e0f875cefaba8d2cda958e76f471a4710a797" // A block from testnet.
                    .parse()
                    .unwrap(),
            )
            .external_node_connection(Endpoint::from_static(
                "http://node.testnet.concordium.com:20000",
            ))
            .block_time_from_external()
            .build()
            .unwrap();

        // These values are queried manually from the node.
        assert_eq!(
            chain.micro_ccd_per_euro(),
            ExchangeRate::new_unchecked(10338559485590134784, 79218205097)
        );
        assert_eq!(
            chain.euro_per_energy(),
            ExchangeRate::new_unchecked(1, 50000)
        );
        assert_eq!(
            chain.block_time(),
            Timestamp::from_timestamp_millis(1687865059500)
        );
    }

    /// Test that the correct error is returned when an unknown query block is
    /// given.
    ///
    /// The block used is one from mainnet, which is extremely unlikely to also
    /// appear on testnet.
    #[test]
    fn test_block_time_from_unknown_block() {
        let err = Chain::builder()
            .external_node_connection(Endpoint::from_static(
                "http://node.testnet.concordium.com:20000",
            ))
            .external_query_block(
                "4f38c7e63645c59e9bf32f7ca837a029810b21c439f7492c3cebe229a2e3ea07"
                    .parse()
                    .unwrap(), // A block from mainnet.
            )
            .build()
            .unwrap_err();
        assert!(matches!(err, ChainBuilderError::SetupExternalNodeError {
            error: SetupExternalNodeError::CannotCheckQueryBlockExistence { .. },
        }));
    }
}
