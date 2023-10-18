use anyhow::{bail, Context, Error};
use concordium_rust_sdk::{
    common::types::TransactionTime,
    id::types::AccountAddress,
    smart_contracts::{common::ModuleReference, types::DEFAULT_INVOKE_ENERGY},
    types::{
        hashes::TransactionHash,
        queries::AccountNonceResponse,
        smart_contracts::{ContractContext, InvokeContractResult, WasmModule},
        transactions::{
            self,
            send::{deploy_module, init_contract, GivenEnergy},
            InitContractPayload, UpdateContractPayload,
        },
        AccountTransactionEffects, BlockItemSummary, BlockItemSummaryDetails, ContractAddress,
        Energy, TransactionType, WalletAccount,
    },
    v2::{self, BlockIdentifier},
};
use std::{path::Path, sync::Arc};

/// A struct containing connection and wallet information.
#[derive(Debug)]
pub struct Deployer {
    /// The client to establish a connection to a Concordium node (V2 API).
    pub client: v2::Client,
    /// The account keys to be used for sending transactions.
    pub key: Arc<WalletAccount>,
}

/// A struct containing the return values of the `deploy_wasm_module` function.
/// If the module does not exist on the chain, it is deployed by the `deploy_wasm_module`
/// function and the transaction hash, the block item, and the module reference are returned.
/// If the module already exists on the chain, no deployment transaction is sent and only the
/// module reference is returned.
#[derive(Debug)]
pub enum DeployResult {
    /// Module is deployed with a deployment transaction.
    ModuleDeployed(Box<ModuleDeployedResult>),
    /// Module already exists on the chain.
    ModuleExists(ModuleReference),
}

/// A struct containing part of the return values of the `deploy_wasm_module` function.
#[derive(Debug)]
pub struct ModuleDeployedResult {
    /// The transaction hash of the deployment transaction.
    pub tx_hash: TransactionHash,
    /// The block_item of the deployment transaction.
    pub block_item: BlockItemSummary,
    /// The module reference of the wasm module.
    pub module_reference: ModuleReference,
}

/// A struct containing the return values of the `init_contract` function.
#[derive(Debug)]
pub struct InitResult {
    /// The transaction hash of the initialization transaction.
    pub tx_hash: TransactionHash,
    /// The block_item of the initialization transaction.
    pub block_item: BlockItemSummary,
    /// The contract address of the smart contract instance.
    pub contract_address: ContractAddress,
}

impl Deployer {
    /// A function to create a new deployer instance from a network client and a path to the wallet.
    pub fn new(client: v2::Client, wallet_account_file: &Path) -> Result<Deployer, Error> {
        let key_data = WalletAccount::from_json_file(wallet_account_file)
            .context("Unable to read wallet file.")?;

        Ok(Deployer {
            client,
            key: key_data.into(),
        })
    }

    /// A function to check if a module exists on the chain.
    pub async fn module_exists(
        &mut self,
        module_reference: &ModuleReference,
    ) -> Result<bool, Error> {
        let module_src = self
            .client
            .get_module_source(module_reference, &BlockIdentifier::LastFinal)
            .await;

        match module_src {
            Ok(_) => Ok(true),
            Err(e) if e.is_not_found() => Ok(false),
            Err(e) => Err(e.into()),
        }
    }

    /// A function to deploy a wasm module on the chain.
    ///
    /// If successful, the transaction hash, the block item, and
    /// the module reference are returned.
    /// If the module already exists on chain, this function returns
    /// the module reference of the already deployed module.
    ///
    /// An optional expiry time for the transaction
    /// can be given. If `None` is provided, the local time + 300 seconds is
    /// used as a default expiry time.
    pub async fn deploy_wasm_module(
        &mut self,
        wasm_module: WasmModule,
        expiry: Option<TransactionTime>,
    ) -> Result<DeployResult, Error> {
        println!("\nDeploying module....");

        let module_reference = wasm_module.get_module_ref();

        let exists = self.module_exists(&module_reference).await?;

        if exists {
            println!(
                "Module with reference {} already exists on the chain.",
                module_reference
            );

            return Ok(DeployResult::ModuleExists(module_reference));
        }

        let nonce = self.get_nonce(self.key.address).await?;

        if !nonce.all_final {
            anyhow::bail!("Nonce not final")
        }

        let expiry = expiry.unwrap_or_else(|| {
            TransactionTime::from_seconds((chrono::Utc::now().timestamp() + 300) as u64)
        });

        let tx = deploy_module(
            &*self.key,
            self.key.address,
            nonce.nonce,
            expiry,
            wasm_module,
        );
        let bi = transactions::BlockItem::AccountTransaction(tx);

        let tx_hash = self.client.send_block_item(&bi).await?;

        println!("Sent transaction with hash: {tx_hash}");

        let (_, block_item) = self.client.wait_until_finalized(&tx_hash).await?;

        self.check_outcome_of_deploy_transaction(&block_item)?;

        println!(
            "Transaction finalized: tx_hash={} module_ref={}",
            tx_hash, module_reference,
        );

        Ok(DeployResult::ModuleDeployed(Box::from(
            ModuleDeployedResult {
                tx_hash,
                block_item,
                module_reference,
            },
        )))
    }

    /// A function to initialize a smart contract instance on the chain.
    ///
    /// If successful, the transaction hash, the block item, and the contract address are
    /// returned.
    ///
    /// An optional energy for the transaction can be given. If `None` is
    /// provided, 5000 energy is used as a default energy value. An optional
    /// expiry time for the transaction can be given. If `None` is provided,
    /// the local time + 300 seconds is used as a default expiry time.
    pub async fn init_contract(
        &mut self,
        payload: InitContractPayload,
        energy: Option<Energy>,
        expiry: Option<TransactionTime>,
    ) -> Result<InitResult, Error> {
        println!("\nInitializing contract....");

        let nonce = self.get_nonce(self.key.address).await?;

        if !nonce.all_final {
            bail!("Nonce not final")
        }

        let energy = energy.unwrap_or(Energy { energy: 5000 });

        let expiry = expiry.unwrap_or_else(|| {
            TransactionTime::from_seconds((chrono::Utc::now().timestamp() + 300) as u64)
        });

        let tx = init_contract(
            &*self.key,
            self.key.address,
            nonce.nonce,
            expiry,
            payload,
            energy,
        );

        let bi = transactions::BlockItem::AccountTransaction(tx);

        let tx_hash = self.client.send_block_item(&bi).await?;

        println!("Sent transaction with hash: {tx_hash}");

        let (_, block_item) = self.client.wait_until_finalized(&tx_hash).await?;

        let contract_address = self.check_outcome_of_initialization_transaction(&block_item)?;

        println!(
            "Transaction finalized: tx_hash={} contract=({}, {})",
            tx_hash, contract_address.index, contract_address.subindex,
        );

        Ok(InitResult {
            tx_hash,
            block_item,
            contract_address,
        })
    }

    /// A function to update a smart contract instance on the chain.
    ///
    /// If successful, the transaction
    /// hash, and the block item are returned.
    ///
    /// An optional energy for the transaction can be
    /// given. If `None` is provided, 50000 energy is used as a default energy
    /// value. An optional expiry time for the transaction can be given. If
    /// `None` is provided, the local time + 300 seconds is used as a default
    /// expiry time.
    pub async fn update_contract(
        &mut self,
        update_payload: UpdateContractPayload,
        energy: Option<GivenEnergy>,
        expiry: Option<TransactionTime>,
    ) -> Result<(TransactionHash, BlockItemSummary), Error> {
        println!("\nUpdating contract....");

        let nonce = self.get_nonce(self.key.address).await?;

        if !nonce.all_final {
            bail!("Nonce not final")
        }

        let payload = transactions::Payload::Update {
            payload: update_payload,
        };

        let expiry = expiry.unwrap_or_else(|| {
            TransactionTime::from_seconds((chrono::Utc::now().timestamp() + 300) as u64)
        });

        let energy = energy.unwrap_or(GivenEnergy::Absolute(Energy { energy: 50000 }));

        let tx = transactions::send::make_and_sign_transaction(
            &*self.key,
            self.key.address,
            nonce.nonce,
            expiry,
            energy,
            payload,
        );
        let bi = transactions::BlockItem::AccountTransaction(tx);

        let tx_hash = self.client.send_block_item(&bi).await?;

        println!("Sent transaction with hash: {tx_hash}");

        let (_, block_item) = self.client.wait_until_finalized(&tx_hash).await?;

        self.check_outcome_of_update_transaction(&block_item)?;

        println!("Transaction finalized: tx_hash={}", tx_hash,);

        Ok((tx_hash, block_item))
    }

    /// A function to estimate the energy needed to execute a transaction on the
    /// chain.
    ///
    /// If successful, the execution cost in energy is returned by this function.
    /// This function can be used to dry-run a transaction.
    ///
    /// The transaction costs on Concordium have two components, one is based on the size of the
    /// transaction and the number of signatures, and then there is a
    /// transaction-specific one for executing the transaction (which is estimated with this function).
    /// In your main deployment script, you want to use the `energy` value returned by this function
    /// and add the transaction cost of the first component before sending the transaction. `GivenEnergy::Add(energy)`
    /// is the recommended helper function to be used in the main deployment script to handle the
    /// cost for the first component automatically.
    /// [GivenEnergy](https://docs.rs/concordium-rust-sdk/latest/concordium_rust_sdk/types/transactions/construct/enum.GivenEnergy.html)
    pub async fn estimate_energy(
        &mut self,
        payload: UpdateContractPayload,
    ) -> Result<Energy, Error> {
        let context =
            ContractContext::new_from_payload(self.key.address, DEFAULT_INVOKE_ENERGY, payload);

        let result = self
            .client
            .invoke_instance(&BlockIdentifier::LastFinal, &context)
            .await?;

        match result.response {
            InvokeContractResult::Failure {
                return_value,
                reason,
                used_energy,
            } => bail!(format!(
                "Contract invoke failed: {reason:?}, used_energy={used_energy}, return \
                 value={return_value:?}"
            )),
            InvokeContractResult::Success {
                return_value: _,
                events: _,
                used_energy,
            } => Ok(used_energy),
        }
    }

    /// A function to get the next nonce of the wallet account.
    pub async fn get_nonce(
        &mut self,
        address: AccountAddress,
    ) -> Result<AccountNonceResponse, Error> {
        let nonce = self
            .client
            .get_next_account_sequence_number(&address)
            .await?;
        Ok(nonce)
    }

    /// A function that checks the outcome of the deploy transaction.
    /// It returns an error if the `block_item` is not a deploy transaction.
    /// It returns the error code if the transaction reverted.
    fn check_outcome_of_deploy_transaction(
        &self,
        block_item: &BlockItemSummary,
    ) -> Result<(), Error> {
        match &block_item.details {
            BlockItemSummaryDetails::AccountTransaction(a) => match &a.effects {
                AccountTransactionEffects::None {
                    transaction_type,
                    reject_reason,
                } => {
                    if *transaction_type != Some(TransactionType::DeployModule) {
                        bail!("Expected transaction type to be of type DeployModule but it was instead {transaction_type:?}",);
                    }

                    bail!(format!(
                        "Module deploy rejected with reason: {reject_reason:?}"
                    ))
                }
                AccountTransactionEffects::ModuleDeployed { module_ref: _ } => Ok(()),
                _ => bail!(
                    "The parsed account transaction effect should be of type `ModuleDeployed` or \
                     `None` (in case the transaction reverted)"
                ),
            },
            _ => bail!(
                "Can only parse an account transaction (no account creation transaction or chain \
                 update transaction)"
            ),
        }
    }

    /// A function that checks the outcome of the initialization transaction.
    /// It returns an error if the `block_item` is not an initialization transaction.
    /// It returns the error code if the transaction reverted.
    fn check_outcome_of_initialization_transaction(
        &self,
        block_item: &BlockItemSummary,
    ) -> Result<ContractAddress, Error> {
        match &block_item.details {
            BlockItemSummaryDetails::AccountTransaction(a) => match &a.effects {
                AccountTransactionEffects::None {
                    transaction_type,
                    reject_reason,
                } => {
                    if *transaction_type != Some(TransactionType::InitContract) {
                        bail!("Expected transaction type to be of type InitContract but it was instead {transaction_type:?}");
                    }

                    bail!(format!(
                        "Contract init rejected with reason: {reject_reason:?}"
                    ))
                }
                AccountTransactionEffects::ContractInitialized { data } => Ok(data.address),
                _ => bail!(
                    "The parsed account transaction effect should be of type \
                     `ContractInitialized` or `None` (in case the transaction reverted)"
                ),
            },
            _ => bail!(
                "Can only parse an account transaction (no account creation transaction or chain \
                 update transaction)"
            ),
        }
    }

    /// A function that checks the outcome of the update transaction.
    /// It returns an error if the `block_item` is not an update transaction.
    /// It returns the error code if the transaction reverted.
    fn check_outcome_of_update_transaction(
        &self,
        block_item: &BlockItemSummary,
    ) -> Result<(), Error> {
        match &block_item.details {
            BlockItemSummaryDetails::AccountTransaction(a) => match &a.effects {
                AccountTransactionEffects::None {
                    transaction_type,
                    reject_reason,
                } => {
                    if *transaction_type != Some(TransactionType::Update) {
                        bail!("Expected transaction type to be of type Update but it was instead {transaction_type:?}");
                    }

                    bail!(format!(
                        "Contract update rejected with reason: {reject_reason:?}"
                    ))
                }
                AccountTransactionEffects::ContractUpdateIssued { effects: _ } => Ok(()),
                _ => bail!(
                    "The parsed account transaction effect should be of type \
                     `ContractUpdateIssued` or `None` (in case the transaction reverted)"
                ),
            },
            _ => bail!(
                "Can only parse an account transaction (no account creation transaction or chain \
                 update transaction)"
            ),
        }
    }
}
