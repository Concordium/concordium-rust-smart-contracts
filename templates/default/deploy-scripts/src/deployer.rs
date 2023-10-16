use crate::DeployError;
use anyhow::Context;
use concordium_rust_sdk::smart_contracts::types::DEFAULT_INVOKE_ENERGY;
use concordium_rust_sdk::types::hashes::TransactionHash;
use concordium_rust_sdk::{
    common::types::TransactionTime,
    id::types::AccountAddress,
    smart_contracts::common::ModuleReference,
    types::{
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
use std::path::Path;

/// A struct representing a smart contract instance on the chain.
#[derive(Clone, Debug)]
pub struct ContractInitialized {
    /// Smart contract address on the chain.
    pub contract: ContractAddress,
}

/// A struct containing connection and wallet information.
#[derive(Debug)]
pub struct Deployer<'a> {
    /// The client to establish a connection to a Concordium node (V2 API).
    pub client: &'a mut v2::Client,
    /// The account keys to be used for sending transactions.
    pub key: WalletAccount,
}

impl<'a> Deployer<'a> {
    /// A function to create a new deployer instance from a network client and a path to the wallet.
    pub fn new(
        client: &'a mut v2::Client,
        wallet_account_file: &Path,
    ) -> Result<Deployer<'a>, DeployError> {
        let key_data = WalletAccount::from_json_file(wallet_account_file)
            .context("Unable to read wallet file.")?;

        Ok(Deployer {
            client,
            key: key_data,
        })
    }

    /// A function to check if a module exists on the chain.
    pub async fn module_exists(
        &mut self,
        module_reference: &ModuleReference,
    ) -> Result<bool, DeployError> {
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
    /// If successful, the transaction hash and
    /// the module reference is returned.
    /// If the module already exists on
    /// chain, this function returns the module reference of the already
    /// deployed module instead.
    ///
    /// An optional expiry time for the transaction
    /// can be given. If `None` is provided, the local time + 300 seconds is
    /// used as a default expiry time.
    pub async fn deploy_wasm_module(
        &mut self,
        wasm_module: WasmModule,
        expiry: Option<TransactionTime>,
        logging: bool,
    ) -> Result<(Option<TransactionHash>, ModuleReference), DeployError> {
        if logging {
            println!("\nDeploying module....");
        }

        let module_reference = wasm_module.get_module_ref();

        let exists = self.module_exists(&module_reference).await?;

        if exists {
            if logging {
                println!(
                    "Module with reference {} already exists on the chain.",
                    module_reference
                );
            }
            return Ok((None, module_reference));
        }

        let nonce = self.get_nonce(self.key.address).await?;

        if !nonce.all_final {
            return Err(DeployError::NonceNotFinal);
        }

        let expiry = expiry.unwrap_or(TransactionTime::from_seconds(
            (chrono::Utc::now().timestamp() + 300) as u64,
        ));

        let tx = deploy_module(
            &self.key,
            self.key.address,
            nonce.nonce,
            expiry,
            wasm_module,
        );
        let bi = transactions::BlockItem::AccountTransaction(tx);

        let tx_hash = self
            .client
            .clone()
            .send_block_item(&bi)
            .await
            .map_err(DeployError::TransactionRejected)?;

        if logging {
            println!("Sent tx: {tx_hash}");
        }

        let (_, block_item) = self.client.wait_until_finalized(&tx_hash).await?;

        let module_reference = self.check_outcome_of_deploy_transaction(block_item)?;

        if logging {
            println!(
                "Transaction finalized: tx_hash={} module_ref={}",
                tx_hash, module_reference,
            );
        }

        Ok((Some(tx_hash), module_reference))
    }

    /// A function to initialize a smart contract instance on the chain.
    ///
    /// If successful, the transaction hash and the contract address is
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
        logging: bool,
    ) -> Result<(TransactionHash, ContractAddress), DeployError> {
        if logging {
            println!("\nInitializing contract....");
        }

        let nonce = self.get_nonce(self.key.address).await?;

        if !nonce.all_final {
            return Err(DeployError::NonceNotFinal);
        }

        let energy = energy.unwrap_or(Energy { energy: 5000 });

        let expiry = expiry.unwrap_or(TransactionTime::from_seconds(
            (chrono::Utc::now().timestamp() + 300) as u64,
        ));

        let tx = init_contract(
            &self.key,
            self.key.address,
            nonce.nonce,
            expiry,
            payload,
            energy,
        );

        let bi = transactions::BlockItem::AccountTransaction(tx);

        let tx_hash = self
            .client
            .clone()
            .send_block_item(&bi)
            .await
            .map_err(DeployError::TransactionRejected)?;

        if logging {
            println!("Sent tx: {tx_hash}");
        }

        let (_, block_item) = self.client.wait_until_finalized(&tx_hash).await?;

        let contract_init = self.check_outcome_of_initialization_transaction(block_item)?;

        if logging {
            println!(
                "Transaction finalized: tx_hash={} contract=({}, {})",
                tx_hash, contract_init.contract.index, contract_init.contract.subindex,
            );
        }

        Ok((tx_hash, contract_init.contract))
    }

    /// A function to update a smart contract instance on the chain.
    ///
    /// If successful, the transaction
    /// hash is returned.
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
        logging: bool,
    ) -> Result<TransactionHash, DeployError> {
        if logging {
            println!("\nUpdating contract....");
        }

        let nonce = self.get_nonce(self.key.address).await?;

        if !nonce.all_final {
            return Err(DeployError::NonceNotFinal);
        }

        let payload = transactions::Payload::Update {
            payload: update_payload,
        };

        let expiry = expiry.unwrap_or(TransactionTime::from_seconds(
            (chrono::Utc::now().timestamp() + 300) as u64,
        ));

        let energy = energy.unwrap_or(GivenEnergy::Absolute(Energy { energy: 50000 }));

        let tx = transactions::send::make_and_sign_transaction(
            &self.key,
            self.key.address,
            nonce.nonce,
            expiry,
            energy,
            payload,
        );
        let bi = transactions::BlockItem::AccountTransaction(tx);

        let tx_hash = self
            .client
            .clone()
            .send_block_item(&bi)
            .await
            .map_err(DeployError::TransactionRejected)?;

        if logging {
            println!("Sent tx: {tx_hash}");
        }

        let (_, block_item) = self.client.wait_until_finalized(&tx_hash).await?;

        self.check_outcome_of_update_transaction(block_item)?;

        if logging {
            println!("Transaction finalized: tx_hash={}", tx_hash,);
        }

        Ok(tx_hash)
    }

    /// A function to estimate the energy needed to send a transaction on the
    /// chain.
    ///
    /// If successful, the transaction energy is returned by this function.
    /// This function can be used to dry-run a transaction.
    pub async fn estimate_energy(
        &mut self,
        payload: UpdateContractPayload,
    ) -> Result<Energy, DeployError> {
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
            } => Err(DeployError::InvokeContractFailed(format!(
                "Contract invoke failed: {reason:?}, used_energy={used_energy}, return \
                 value={return_value:?}"
            ))),
            InvokeContractResult::Success {
                return_value: _,
                events: _,
                used_energy,
            } => Ok(used_energy),
        }
    }

    /// A function to get the current nonce of the wallet account.
    pub async fn get_nonce(
        &mut self,
        address: AccountAddress,
    ) -> Result<AccountNonceResponse, DeployError> {
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
        block_item: BlockItemSummary,
    ) -> Result<ModuleReference, DeployError> {
        match block_item.details {
            BlockItemSummaryDetails::AccountTransaction(a) => match a.effects {
                AccountTransactionEffects::None {
                    transaction_type,
                    reject_reason,
                } => {
                    if transaction_type != Some(TransactionType::DeployModule) {
                        return Err(DeployError::InvalidBlockItem(
                            "Expected transaction type to be DeployModule".into(),
                        ));
                    }

                    Err(DeployError::TransactionRejectedR(format!(
                        "Module deploy rejected with reason: {reject_reason:?}"
                    )))
                }
                AccountTransactionEffects::ModuleDeployed { module_ref } => {
                    Ok( module_ref )
                }
                _ => Err(DeployError::InvalidBlockItem(
                    "The parsed account transaction effect should be of type `ModuleDeployed` or \
                     `None` (in case the transaction reverted)"
                        .into(),
                )),
            },
            _ => Err(DeployError::InvalidBlockItem(
                "Can only parse an account transaction (no account creation transaction or chain \
                 update transaction)"
                    .into(),
            )),
        }
    }

    /// A function that checks the outcome of the initialization transaction.
    /// It returns an error if the `block_item` is not an initialization transaction.
    /// It returns the error code if the transaction reverted.
    fn check_outcome_of_initialization_transaction(
        &self,
        block_item: BlockItemSummary,
    ) -> Result<ContractInitialized, DeployError> {
        match block_item.details {
            BlockItemSummaryDetails::AccountTransaction(a) => match a.effects {
                AccountTransactionEffects::None {
                    transaction_type,
                    reject_reason,
                } => {
                    if transaction_type != Some(TransactionType::InitContract) {
                        return Err(DeployError::InvalidBlockItem(
                            "Expected transaction type to be InitContract".into(),
                        ));
                    }

                    Err(DeployError::TransactionRejectedR(format!(
                        "Contract init rejected with reason: {reject_reason:?}"
                    )))
                }
                AccountTransactionEffects::ContractInitialized { data } => {
                    Ok(ContractInitialized {
                        contract: data.address,
                    })
                }
                _ => Err(DeployError::InvalidBlockItem(
                    "The parsed account transaction effect should be of type \
                     `ContractInitialized` or `None` (in case the transaction reverted)"
                        .into(),
                )),
            },
            _ => Err(DeployError::InvalidBlockItem(
                "Can only parse an account transaction (no account creation transaction or chain \
                 update transaction)"
                    .into(),
            )),
        }
    }

    /// A function that checks the outcome of the update transaction.
    /// It returns an error if the `block_item` is not an update transaction.
    /// It returns the error code if the transaction reverted.
    fn check_outcome_of_update_transaction(
        &self,
        block_item: BlockItemSummary,
    ) -> Result<(), DeployError> {
        match block_item.details {
            BlockItemSummaryDetails::AccountTransaction(a) => match a.effects {
                AccountTransactionEffects::None {
                    transaction_type,
                    reject_reason,
                } => {
                    if transaction_type != Some(TransactionType::Update) {
                        return Err(DeployError::InvalidBlockItem(
                            "Expected transaction type to be Update".into(),
                        ));
                    }

                    Err(DeployError::TransactionRejectedR(format!(
                        "Contract update rejected with reason: {reject_reason:?}"
                    )))
                }
                AccountTransactionEffects::ContractUpdateIssued { effects: _ } => Ok(()),
                _ => Err(DeployError::InvalidBlockItem(
                    "The parsed account transaction effect should be of type \
                     `ContractUpdateIssued` or `None` (in case the transaction reverted)"
                        .into(),
                )),
            },
            _ => Err(DeployError::InvalidBlockItem(
                "Can only parse an account transaction (no account creation transaction or chain \
                 update transaction)"
                    .into(),
            )),
        }
    }
}
