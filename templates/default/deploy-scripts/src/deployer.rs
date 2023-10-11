use crate::v2::BlockIdentifier::Best;
use concordium_rust_sdk::{
    common::types::TransactionTime,
    id::types::AccountAddress,
    smart_contracts::common::{Address, ModuleReference},
    types::{
        hashes::{HashBytes, TransactionMarker},
        queries::AccountNonceResponse,
        smart_contracts::{ContractContext, InvokeContractResult, WasmModule},
        transactions::{
            self,
            send::{deploy_module, init_contract, GivenEnergy},
            InitContractPayload, UpdateContractPayload,
        },
        AccountTransactionEffects, BlockItemSummary, BlockItemSummaryDetails, ContractAddress,
        Energy, RejectReason, TransactionType, WalletAccount,
    },
    v2,
};
use std::path::Path;

use crate::DeployError;

/// A struct representing the deployed module on the chain.
#[derive(Clone, Debug)]
pub struct ModuleDeployed {
    /// Module reference on the chain.
    pub module_ref: ModuleReference,
}

/// A struct representing a smart contract instance on the chain.
#[derive(Clone, Debug)]
pub struct ContractInitialized {
    /// Smart contract address on the chain.
    pub contract: ContractAddress,
}

/// A struct containing connection and wallet information.
#[derive(Debug)]
pub struct Deployer {
    /// The client to establish a connection to a Concordium node (V2 API).
    pub client: v2::Client,
    /// The account keys to be used for sending transactions.
    pub key:    WalletAccount,
}

impl Deployer {
    /// A function to create a new deployer instance.
    pub fn new(client: v2::Client, wallet_account_file: &Path) -> Result<Deployer, DeployError> {
        let key_data = WalletAccount::from_json_file(wallet_account_file)?;

        Ok(Deployer {
            client,
            key: key_data,
        })
    }

    /// A function to check if a module exists on the chain.
    pub async fn module_exists(&self, wasm_module: WasmModule) -> Result<bool, DeployError> {
        let best_block = self.client.clone().get_block_finalization_summary(Best).await?;

        let best_block_hash = best_block.block_hash;

        let module_ref = wasm_module.get_module_ref();

        let module_src = self.client.clone().get_module_source(&module_ref, &best_block_hash).await;

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
        &self,
        wasm_module: WasmModule,
        expiry: Option<TransactionTime>,
    ) -> Result<(Option<HashBytes<TransactionMarker>>, ModuleDeployed), DeployError> {
        println!("\nDeploying module....");

        let exists = self.module_exists(wasm_module.clone()).await?;

        if exists {
            println!(
                "Module with reference {} already exists on the chain.",
                wasm_module.get_module_ref()
            );
            return Ok((None, ModuleDeployed {
                module_ref: wasm_module.get_module_ref(),
            }));
        }

        let nonce = self.get_nonce(self.key.address).await?;

        if !nonce.all_final {
            return Err(DeployError::NonceNotFinal);
        }

        let expiry = match expiry {
            Some(expiry) => expiry,
            None => TransactionTime::from_seconds((chrono::Utc::now().timestamp() + 300) as u64),
        };

        let tx = deploy_module(&self.key, self.key.address, nonce.nonce, expiry, wasm_module);
        let bi = transactions::BlockItem::AccountTransaction(tx);

        let tx_hash = self
            .client
            .clone()
            .send_block_item(&bi)
            .await
            .map_err(DeployError::TransactionRejected)?;

        println!("Sent tx: {tx_hash}");

        let (_, block_item) = self.client.clone().wait_until_finalized(&tx_hash).await?;

        let module_deployed = self.parse_deploy_module_event(block_item)?;

        println!(
            "Transaction finalized, tx_hash={} module_ref={}",
            tx_hash, module_deployed.module_ref,
        );

        Ok((Some(tx_hash), module_deployed))
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
        &self,
        payload: InitContractPayload,
        energy: Option<Energy>,
        expiry: Option<TransactionTime>,
    ) -> Result<(HashBytes<TransactionMarker>, ContractAddress), DeployError> {
        println!("\nInitializing contract....");

        let nonce = self.get_nonce(self.key.address).await?;

        if !nonce.all_final {
            return Err(DeployError::NonceNotFinal);
        }

        let energy = match energy {
            Some(energy) => energy,
            None => Energy {
                energy: 5000,
            },
        };

        let expiry = match expiry {
            Some(expiry) => expiry,
            None => TransactionTime::from_seconds((chrono::Utc::now().timestamp() + 300) as u64),
        };

        let tx = init_contract(&self.key, self.key.address, nonce.nonce, expiry, payload, energy);

        let bi = transactions::BlockItem::AccountTransaction(tx);

        let tx_hash = self
            .client
            .clone()
            .send_block_item(&bi)
            .await
            .map_err(DeployError::TransactionRejected)?;

        println!("Sent tx: {tx_hash}");

        let (_, block_item) = self.client.clone().wait_until_finalized(&tx_hash).await?;

        let contract_init = self.parse_contract_init_event(block_item)?;

        println!(
            "Transaction finalized, tx_hash={} contract=({}, {})",
            tx_hash, contract_init.contract.index, contract_init.contract.subindex,
        );

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
        &self,
        update_payload: UpdateContractPayload,
        energy: Option<GivenEnergy>,
        expiry: Option<TransactionTime>,
    ) -> Result<HashBytes<TransactionMarker>, DeployError> {
        println!("\nUpdating contract....");

        let nonce = self.get_nonce(self.key.address).await?;

        if !nonce.all_final {
            return Err(DeployError::NonceNotFinal);
        }

        let payload = transactions::Payload::Update {
            payload: update_payload,
        };

        let expiry = match expiry {
            Some(expiry) => expiry,
            None => TransactionTime::from_seconds((chrono::Utc::now().timestamp() + 300) as u64),
        };

        let energy = match energy {
            Some(energy) => energy,
            None => GivenEnergy::Absolute(Energy {
                energy: 50000,
            }),
        };

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

        println!("Sent tx: {tx_hash}");

        let (_, block_item) = self.client.clone().wait_until_finalized(&tx_hash).await?;

        self.parse_contract_update_event(block_item)?;

        println!("Transaction finalized, tx_hash={}", tx_hash,);

        Ok(tx_hash)
    }

    /// A function to estimate the energy needed to send a transaction on the
    /// chain.
    ///
    /// If successful, the transaction energy is returned by this function.
    /// This function can be used to dry-run a transaction.
    ///
    /// An optional max_energy value for the transaction can
    /// be given. If `None` is provided, 50000 energy is used as a default
    /// max_energy value.
    pub async fn estimate_energy(
        &self,
        payload: UpdateContractPayload,
        max_energy: Option<Energy>,
    ) -> Result<Energy, DeployError> {
        println!("\nEstimating energy....");

        let best_block = self.client.clone().get_block_finalization_summary(Best).await?;

        let best_block_hash = best_block.block_hash;

        let max_energy = match max_energy {
            Some(energy) => energy,
            None => Energy {
                energy: 50000,
            },
        };

        let context = ContractContext {
            invoker:   Some(Address::Account(self.key.address)),
            contract:  payload.address,
            amount:    payload.amount,
            method:    payload.receive_name,
            parameter: payload.message,
            energy:    max_energy,
        };

        let result = self.client.clone().invoke_instance(&best_block_hash, &context).await?;

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
            } => {
                let e = used_energy.energy;
                println!("Contract invoke success: estimated_energy={e}");
                Ok(Energy {
                    energy: e,
                })
            }
        }
    }

    /// A function to get the current nonce of the wallet account.
    pub async fn get_nonce(
        &self,
        address: AccountAddress,
    ) -> Result<AccountNonceResponse, DeployError> {
        let nonce = self.client.clone().get_next_account_sequence_number(&address).await?;
        Ok(nonce)
    }

    /// A function to parse the deploy module events.
    fn parse_deploy_module_event(
        &self,
        block_item: BlockItemSummary,
    ) -> Result<ModuleDeployed, DeployError> {
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

                    match reject_reason {
                        RejectReason::ModuleHashAlreadyExists {
                            contents,
                        } => Ok(ModuleDeployed {
                            module_ref: contents,
                        }),
                        _ => Err(DeployError::TransactionRejectedR(format!(
                            "Module deploy rejected with reason: {reject_reason:?}"
                        ))),
                    }
                }
                AccountTransactionEffects::ModuleDeployed {
                    module_ref,
                } => Ok(ModuleDeployed {
                    module_ref,
                }),
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

    /// A function to parse the initialization events.
    fn parse_contract_init_event(
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
                AccountTransactionEffects::ContractInitialized {
                    data,
                } => Ok(ContractInitialized {
                    contract: data.address,
                }),
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

    /// A function to parse the contract update events.
    fn parse_contract_update_event(&self, block_item: BlockItemSummary) -> Result<(), DeployError> {
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
                AccountTransactionEffects::ContractUpdateIssued {
                    effects: _,
                } => Ok(()),
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
