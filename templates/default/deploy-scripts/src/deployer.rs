use concordium_rust_sdk::{
    common::types::TransactionTime,
    id::types::AccountAddress,
    smart_contracts::common::{Address, ModuleReference},
    types::{
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
use crate::v2::BlockIdentifier::Best;

use crate::DeployError;

#[derive(Clone, Debug)]
pub struct ModuleDeployed {
    pub module_ref: ModuleReference,
}

#[derive(Clone, Debug)]
pub struct ContractInitialized {
    pub contract: ContractAddress,
}

#[derive(Debug)]
pub struct Deployer {
    pub client: v2::Client,
    pub key: WalletAccount,
}

impl Deployer {
    pub fn new(client: v2::Client, wallet_account_file: &Path) -> Result<Deployer, DeployError> {
        let key_data = WalletAccount::from_json_file(wallet_account_file)?;

        Ok(Deployer {
            client,
            key: key_data,
        })
    }

    pub async fn module_exists(&self, wasm_module: WasmModule) -> Result<bool, DeployError> {

        let best_block = self.client.clone().get_block_finalization_summary(Best).await?;
 
        let best_block_hash = best_block.block_hash;

        let module_ref = wasm_module.get_module_ref();

        let module_ref = self
            .client
            .clone()
            .get_module_source(&module_ref, &best_block_hash)
            .await;

        match module_ref {
            Ok(_) => Ok(true),
            Err(e) if e.is_not_found() => Ok(false),
            Err(e) => Err(e.into()),
        }
    }

    pub async fn deploy_wasm_module(
        &self,
        wasm_module: WasmModule,
    ) -> Result<ModuleDeployed, DeployError> {
        println!();

        println!("Deploying contract....");

        let exists = self.module_exists(wasm_module.clone()).await?;

        if exists {
            println!(
                "Module with reference {} already exists on chain.",
                wasm_module.get_module_ref()
            );
            return Ok(ModuleDeployed {
                module_ref: wasm_module.get_module_ref(),
            });
        }

        let nonce = self.get_nonce(self.key.address).await?;

        if !nonce.all_final {
            return Err(DeployError::NonceNotFinal);
        }

        let expiry = TransactionTime::from_seconds((chrono::Utc::now().timestamp() + 300) as u64);

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

        let (_, block_item) = self.client.clone().wait_until_finalized(&tx_hash).await?;

        let module_deployed = self.parse_deploy_module_event(block_item)?;

        println!(
            "Transaction finalized, tx_hash={} module_ref={}",
            tx_hash, module_deployed.module_ref,
        );

        Ok(module_deployed)
    }

    pub async fn init_contract(
        &self,
        payload: InitContractPayload,
    ) -> Result<ContractAddress, DeployError> {
        println!();

        println!("Initializing contract....");

        let nonce = self.get_nonce(self.key.address).await?;

        if !nonce.all_final {
            return Err(DeployError::NonceNotFinal);
        }

        let expiry = TransactionTime::from_seconds((chrono::Utc::now().timestamp() + 300) as u64);
        let energy = Energy { energy: 5000 };

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

        println!("Sent tx: {tx_hash}");

        let (_, block_item) = self.client.clone().wait_until_finalized(&tx_hash).await?;

        let contract_init = self.parse_contract_init_event(block_item)?;

        println!(
            "Transaction finalized, tx_hash={} contract=({}, {})",
            tx_hash, contract_init.contract.index, contract_init.contract.subindex,
        );

        Ok(contract_init.contract)
    }

    pub async fn update_contract(
        &self,
        update_payload: UpdateContractPayload,
        energy: GivenEnergy,
    ) -> Result<(), DeployError> {
        let nonce = self.get_nonce(self.key.address).await?;

        if !nonce.all_final {
            return Err(DeployError::NonceNotFinal);
        }

        let payload = transactions::Payload::Update {
            payload: update_payload,
        };

        let expiry = TransactionTime::from_seconds((chrono::Utc::now().timestamp() + 300) as u64);

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

        Ok(())
    }

    pub async fn estimate_energy(&self, payload: UpdateContractPayload) -> Result<Energy, DeployError> {
        let best_block = self.client.clone().get_block_finalization_summary(Best).await?;

        let best_block_hash = best_block.block_hash;

        let context = ContractContext {
            invoker: Some(Address::Account(self.key.address)),
            contract: payload.address,
            amount: payload.amount,
            method: payload.receive_name,
            parameter: payload.message,
            energy: 100000.into(),
        };

        let result = self
            .client
            .clone()
            .invoke_instance(&best_block_hash, &context)
            .await?;

        match result.response {
            InvokeContractResult::Failure {
                return_value,
                reason,
                used_energy,
            } => Err(DeployError::InvokeContractFailed(format!(
                "contract invoke failed: {reason:?}, used_energy={used_energy}, return \
                 value={return_value:?}"
            ))),
            InvokeContractResult::Success {
                return_value: _,
                events: _,
                used_energy,
            } => {
                let e = used_energy.energy;
                println!("Estimated energy: {e}");
                Ok(Energy { energy: e + 100 })
            }
        }
    }

    pub async fn get_nonce(
        &self,
        address: AccountAddress,
    ) -> Result<AccountNonceResponse, DeployError> {
        let nonce = self
            .client
            .clone()
            .get_next_account_sequence_number(&address)
            .await?;
        Ok(nonce)
    }

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
                            "Expected transaction type to be DeployModule if rejected".into(),
                        ));
                    }

                    match reject_reason {
                        RejectReason::ModuleHashAlreadyExists { contents } => Ok(ModuleDeployed {
                            module_ref: contents,
                        }),
                        _ => Err(DeployError::TransactionRejectedR(format!(
                            "module deploy rejected with reason: {reject_reason:?}"
                        ))),
                    }
                }
                AccountTransactionEffects::ModuleDeployed { module_ref } => {
                    Ok(ModuleDeployed { module_ref })
                }
                _ => Err(DeployError::InvalidBlockItem(
                    "invalid transaction effects".into(),
                )),
            },
            _ => Err(DeployError::InvalidBlockItem(
                "Expected Account transaction".into(),
            )),
        }
    }

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
                            "Expected transaction type to be InitContract if rejected".into(),
                        ));
                    }

                    Err(DeployError::TransactionRejectedR(format!(
                        "contract init rejected with reason: {reject_reason:?}"
                    )))
                }
                AccountTransactionEffects::ContractInitialized { data } => {
                    Ok(ContractInitialized {
                        contract: data.address,
                    })
                }
                _ => Err(DeployError::InvalidBlockItem(
                    "invalid transaction effects".into(),
                )),
            },
            _ => Err(DeployError::InvalidBlockItem(
                "Expected Account transaction".into(),
            )),
        }
    }

    fn parse_contract_update_event(&self, block_item: BlockItemSummary) -> Result<(), DeployError> {
        match block_item.details {
            BlockItemSummaryDetails::AccountTransaction(a) => match a.effects {
                AccountTransactionEffects::None {
                    transaction_type,
                    reject_reason,
                } => {
                    if transaction_type != Some(TransactionType::Update) {
                        return Err(DeployError::InvalidBlockItem(
                            "Expected transaction type to be Update if rejected".into(),
                        ));
                    }

                    Err(DeployError::TransactionRejectedR(format!(
                        "contract update rejected with reason: {reject_reason:?}"
                    )))
                }
                AccountTransactionEffects::ContractUpdateIssued { effects: _ } => Ok(()),
                _ => Err(DeployError::InvalidBlockItem(
                    "invalid transaction effects".into(),
                )),
            },
            _ => Err(DeployError::InvalidBlockItem(
                "Expected Account transaction".into(),
            )),
        }
    }
}
