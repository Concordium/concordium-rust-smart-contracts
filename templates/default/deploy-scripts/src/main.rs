pub mod deployer;

use anyhow::Context;
use clap::Parser;
use concordium_rust_sdk::common::types::Amount;
use concordium_rust_sdk::smart_contracts::types::OwnedContractName;
use concordium_rust_sdk::smart_contracts::types::OwnedParameter;
use concordium_rust_sdk::{
    endpoints::{self, RPCError},
    smart_contracts::common::{NewContractNameError, NewReceiveNameError},
    types::{
        hashes::TransactionHash,
        smart_contracts::{ExceedsParameterSize, ModuleReference, WasmModule},
        ContractAddress,
    },
    v2,
};

use concordium_rust_sdk::types::transactions::InitContractPayload;
use deployer::{Deployer, ModuleDeployed};
use hex::FromHexError;
use serde::{Deserialize, Serialize};
use std::{
    io::Cursor,
    path::{Path, PathBuf},
};
use thiserror::Error;

#[derive(Deserialize, Clone, Debug)]
pub struct WrappedToken {
    pub name: String,
    pub token_metadata_url: String,
    pub token_metadata_hash: TransactionHash,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Output {
    pub bridge_manager: ContractAddress,
    pub tokens: Vec<OutputToken>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct OutputToken {
    pub name: String,
    pub token_url: String,
    pub contract: ContractAddress,
}

#[derive(Error, Debug)]
pub enum DeployError {
    #[error("concordium error: {0}")]
    RPCError(#[from] RPCError),
    #[error("transport error: {0}")]
    TransportError(#[from] v2::Error),
    #[error("query error: {0}")]
    QueryError(#[from] endpoints::QueryError),
    #[error("anyhow error: {0}")]
    AnyhowError(#[from] anyhow::Error),
    #[error("There are unfinalized transactions. Transaction nonce is not reliable enough.")]
    NonceNotFinal,
    #[error("Transaction rejected: {0}")]
    TransactionRejected(RPCError),
    #[error("Transaction rejected: {0:?}")]
    TransactionRejectedR(String),
    #[error("Invalid block item: {0}")]
    InvalidBlockItem(String),
    #[error("Invalid contract name: {0}")]
    InvalidContractName(String),
    #[error("hex decoding error: {0}")]
    HexDecodingError(#[from] FromHexError),
    #[error("failed to parse receive name: {0}")]
    FailedToParseReceiveName(String),
    #[error("Json error: {0}")]
    JSONError(#[from] serde_json::Error),
    #[error("Parameter size error: {0}")]
    ParameterSizeError(#[from] ExceedsParameterSize),
    #[error("Receive name error: {0}")]
    ReceiveNameError(#[from] NewReceiveNameError),
    #[error("Contract name error: {0}")]
    ContractNameError(#[from] NewContractNameError),
    #[error("Reqwest error: {0}")]
    ReqwestError(#[from] reqwest::Error),
    #[error("Invalid metadata hash: {0}")]
    InvalidHash(String),
    #[error("IO error: {0}")]
    IOError(#[from] std::io::Error),
    #[error("Invoke contract failed: {0}")]
    InvokeContractFailed(String),
}

#[allow(dead_code)]
fn module_deployed(module_ref: &str) -> Result<ModuleDeployed, DeployError> {
    let mut bytes = [0u8; 32];
    hex::decode_to_slice(module_ref, &mut bytes)?;

    let module_deployed = ModuleDeployed {
        module_ref: ModuleReference::from(bytes),
    };

    Ok(module_deployed)
}

fn get_wasm_module(file: &Path) -> Result<WasmModule, DeployError> {
    let wasm_module = std::fs::read(file).context("Could not read the contract WASM file")?;
    let mut cursor = Cursor::new(wasm_module);
    let wasm_module: WasmModule = concordium_rust_sdk::common::from_bytes(&mut cursor)?;
    Ok(wasm_module)
}

#[derive(clap::Parser, Debug)]
#[clap(author, version, about)]
struct App {
    #[clap(
        long = "node",
        default_value = "http://node.testnet.concordium.com:20000",
        help = "V2 API of the concordium node."
    )]
    url: v2::Endpoint,
    #[clap(
        long = "account",
        help = "Location of the Concordium account key file."
    )]
    key_file: PathBuf,
}

const CONTRACTS: &[&str] = &["./cis2_nft.wasm.v1"];

#[tokio::main(flavor = "current_thread")]
async fn main() -> Result<(), DeployError> {
    let app: App = App::parse();

    let concordium_client = v2::Client::new(app.url).await?;

    let deployer = Deployer::new(concordium_client, &app.key_file)?;

    let mut modules_deployed: Vec<ModuleDeployed> = Vec::new();

    for contract in CONTRACTS {
        let wasm_module = get_wasm_module(PathBuf::from(contract).as_path())?;

        let module = deployer.deploy_wasm_module(wasm_module).await?;

        modules_deployed.push(module);
    }

    // Write your own deployment/initialization script below. Here is an example given.

    let param: OwnedParameter = OwnedParameter::default();

    let init_method_name: &str = "init_cis2_nft";

    let payload = InitContractPayload {
        init_name: OwnedContractName::new(init_method_name.into())?,
        amount: Amount::from_micro_ccd(0),
        mod_ref: modules_deployed[0].module_ref,
        param,
    };

    let _contract = deployer.init_contract(payload).await?;

    Ok(())
}
