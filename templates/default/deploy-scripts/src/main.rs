pub mod deployer;
use anyhow::Context;
use clap::Parser;
use concordium_rust_sdk::{
    common::types::Amount,
    endpoints::{self, RPCError},
    smart_contracts::{
        common::{self as contracts_common, NewContractNameError, NewReceiveNameError},
        types::{OwnedContractName, OwnedParameter, OwnedReceiveName},
    },
    types::{
        smart_contracts::{ExceedsParameterSize, WasmModule},
        transactions,
        transactions::send::GivenEnergy,
    },
    v2,
};
use itertools::Itertools;

use concordium_rust_sdk::types::transactions::InitContractPayload;
use deployer::{Deployer, ModuleDeployed};
use hex::FromHexError;
use std::{
    io::Cursor,
    path::{Path, PathBuf},
};
use thiserror::Error;

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

/// Reads the wasm module from a given file path and file name.
fn get_wasm_module(file: &Path) -> Result<WasmModule, DeployError> {
    let wasm_module = std::fs::read(file).context("Could not read the WASM file")?;
    let mut cursor = Cursor::new(wasm_module);
    let wasm_module: WasmModule = concordium_rust_sdk::common::from_bytes(&mut cursor)?;
    Ok(wasm_module)
}

/// Command line flags.
#[derive(clap::Parser, Debug)]
#[clap(author, version, about)]
struct App {
    #[clap(
        long = "node",
        default_value = "http://node.testnet.concordium.com:20000",
        help = "V2 API of the Concordium node."
    )]
    url:      v2::Endpoint,
    #[clap(
        long = "account",
        help = "Location path and file name of the Concordium account key file (e.g. \
                ./myPath/3PXwJYYPf6fyVb4GJquxSZU8puxrHfzc4XogdMVot8MUQK53tW.export)."
    )]
    key_file: PathBuf,
    #[clap(
        long = "modules",
        help = "Location paths and names of Concordium smart contract modules. Use this flag \
                several times if you have several smart contract modules to be deployed (e.g. \
                --modules ./myPath/default.wasm.v1 --modules ./default2.wasm.v1)."
    )]
    modules:  Vec<PathBuf>,
}

/// Main function: It deploys to chain all wasm modules from the command line
/// `--modules` flags. Write your own custom deployment/initialization script in
/// this function. An deployment/initialization script example is given in this
/// function for the `default` smart contract.
#[tokio::main(flavor = "current_thread")]
async fn main() -> Result<(), DeployError> {
    let app: App = App::parse();

    let mut concordium_client = v2::Client::new(app.url).await?;

    let mut deployer = Deployer::new(&mut concordium_client, &app.key_file)?;

    let mut modules_deployed: Vec<ModuleDeployed> = Vec::new();

    for contract in app.modules.iter().unique() {
        let wasm_module = get_wasm_module(contract.as_path())?;

        let (_, module) = deployer.deploy_wasm_module(wasm_module, None).await?;

        modules_deployed.push(module);
    }

    // Write your own deployment/initialization script below. An example is given
    // here.

    let param: OwnedParameter = OwnedParameter::default(); // Example

    let init_method_name: &str = "init_{{crate_name}}"; // Example

    let payload = InitContractPayload {
        init_name: OwnedContractName::new(init_method_name.into())?,
        amount: Amount::from_micro_ccd(0),
        mod_ref: modules_deployed[0].module_ref,
        param,
    }; // Example

    let (_, contract) = deployer.init_contract(payload, None, None).await?; // Example

    // This is how you can use a type from your smart contract.
    use {{crate_name}}::{MyInputType};

    let input_parameter: MyInputType = false;

    // Create a successful transaction.

    let bytes = contracts_common::to_bytes(&input_parameter); // Example

    let update_payload = transactions::UpdateContractPayload {
        amount:       Amount::from_ccd(0),
        address:      contract,
        receive_name: OwnedReceiveName::new_unchecked("{{crate_name}}.receive".to_string()),
        message:      bytes.try_into()?,
    }; // Example

    let mut energy = deployer.estimate_energy(update_payload.clone(), None).await?; // Example

    // We add 100 energy to be safe.
    energy.energy += 100; // Example

    let _update_contract =
        deployer.update_contract(update_payload, Some(GivenEnergy::Add(energy)), None).await?; // Example

    // Write your own deployment/initialization script above. An example is given
    // here.

    Ok(())
}
