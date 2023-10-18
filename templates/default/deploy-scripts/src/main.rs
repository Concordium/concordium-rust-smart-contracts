pub mod deployer;
use anyhow::{Context, Error};
use clap::Parser;
use concordium_rust_sdk::{
    common::types::Amount,
    smart_contracts::{
        common::{self as contracts_common},
        types::{OwnedContractName, OwnedParameter, OwnedReceiveName},
    },
    types::{
        smart_contracts::{ModuleReference, WasmModule},
        transactions,
        transactions::{send::GivenEnergy, InitContractPayload},
    },
    v2,
};
use deployer::{DeployResult, Deployer, InitResult};
use std::{
    io::Cursor,
    path::{Path, PathBuf},
};

/// Reads the wasm module from a given file path.
fn get_wasm_module(file: &Path) -> Result<WasmModule, Error> {
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
    url: v2::Endpoint,
    #[clap(
        long = "account",
        help = "Path to the file containing the Concordium account keys exported from the wallet \
                (e.g. ./myPath/3PXwJYYPf6fyVb4GJquxSZU8puxrHfzc4XogdMVot8MUQK53tW.export)."
    )]
    key_file: PathBuf,
    #[clap(
        long = "module",
        help = "Path of the Concordium smart contract module. Use this flag several times if you \
                have several smart contract modules to be deployed (e.g. --module \
                ./myPath/default.wasm.v1 --module ./default2.wasm.v1)."
    )]
    module: Vec<PathBuf>,
}

/// Main function: It deploys to chain all wasm modules from the command line
/// `--module` flags. Write your own custom deployment/initialization script in
/// this function. An deployment/initialization script example is given in this
/// function for the `default` smart contract.
#[tokio::main]
async fn main() -> Result<(), Error> {
    let app: App = App::parse();

    let concordium_client = v2::Client::new(app.url).await?;

    let mut deployer = Deployer::new(concordium_client, &app.key_file)?;

    let mut modules_deployed: Vec<ModuleReference> = Vec::new();

    for contract in app.module {
        let wasm_module = get_wasm_module(contract.as_path())?;

        let deploy_result = deployer
            .deploy_wasm_module(wasm_module, None)
            .await
            .context("Failed to deploy a module.")?;

        match deploy_result {
            DeployResult::ModuleDeployed(module_deploy_result) => {
                modules_deployed.push(module_deploy_result.module_reference)
            }
            DeployResult::ModuleExists(module_reference) => modules_deployed.push(module_reference),
        }
    }

    // Write your own deployment/initialization script below. An example is given
    // here.

    let param: OwnedParameter = OwnedParameter::empty(); // Example

    let init_method_name: &str = "init_{{crate_name}}"; // Example

    let payload = InitContractPayload {
        init_name: OwnedContractName::new(init_method_name.into())?,
        amount: Amount::from_micro_ccd(0),
        mod_ref: modules_deployed[0],
        param,
    }; // Example

    let init_result: InitResult = deployer
        .init_contract(payload, None, None)
        .await
        .context("Failed to initialize the contract.")?; // Example

    // This is how you can use a type from your smart contract.
    use {{crate_name}}::MyInputType; // Example

    let input_parameter: MyInputType = false; // Example

    // Create a successful transaction.

    let bytes = contracts_common::to_bytes(&input_parameter); // Example

    let update_payload = transactions::UpdateContractPayload {
        amount: Amount::from_ccd(0),
        address: init_result.contract_address,
        receive_name: OwnedReceiveName::new_unchecked("{{crate_name}}.receive".to_string()),
        message: bytes.try_into()?,
    }; // Example

    // The transaction costs on Concordium have two components, one is based on the size of the
    // transaction and the number of signatures, and then there is a
    // transaction-specific one for executing the transaction (which is estimated with this function).
    let mut energy = deployer
        .estimate_energy(update_payload.clone())
        .await
        .context("Failed to estimate the energy.")?; // Example

    // We add 100 energy to be safe.
    energy.energy += 100; // Example

    // `GivenEnergy::Add(energy)` is the recommended helper function to handle the transaction cost automatically for the first component
    // (based on the size of the transaction and the number of signatures).
    // [GivenEnergy](https://docs.rs/concordium-rust-sdk/latest/concordium_rust_sdk/types/transactions/construct/enum.GivenEnergy.html)
    let _update_contract = deployer
        .update_contract(update_payload, Some(GivenEnergy::Add(energy)), None)
        .await
        .context("Failed to update the contract.")?; // Example

    // Write your own deployment/initialization script above. An example is given
    // here.

    Ok(())
}
