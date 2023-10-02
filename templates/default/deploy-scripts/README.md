# Deploy, Initialize, and Update Script Template

This project has boilerplate code to write deployment, initilization, and update scripts for Concordium smart contract protocols. 

# Purpose

Automatic scripts are useful to speed up the development and testing of your protocol on chain. 
In addition, scripts help to set up identical protocols on different chains easily. E.g. you can deploy your protocol to testnet or mainnet by just specifiying a corresponding node connection when running the script.

# Setup

Option 1:

```
cargo concordium init 
```

Option 2 (alternative command):

```
cargo generate --git https://github.com/Concordium/concordium-rust-smart-contracts.git
```

Any of the two commands will work and will give you several templates to choose from. 

- Choose the `templates/default` and answer the questions to complete the setup process.

At the end, you will have a Rust project setup with this boilerplate code included.

# Running The Script

Build and run the script from the root folder using
```
cargo run
```

The following options are necessary when running the script

```
      --node <CONCORDIUM_URL>
          V2 API of the concordium node. [default: http://node.testnet.concordium.com:20000]
      --account <CONCORDIUM_ACCOUNT>
          Path to the Concordium account (with account keys).
      --modules <modules[]>
          A list of wasm modules. [default: [./default.wasm.v1]]
```

The `account` parameter should be a Concordium wallet account either exported from the
Browser wallet or the mobile wallets, or in the format emitted by the
genesis tool.

Example:
```
cargo run -- --node http://node.testnet.concordium.com:20000 --account ./3PXwJYYPf6fyVb4GJquxSZU8puxrHfzc4XogdMVot8MUQK53tW.export --modules ["./default.wasm.v1"]
```

# Functionalities

The boilerplate code has support for the following functionalities:

Read functions:
- `estimate_energy`: To estmiate the energy needed to execute one of the three write functions below.
- `module_exists`: To check if a module has already been deployed on chain.
- `get_nonce`: To get the current nonce of the provided wallet account.

Write functions:
- `deploy_wasm_module`: To deploy a new smart contract module on chain.
- `init_contract`: To initilization a smart contract instance on chain.
- `update_contract`: To updating a smart conract instance on chain.

Event parsing helper functions:
- `parse_deploy_module_event`: To parse the chain events after deploying a modules.
- `parse_contract_init_event`: To parse the chain events after initilization a smart contract instance.
- `parse_contract_update_event`: To parse the chain events after updating a smart conract instance.

The `main.rs` file has a section (marked with `// Write your own deployment/initialization script below. An example is given here.`) that you should replace with your custom logic to deploy, initilize, and update your smart contract protocol.

# Running the Example

The `main.rs` file has a section (marked with `// Write your own deployment/initialization script below. An example is given here.`) which provides an example that you can run.

Navigate into the root folder and compile the `default` smart contract with the command:
```
cargo concordium build --out ./deploy-scripts/default.wasm.v1
```

Then, deploy the `default` smart contract on chain (replace your wallet account in the below command):

```
cargo run -- --node http://node.testnet.concordium.com:20000 --account ./3PXwJYYPf6fyVb4GJquxSZU8puxrHfzc4XogdMVot8MUQK53tW.export --modules ["./default.wasm.v1"]
```

The output should be:

```
$ cargo run

...
```
