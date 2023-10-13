# Deploy, Initialize, and Update Script Template

This project has boilerplate code to write deployment, initialization, and update scripts for Concordium smart contract protocols. 

# Purpose

Automatic scripts are useful to speed up the development and testing of your protocol on the chain. 
In addition, scripts help to set up identical protocols on different chains easily. E.g. you can deploy your protocol to testnet or mainnet by just specifying a corresponding node connection when running the script.

# Running The Script

Build and run the script from the deploy-scripts folder using
```
cargo run
```

The following options are necessary when running the script

```
      --node <CONCORDIUM_URL>
          V2 API of the concordium node. [default: http://node.testnet.concordium.com:20000]
      --account <CONCORDIUM_ACCOUNT>
          Location path and file name of the Concordium account key file (e.g. ./myPath/4SizPU2ipqQQza9Xa6fUkQBCDjyd1vTNUNDGbBeiRGpaJQc6qX.export).
      --modules <MODULES>
          Location paths and names of Concordium smart contract modules. Use this flag several times \
          if you have several smart contract modules to be deployed (e.g. --modules ./myPath/default.wasm.v1 --modules ./default2.wasm.v1).
```

The `account` parameter should be a Concordium wallet account either exported from the
Browser wallet or the mobile wallets, or in the format emitted by the
genesis tool.

Example:
```
cargo run -- --node http://node.testnet.concordium.com:20000 --account ./myPath/4SizPU2ipqQQza9Xa6fUkQBCDjyd1vTNUNDGbBeiRGpaJQc6qX.export --modules ./myPath/default.wasm.v1 --modules ./default2.wasm.v1
```

# Functionalities

The boilerplate code has support for the following functionalities:

Read functions:
- `estimate_energy`: To estimate the energy needed to execute one of the three write functions below.
- `module_exists`: To check if a module has already been deployed on the chain.
- `get_nonce`: To get the current nonce of the provided wallet account.

Write functions:
- `deploy_wasm_module`: To deploy a new smart contract module on the chain.
- `init_contract`: To initialize a smart contract instance on the chain.
- `update_contract`: To update a smart contract instance on the chain.

Event parsing helper functions:
- `parse_deploy_module_event`: To parse the chain events after deploying a module.
- `parse_contract_init_event`: To parse the chain events after initialization of a smart contract instance.
- `parse_contract_update_event`: To parse the chain events after updating a smart contract instance.

The `main.rs` file has a section (marked with `// Write your own deployment/initialization script below. An example is given here.`) that you should replace with your custom logic. You can write your script using `deploy`, `initialize`, and contract `update` transactions.

# Running the Example

The `main.rs` file has a section (marked with `// Write your own deployment/initialization script below. An example is given here.`) that provides an example that you can run.

ATTENTION: You have to have created a smart contract with the name `default` to run the given example. This can be done by answering `default` to the two questions when creating the project via `cargo-generate`.

Navigate into the root folder and compile the `default` smart contract with the command:
```
cargo concordium build --out ./deploy-scripts/default.wasm.v1
```

Navigate into the deploy-scripts folder and run the example with the `default` smart contract (replace your wallet account in the below command):

```
cargo run -- --node http://node.testnet.concordium.com:20000 --account ./4SizPU2ipqQQza9Xa6fUkQBCDjyd1vTNUNDGbBeiRGpaJQc6qX.export --modules ./default.wasm.v1
```

The output should be:

```
Deploying module....
Module with reference 15c936d9f60dc99c543282a8f16823d2ec5c6faae689772ae06a9b2de45a39d0 already exists on the chain.

Initializing contract....
Sent tx: 09ecaa6a66e4fe2a756dd9ad8c91f5fc2099a6dd30ebd4532cb8c5aad1bab440
Transaction finalized, tx_hash=09ecaa6a66e4fe2a756dd9ad8c91f5fc2099a6dd30ebd4532cb8c5aad1bab440 contract=(6941, 0)

Estimating energy....
Contract invoke success: estimated_energy=731

Updating contract....
Sent tx: c61b40a09e422835c70b07369bc5f4bba8292499be80cd735af21941c9798dd2
Transaction finalized, tx_hash=c61b40a09e422835c70b07369bc5f4bba8292499be80cd735af21941c9798dd2
```
