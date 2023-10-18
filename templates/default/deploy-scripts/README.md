# Deploy, Initialize, and Update Script Template

This project has boilerplate code to write deployment, initialization, and update scripts for Concordium smart contract protocols. 

# Purpose

Automatic scripts are useful to speed up the development and testing of your protocol on the chain. 
In addition, scripts help to set up identical protocols on different chains easily. E.g. you can deploy your protocol to testnet or mainnet by just specifying a corresponding node connection and account keys for the respective network when running the script.

# Running The Script

Build and run the script from the deploy-scripts folder using
```
cargo run
```

The following options are necessary when running the script

```
    --node <CONCORDIUM_NODE_URL>
        V2 API of the concordium node. [default: http://node.testnet.concordium.com:20000]
    --account <CONCORDIUM_ACCOUNT_PATH>
        Path to the file containing the Concordium account keys exported from the wallet (e.g. ./myPath/4SizPU2ipqQQza9Xa6fUkQBCDjyd1vTNUNDGbBeiRGpaJQc6qX.export).
    --module <MODULE_PATH>
        Path of the Concordium smart contract module. Use this flag several times \
        if you have several smart contract modules to be deployed (e.g. --module ./myPath/default.wasm.v1 --module ./default2.wasm.v1).
```

The `account` parameter should be a Concordium wallet account either exported from the
Browser wallet or the mobile wallets, or in the format emitted by the
genesis tool.

Example:
```
cargo run -- --node http://node.testnet.concordium.com:20000 --account ./myPath/4SizPU2ipqQQza9Xa6fUkQBCDjyd1vTNUNDGbBeiRGpaJQc6qX.export --module ./myPath/default.wasm.v1 --module ./default2.wasm.v1
```

# Functionalities

The boilerplate code has support for the following functionalities:

Read functions:
- `estimate_energy`: To estimate the energy needed to execute one of the three write functions below.
- `module_exists`: To check if a module has already been deployed on the chain.
- `get_nonce`: To get the next nonce of the provided wallet account.

Write functions:
- `deploy_wasm_module`: To deploy a new smart contract module on the chain.
- `init_contract`: To initialize a smart contract instance on the chain.
- `update_contract`: To update a smart contract instance on the chain.

Helper functions to check the outcome of the transactions:
- `check_outcome_of_deploy_transaction`: To check the outcome of a deploy module transaction.
- `check_outcome_of_initialization_transaction`: To check the outcome of a smart contract instance initialization transaction.
- `check_outcome_of_update_transaction`: To check the outcome of an update smart contract instance transaction.

The `main.rs` file has a section (marked with `// Write your own deployment/initialization script below. An example is given here.`) that you should replace with your custom logic. You can write your script using `deploy`, `initialize`, and contract `update` transactions.

# Running the Example

The `main.rs` file has a section (marked with `// Write your own deployment/initialization script below. An example is given here.`) that provides an example that you can run.

Navigate into the root folder and compile the `default` smart contract with the command:
```
cargo concordium build --out ./deploy-scripts/default.wasm.v1
```

Navigate into the deploy-scripts folder and run the example with the `default` smart contract (replace your wallet account in the below command):

```
cargo run -- --node http://node.testnet.concordium.com:20000 --account ./4SizPU2ipqQQza9Xa6fUkQBCDjyd1vTNUNDGbBeiRGpaJQc6qX.export --module ./default.wasm.v1
```

The output should be:

```
Deploying module....
Module with reference 3774d4b9ae86ae3c5192e13455d7515073f5163a25deabc55abdab31d1cc002e already exists on the chain.

Initializing contract....
Sent transaction with hash: bdb43d1f00a4c5ba02ec81e0e2da52b6920582a16acd21a364ec3e3734ad4f12
Transaction finalized: tx_hash=bdb43d1f00a4c5ba02ec81e0e2da52b6920582a16acd21a364ec3e3734ad4f12 contract=(7000, 0)

Updating contract....
Sent transaction with hash: 4843efc3b700bce8e67f2cc3f17da3124cf0a7323652fb778412ecd768ae2fe5
Transaction finalized: tx_hash=4843efc3b700bce8e67f2cc3f17da3124cf0a7323652fb778412ecd768ae2fe5
```
