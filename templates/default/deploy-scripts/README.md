# Deploy smart contract instances for Bridge Manager

# Setup:

Make sure to initialize and update the submodules of this repository

```
git submodule update --init --recursive
```

Build and run the scripts using
```
cargo run
```

The following options are necessary

```
      --node <CONCORDIUM_URL>
          V2 API of the concordium node. [default: http://localhost:20001]
      --wallet <CONCORDIUM_WALLET>
          Location of the Concordium wallet.
      --tokens <TOKENS>
          JSON file with a list of tokens.
      --manager-source <MANAGER_SOURCE>
          Location of the compiled BridgeManager contract.
      --cis2-bridgeable <CIS2_SOURCE>
          Source of the CIS2 token contract.
```

The `tokens` file should be a valid JSON file with a list of objects of the form
```
{
    name: "USDC.eth",
    token_metadata_url:  "http://domain/path",
    token_metadata_hash: "6a6ca3243935653bf3b271aa1257a3f9351663757c66a498750d4622f81c08f5"
}
```

The `wallet` parameter should be a Concordium wallet either exported from the
Browser wallet or the new mobile wallets, or in the format emitted by the
genesis tool.

# Deploy contracts:

```
$ cargo run

Deploying CIS2-Bridgeable....
Module with reference 56a6ca3243935653bf3b271aa1257a3f9351663757c66a498750d4622f81c08f already exists.
Deployed CIS2-Bridgeable, module_ref: 56a6ca3243935653bf3b271aa1257a3f9351663757c66a498750d4622f81c08f

Deploying Bridge-Manager....
Module with reference 4dae844ef592e011b67d4c44da9604232976857fcf8ad8d14438afe6125d6c24 already exists.
Deployed Bridge-Manager, module_ref: 4dae844ef592e011b67d4c44da9604232976857fcf8ad8d14438afe6125d6c24

Initializing BridgeManager....
Sent tx: ea5376d2a58a268fd06188840fea46e1f9b09ce2eaa0d929eebd771f6c622588
Transaction finalized, tx_hash=ea5376d2a58a268fd06188840fea46e1f9b09ce2eaa0d929eebd771f6c622588 contract=(605, 0)
Initialized BridgeManager, address: (605, 0)
Granting Manager address Manager role on BridgeManager....
Sent tx: 8e7883a2a9e49cdc5f9181df851f0ba6cf8ab8051ba559713233703b505b4d83
Granted Manager address Manager role on BridgeManager

Initializing CIS2-Bridgeable MOCK.et....
Sent tx: 9dcaac74c42e0cc23b4b02be7c688e8c7f8e48779b69d52690ab76aa3c939fef
Transaction finalized, tx_hash=9dcaac74c42e0cc23b4b02be7c688e8c7f8e48779b69d52690ab76aa3c939fef contract=(606, 0)
Initialized CIS2-Bridgeable MOCK.et at address: (606, 0)
Granting BridgeManager Manager role on MOCK.et token....
Sent tx: 8707603fc0dd1e2733c9e6b77ff341e576f12dd0076620aaec6e28f15f77357b
Granted BridgeManager Manager role on MOCK.et token

Initializing CIS2-Bridgeable USDC.et....
Sent tx: 5dc31a314dc1c512c1ba355d05224e308de9cb31334ad8412a0914a2b1796000
Transaction finalized, tx_hash=5dc31a314dc1c512c1ba355d05224e308de9cb31334ad8412a0914a2b1796000 contract=(607, 0)
Initialized CIS2-Bridgeable USDC.et at address: (607, 0)
Granting BridgeManager Manager role on USDC.et token....
Sent tx: e1db48b78699cbfb6bc2585745fcb1378de115e23e833999bc0c2589d8ede154
Granted BridgeManager Manager role on USDC.et token
```
