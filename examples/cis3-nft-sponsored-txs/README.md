**Sponsored Transaction Smart Contract**

**Prerequisites**

`cargo/rustup` and `cargo-concordium` needs to be [set up](https://developer.concordium.software/en/mainnet/smart-contracts/guides/quick-start.html).

**Commands**

Run the following command to compile the smart contract into the wasm module `contract.wasm.v1` with embedded schema:

```
crago concordium build -e --out contract.wasm.v1
```

Run the following command to run the unit and integration tests:

```
crago concordium test 
```
```
crago test 
```
