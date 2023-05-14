Example smart contracts illustrating the use of the tools for developing smart
contracts in Rust.

Contracts are not meant for production, they are used to illustrate how to use
the standard library and the tooling Concordium provides. There is no claim that
the logic of the contract is reasonable, or safe.

**Do not use these contracts as-is for anything other then experimenting.**

The list of contracts is as follows
- [two-step-transfer](./two-step-transfer) A contract that acts like an account (can send, store and accept CCD),
 but requires n > 1 ordained accounts to agree to the sending of CCD before it is accepted.
- [auction](./auction) A contract implementing an simple auction.
- [piggy-bank](./piggy-bank) The smart contract created as part of the Piggy Bank tutorial.
- [memo](./memo/) An extremely minimal contract that can be used to
  mimic the memo feature. Normally a transfer between accounts cannot add any
  information other than the amount being transferred. Making transfers to this
  intermediate contract instead works around this limitation.
- [cis2-multi](./cis2-multi) An example implementation of the CIS-2 Concordium Token Standard
  containing multiple token types.
- [cis2-nft](./cis2-nft) An example implementation of the CIS-2 Concordium Token Standard
  containing NFTs.
- [cis2-wccd](./cis2-wccd) An upgradable example implementation of the CIS-2 Concordium Token Standard
  containing a single fungible token which is a wrapped CCD.
- [counter-notify](./counter-notify) A contract that works as a counter and can invoke another contract with the current counter value.
- [fib](./fib) A contract that calculates and stores the nth Fibonacci number by recursively calling itself.
- [icecream](./icecream) A contract for buying ice cream only when it is sunny. A weather service oracle smart contract is used.
- [proxy](./proxy) A proxy contract that can be put in front of another contract. It works with V0 as well as V1 smart contracts.
- [recorder](./recorder) A contract that records account addresses, and has an entry point to invoke transfers to all those addresses.
- [signature-verifier](./signature-verifier) An example of how to use `crypto_primitives`. The contract verifies an Ed25519 signature.
- [nametoken](./nametoken) An example of how to register and manage names as tokens in a smart contract.
- [voting](./voting) An example of how to conduct an election using a smart contract.
- [transfer-policy-check](./transfer-policy-check) A contract that showcases how to use policies.
- [eSealing](./eSealing) A contract implementing an eSealing service.
- [sponsoredTransactions](./cis3-nft-sponsored-txs) A contract implementing the sponsored transaction mechanism (CIS3 standard).
- [smartContractUpgrade](./smart-contract-upgrade) An example of how to upgrade a smart contract. The state is migrated during the upgrade.
- [credentialRegistryStorageContract](./credential-registry-storage-contract) The contract is used for storing credentials for the Web3Id infrastructure.

