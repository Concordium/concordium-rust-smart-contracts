## Standard library for writing smart contracts for the Concordium blockchain.

This repository consists of the core standard library for writing smart
contracts for the Concordium blockchain in the Rust programming languages, as
well as some sample smart contracts. The core libraries are
[concordium-std](./concordium-std) and its helper crate of procedural macros
[concordium-std-derive](./concordium-std-derive).

The procedural macros reduce the amount of boilerplate the user needs to write,
while the `concordium-std` library exposes a high-level API that smart contract
writers can use when writing contracts, alleviating them from the need to deal
with low-level details of how the interaction with the chain works.

## Examples

The [examples](./examples) directory contains some smart contracts that are used
to test the standard library.

Contracts are not meant for production, they are used to illustrate how to use
the standard library and the tooling Concordium provides. There is no claim that
the logic of the contract is reasonable, or safe.

**Do not use these contracts as-is for anything other then experimenting.**

The list of contracts is as follows
- [two-step-transfer](./examples/two-step-transfer) A contract that acts like an
 account (can send, store and accept GTU), but requires n > 1 ordained accounts
 to agree to the sending of GTU before it is accepted.

## Submodules

The repository has
[concordium-contracts-common](https://github.com/Concordium/concordium-contracts-common)
as a submodule, and testing and builds are set-up to use the submodule version.
When changes are made in `concordium-contracts-common` they should be propagated
to this repository.
