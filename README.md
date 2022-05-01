# Standard library for writing smart contracts for the Concordium blockchain

[![Contributor Covenant](https://img.shields.io/badge/Contributor%20Covenant-2.0-4baaaa.svg)](https://github.com/Concordium/.github/blob/main/.github/CODE_OF_CONDUCT.md)

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

These contracts are not meant for production, they are used to illustrate how to use
the standard library and the tooling Concordium provides. There is no claim that
the logic of the contract is reasonable, or safe.

**Do not use these contracts as-is for anything other then experimenting.**

## Submodules

The repository has
[concordium-contracts-common](https://github.com/Concordium/concordium-contracts-common)
as a submodule, and testing and builds are set-up to use the submodule version.
When changes are made in `concordium-contracts-common` they should be propagated
to this repository.

## Contributing

[![Contributor Covenant](https://img.shields.io/badge/Contributor%20Covenant-2.0-4baaaa.svg)](https://github.com/Concordium/.github/blob/main/.github/CODE_OF_CONDUCT.md)

This repository's CI automatically checks formatting and common problems in rust.
Changes to any of the packages must be such that

- ```cargo clippy --all``` produces no warnings
- ```rustfmt``` makes no changes.

Everything in this repository should build with rust version 1.53 (it should work with 1.51 and up, but we do not test regularly) however the `fmt` tool must be from a nightly release since some of the configuration options are not stable. One way to run the `fmt` tool is
```
cargo +nightly-2021-06-09 fmt
```

(the exact version used by the CI can be found in [.github/workflows/linter.yml](.github/workflows/linter.yml) file).
You will need to have a recent enough nightly version installed, which can be done via

```
rustup toolchain install nightly-2021-06-09
```

or similar, using the [rustup](https://rustup.rs/) tool. See the documentation of the tool for more details.

In order to contribute you should make a pull request and ask at least two people familiar with the code to do a review.
