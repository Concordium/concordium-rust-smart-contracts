# Standard library for writing smart contracts for the Concordium blockchain.

This repository consists of two Rust crates, [concordium-std](./concordium-std)
and [concordium-std-derive](./concordium-std-derive).

The latter contains procedural macros for reducing the amount of boilerplate the
user needs to write, while the former exposes a high-level API that smart
contract writers can use when writing contracts, alleviating them from the need
to deal with low-level details of how the interaction with the chain works.
