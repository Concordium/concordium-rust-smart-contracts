Example smart contracts illustrating the use of the tools for developing smart
contracts in Rust.

Contracts are not meant for production, they are used to illustrate how to use
the standard library and the tooling Concordium provides. There is no claim that
the logic of the contract is reasonable, or safe.

**Do not use these contracts as-is for anything other then experimenting.**

The list of contracts is as follows
- [two-step-transfer](./two-step-transfer) A contract that acts like an account (can send, store and accept GTU),
 but requires n > 1 ordained accounts to agree to the sending of GTU before it is accepted.
