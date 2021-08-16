Example smart contracts illustrating the use of the tools for developing smart
contracts in Rust.

Contracts are not meant for production, they are used to illustrate how to use
the standard library and the tooling Concordium provides. There is no claim that
the logic of the contract is reasonable, or safe.

**Do not use these contracts as-is for anything other then experimenting.**

The list of contracts is as follows
- [two-step-transfer](./two-step-transfer) A contract that acts like an account (can send, store and accept GTU),
 but requires n > 1 ordained accounts to agree to the sending of GTU before it is accepted.
- [auction](./auction) A contract implementing an simple auction.
- [piggy-bank](./piggy-bank) The smart contract created as part of the Piggy Bank tutorial.
- [ERC721](./erc721) A simple example implementation of the ERC721 non-fungible token standard.
- [memo](./memo/) An extremely minimal contract that can be used to
  mimic the memo feature. Normally a transfer between accounts cannot add any
  information other than the amount being transferred. Making transfers to this
  intermediate contract instead works around this limitation.
- [cts1-multi](./cts1-multi) An example implementation of the Concordium Token Standard
  containing multiple tokens all minted at contract initialization.
- [cts1-nft](./cts1-nft) An example implementation of the Concordium Token Standard
  containing a number of NFTs all minted at contract initialization.
- [cts1-wgtu](./cts1-wgtu) An example implementation of the Concordium Token Standard
  containing a single fungible token which is a wrapped GTU.
