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
- [ERC721](./erc721) A simple example implementation of the ERC721 non-fungible token standard.
- [memo](./memo/) An extremely minimal contract that can be used to
  mimic the memo feature. Normally a transfer between accounts cannot add any
  information other than the amount being transferred. Making transfers to this
  intermediate contract instead works around this limitation.
- [cis1-multi](./cis1-multi) An example implementation of the CIS-1 Concordium Token Standard
  containing multiple token types.
- [cis1-nft](./cis1-nft) An example implementation of the CIS-1 Concordium Token Standard
  containing NFTs.
- [cis1-wccd](./cis1-wccd) An example implementation of the CIS-1 Concordium Token Standard
  containing a single fungible token which is a wrapped CCD.
- [cis1-single-nft](./cis1-single-nft) An example implementation of the CIS-1 Concordium Token Standard
  specialized to contain a single non-fungible token per contract instance.
- [listing-cis1](./listing-cis1) An example implementation of a contract for listing CIS-1 tokens. It is specialized only to work with the above NFT contract `cis1-single-nft`.
