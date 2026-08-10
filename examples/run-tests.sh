#!/usr/bin/env bash

# This scripts runs the tests in all the smart contract crates using cargo concordium. The script exists because
# cargo concordium does not support workspace invocation of tests yet.

cd "$(dirname "$0")"

# The example crates, as listed in the workspace `Cargo.toml` members.
CRATES=(
    account-signature-checks
    auction
    bump-alloc-tests
    cis2-dynamic-nft
    cis2-multi
    cis2-multi-royalties
    cis2-nft
    cis2-wccd
    cis3-nft-sponsored-txs
    cis5-smart-contract-wallet
    counter-notify
    credential-registry
    eSealing
    factory
    fib
    icecream
    memo
    nametoken
    offchain-transfers
    piggy-bank/part1
    piggy-bank/part2
    proxy
    recorder
    signature-verifier
    smart-contract-upgrade/contract-version1
    smart-contract-upgrade/contract-version2
    sponsored-tx-enabled-auction
    transfer-policy-check
    two-step-transfer
    voting
)

# Some examples need another example's compiled Wasm module available before
# their tests can run. Build those modules up front so ordering never matters:
#   - smart-contract-upgrade/contract-version1 upgrades to contract-version2.
#   - sponsored-tx-enabled-auction and cis5-smart-contract-wallet use cis2-multi.
PREREQUISITES=(
    smart-contract-upgrade/contract-version2
    cis2-multi
)

failed=()

for crate in "${PREREQUISITES[@]}"; do
    if ! ( cd "$crate" && cargo concordium build); then
        exit 1
    fi
done

for crate in "${CRATES[@]}"; do
    if ! ( cd "$crate" && cargo concordium test); then
        exit 1
    fi
done
