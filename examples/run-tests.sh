#!/usr/bin/env bash

# This scripts runs the tests in all the smart contract crates using cargo concordium. The script exists because
# cargo concordium does not support workspace invocation of tests yet.

cd "$(dirname "$0")"

# Read the list of crates from Cargo.toml
CRATES=( $(cargo metadata --no-deps --format-version 1 \
    | jq -r '.workspace_root as $r | .packages[].manifest_path | ltrimstr($r + "/") | rtrimstr("/Cargo.toml")') )

# Some crates tests need another crates compiled Wasm module available before
# their tests can run. Build those modules up front so ordering never matters:
#   - smart-contract-upgrade/contract-version1 upgrades to contract-version2.
#   - sponsored-tx-enabled-auction and cis5-smart-contract-wallet use cis2-multi.
PREREQUISITES=(
    smart-contract-upgrade/contract-version2
    cis2-multi
)

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
