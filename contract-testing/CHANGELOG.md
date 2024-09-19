# Changelog

## 4.3.0

- Integrate protocol version 7 cost semantics.
- The `ContractInvokeSuccess` and `ContractInvokeError` have additional fields
  that record where parts of the energy was allocated during execution.
- Add support for loading the contract under test with the `module_load_output` function. The module path is exposed by `cargo-concordium` through the `CARGO_CONCORDIUM_TEST_MODULE_OUTPUT_PATH` environment variable.
- Updated the Concordium Rust SDK to support the changes introduced in protocol 7.

## 4.2.0

- Add support for querying the module reference and contract name of an instance.
  This functionality is only available on-chain from protocol version 7.
- Bump minimum supported Rust version (MSRV) to `1.73`.

## 4.1.0

- Fix a bug in debug output. The events emitted before some contract queries
  (such as querying account balance) were not emitted in the debug output. To
  fix this, `DebugTraceElement` gets a new variant `Debug` to retain these
  events.

## 4.0.0

- Add support for debug output when running smart contracts. This adds a new
  `module_deploy_v1_debug` method to the `Chain` that allows debug symbols
  in the deployed module.
- Add `DebugInfoExt` trait that has convenience methods for printing debug
  information.
- Add `debug_trace` field to `DebugTraceElement` variants. This records both any
  information emitted by the `concordium_dbg!` macro of `concordium-std` as well
  as the trace of all the host function calls that occurred.
- Add `is_debug_enabled` function to detect whether tests are being run in debug
  mode or not. This function uses the `CARGO_CONCORDIUM_TEST_ALLOW_DEBUG`
  environment variable that is set by `cargo-concordium` when running in debug
  mode.

## 3.2.0

- Bump minimum supported Rust version to `1.67`.
- Re-export `AccountKeys`.

## 3.1.0

- Add functionality for setting the exchange rates and block time of the chain based on queries from an external node.
  - Configured via a builder pattern, see `Chain::builder`.
- Add methods to `Chain`:
  - `external_query_block` to get the default block used for external queries
  - `block_time` to get the block time
  - `tick_block_time` to increase the block time by a `Duration`
- Add the following types by re-exporting them from internal crates:
  - `BlockHash`
  - `Timestamp` which `SlotTime` is an alias of.
  - `Duration`
  - `Endpoint`
- Add methods to the `Chain` for adding external accounts and contracts and for invoking contracts on an external node.
  - See the `Chain` method `contract_invoke_external` for more details.
- Add helper method `parse_return_value` to `ContractInvokeError` and `ContractInvokeSuccess`.
- Bump minimum supported Rust version to `1.66`.

## 3.0.0

- Support protocol 6 semantics, in particular validation assumes protocol 6
  semantics now, allowing sign extension instructions and new operations for
  querying account's public keys, and checking signatures with account's keys.
- Add `AccountSignatures` structure.
- Add an `AccountAccessStructure` to the `Account` structure. This is a breaking
  change. Extend the constructors of `Account` to allow constructing accounts
  with this access structure.

## 2.0.0

- Include `ContractTraceElement`s for failed contract executions, including internal failures.
  - Introduce the enum `DebugTraceElement`, which has information about trace elements, including failed ones and the cause of error, and the energy usage.
  - On the `ContractInvokeSuccess` type:
    - Change the type of the `trace_elements` field to be `Vec<DebugTraceElement>` instead of `Vec<ContractTraceElement>`. (breaking change)
    - Add a helper method, `effective_trace_elements()`, to retrieve the "effective" trace elements, i.e., elements that were *not* rolled back.
      - These are the elements that were previously returned in the `trace_elements` field.
      - There is also a version of the method which clones: `effective_trace_elements_cloned()`.
    - To migrate existing code, replace `some_update.trace_elements` with `some_update.effective_trace_elements_cloned()`.
    - Add a helper method, `rollbacks_occurred()`, to determine whether any internal failures or rollbacks occurred.
  - On the `ContractInvokeError` type:
    - Include the field `trace_elements` of type `Vec<DebugTraceElements>` with the trace elements that were hitherto discarded. (breaking change)
    - To migrate, include the new field or use `..` when pattern matching on the type.

## 1.0.0

- The initial release of the library.
