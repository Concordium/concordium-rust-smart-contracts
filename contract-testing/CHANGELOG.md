# Changelog

## Unreleased changes

- Add methods to `Chain` for setting the exchange rates and block time based on queries from an external node.
  - Add the method `setup_external_node_connection` for configuring the external node to use.
  - Add the method `set_exchange_rates_via_external_node` for setting the exchange rates.
  - Add the method `set_block_time_via_external_node` for setting the block time.
  - Add the method `block_time` to get the current block time.
  - Add the method `sticky_block` for viewing the "sticky block", a concept explained in the `*via_external_node` methods.
- Add the `BlockHash` type (re-exported from internal crate) for use in the methods above.

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
