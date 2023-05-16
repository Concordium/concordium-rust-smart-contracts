# Changelog

## Unreleased

- Include `ContractTraceElement`s for failed contract executions, including internal failures.
  - Introduce the enum `DebugTraceElement`, which has information about trace elements, including failed ones and the cause of error, and the energy usage.
  - On the `ContractInvokeSuccess` type:
    - Change the type of the `trace_elements` to be `Vec<DebugTraceElement>` instead of `Vec<ContractTraceElement>`. (breaking change)
    - Add a helper method, `effective_trace_elements()`, to retrieve the "effective" trace elements, i.e., elements that were *not* rolled back.
      - These are the elements that were previously returned in the `trace_elements` field.
    - To migrate existing code, replace `some_update.trace_elements` with `some_update.effective_trace_elements().collect::<Vec<_>>()`, 
      and dereference elements of the list if necessary.
    - Add a helper method, `rollbacks_occurred()`, to determine whether any internal failures occurred. 
  - On the `ContractInvokeError` type:
    - Include the field `trace_elements` of type `Vec<DebugTraceElements>` with the trace elements that were hitherto discarded. (breaking change)
    - To migrate, include the new field or use `..` when pattern matching on the type.

## 1.0.0

- The initial release of the library.
