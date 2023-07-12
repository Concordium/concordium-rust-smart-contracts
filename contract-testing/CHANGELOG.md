# Changelog

## Unreleased changes

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
