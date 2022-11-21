# Changelog

## Unreleased changes

## concordium-cis2 2.0.0 (2022-11-21)

- Update `concordium-std` to version 5.
- Add `From` implementation from types implementing `From<UpgradeError>`, `From<QueryAccountBalanceError>` or `From<QueryContractBalanceError>` to `Cis2Error`.
- Add SchemaType for Cis2Event<T, A>

## concordium-cis2 1.2.0 (2022-09-01)

- Add `TokenAmountU256`
- Fix overflow during deserialization of amounts.

## concordium-cis2 1.1.0 (2022-08-24)

- Update `concordium-std` to version 4.
- Support schemas for error types defined in the library.

## concordium-cis2 1.0.0

Initial release of the library.
