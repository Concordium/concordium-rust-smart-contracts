# Changelog

## Unreleased changes
- Add error codes for the new cases in NewContractNameError and NewReceiveNameError:
  - `NewContractNameError::ContainsDot` is mapped to `i32::MIN + 9`
  - `NewContractNameError::InvalidCharacters` is mapped to `i32::MIN + 10`
  - `NewReceiveNameError::InvalidCharacters` is mapped to `i32::MIN + 11`
- Change error code for when a contract that was not marked as payable received
  tokens. The error code is now `i32::MIN + 12`, changed from the previous `-1`.
- Export `HashMap` and `HashSet` from `contract-common` in `collections` module.
- Added implementation of `SerialCtx` for `Vec`.
- Export `Box` when no `std` feature.
- Bump minimum supported Rust version to 1.51.
- Deriving SchemaType supports types with generics.

## concordium-std 0.5.0 (2021-05-12)

- Make Write implementation for ContractStateTest resize the state automatically
  to be consistent with the Write implementation for ContractState.
- Use little-endian encoding for sender contract addresses in receive contexts. This
  reverts the change in concordium-std 0.4.1.
- Change the `receive_name` parameter of `HasActions::send` to use `ReceiveName`
  instead of `str`.
- Rename `send` to `send_raw` in `HasActions`.
- Rename `log_bytes` to `log_raw` in `HasLogger`.
- Add `send`, a wrapper for `HasActions::send_raw`, which automatically
  serializes `parameter` (using `Serial`).
- Allow init and receive methods to return custom error codes that will be displayed to the user
  if a smart-contract invocation fails.
- Add i128 and u128 support to serialization and schema.

## concordium-std 0.4.1 (2021-02-22)

- Fix endianness mismatch when getting the sender contract address.
- Add PhantomData Serial/Deserial implementation.
- Add ContractStateTest wrapper with a HasContractState implemenation to enable testing with a low-level interface.

## concordium-std 0.4.0 (2021-01-08)

- Remove some chain details from ChainMetadata. Only the slot time remains.

## concordium-std 0.3.1 (2020-12-21)

### Added
- A trait `ExpectErrReport` with a method `expect_err_report` that works
  analogously to the
  [expect_err](https://doc.rust-lang.org/std/result/enum.Result.html#method.expect_err)
  and
  [expect_none](https://doc.rust-lang.org/std/option/enum.Option.html#method.expect_none)
  methods on the Result and Option types, respectively, except it invokes the
  [fail](https://docs.rs/concordium-std/0.3.1/concordium_std/macro.fail.html)
  macro instead of panic.

  The trait is implemented for
  [Result](https://doc.rust-lang.org/std/result/enum.Result.html) and
  [Option](https://doc.rust-lang.org/stable/std/option/enum.Option.html) types.

### Changed

### Fixed
