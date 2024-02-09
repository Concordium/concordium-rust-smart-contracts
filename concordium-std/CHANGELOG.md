# Changelog

## Unreleased changes

## concordium-std 9.0.2 (2024-02-07)

- Make the `concordium_dbg!` and related macros also usable with the full syntax
  that `println!` supports.
- Remove the feature `wee_alloc` and replace it with `bump_alloc`, which enables a small and simple global allocator that can only be used in Wasm.

## concordium-std 9.0.1 (2024-01-26)

- Fix a bug that caused a linking error when using `concordium_dbg!` on some
  platforms.
  - The error message states that `_debug_print` cannot be found.

## concordium-std 9.0.0 (2024-01-22)

- Add a `concordium_dbg!` macro and the associated `debug` feature to enable,
  together with `cargo concordium`, to emit debug information during contract
  execution.
- Update `concordium-contracts-common` dependency to version `9`.

## concordium-std 8.1.0 (2023-10-18)

- Set minimum Rust version to 1.66.
- Fix bug in `StateMap::get_mut`, which allowed multiple mutable references to the state to coexist.
  - The signature has changed using `&self` to using `&mut self`.
- Deprecate the `test_infrastructure` module in favour of [concordium-smart-contract-testing](https://docs.rs/concordium-smart-contract-testing).
  - Several traits are also deprecated as they are only needed when using the `test_infrastructure` for testing.
  - Among the traits are `HasHost`, `HasStateApi`, `HasInitContext`, `HasReceiveContext`.
    - They are replaced by concrete types, e.g. `Host`, `StateApi`, etc. in the documentation and nearly all example contracts.
  - Add a section in the library documentation about how to migrate your contracts and tests.

## concordium-std 8.0.0 (2023-08-21)

- Support adding attribute `#[concordium(repr(u))]` for enum types, where `u` is either `u8` or `u16`. Setting this changes the integer serialization used for the variant tags in derive macros such as  `Serial`, `Deserial`, `DeserialWithState` and `SchemaType`.
- Support adding attribute `#[concordium(tag = n)]` for enum variants, where `n` is some unsigned integer literal. Setting this attribute on a variant overrides the tag used in derive macros such as `Serial`, `Deserial`, `DeserialWithState` and `SchemaType`. Note that setting `#[concordium(repr(u*))]` is required when using this attribute.
- Support adding `#[concordium(forward = n)]`, for enum variants, where `n` is either an unsigned integer literal, `cis2_events`, `cis3_events`, `cis4_events` or an array of the same options.
  Setting this attribute on a variant overrides the (de)serialization to flatten with the (de)serialization of the inner field when using derive macros such as `Serial`, `Deserial`, `DeserialWithState` and `SchemaType`.
  Note that setting `#[concordium(repr(u*))]` is required when using this attribute.
- Support protocol 6 smart contract extensions. In particular the `HasHost`
  trait is extended with two additional host operations, `account_public_keys`
  and `check_account_signature` corresponding to the two new host functions
  available in protocol 6. Two new types were added to support these operations,
  `AccountSignatures` and `AccountPublicKeys`.
- Contract state no longer needs to implement `StateClone` trait in order to work with test infrastructure.
  `StateClone` itself is completely removed

## concordium-std 7.0.0 (2023-06-16)

- Set minimum Rust version to 1.65.
- Move `MetadataUrl` from the CIS-2 library to `concordium-std` along with the schema and serialization to make it available to other CIS standards.
- Change the `MetadataUrl` schema: use hex string representation for `hash`.
- Introduce a new method `block_time` as an alias to `slot_time` in the `HasChainMetadata` trait.

## concordium-std 6.2.0 (2023-05-08)

- Add `write_root` helper function to write the root of the state trie. This is
  useful in migrations when upgrading smart contracts.
- Bump Rust edition to `2021`.
- Remove the use of `alloc_error_handler` since the feature is no longer
  available in recent nightly builds of the compiler. This can increase the
  smart contract size slightly.
- Set minimum Rust version to 1.60.

## concordium-std 6.1.1 (2023-03-16)

- Bump contracts-common to 5.3.1.

## concordium-std 6.1.0 (2023-03-16)

- Add `Display` implementation for `OwnedParameter` and `Parameter`, which uses
  hex encoding.
- Replace `From<Vec<u8>>` instance for `OwnedParameter`/`Parameter` with a `TryFrom`,
  which ensures a valid length, and the unchecked method `new_unchecked`.
  - Migrate from `From`/`Into`: Use `new_unchecked` instead (if known to be
    valid length).
- Make inner field in `OwnedParameter`/`Parameter` private, but add a `From`
  implementation for getting the raw bytes.
  - Migrate from `parameter.0`: use `parameter.into()` instead (for both of the affected
    types).
- For `ModuleReference`, replace `AsRef<[u8;32]>` with `AsRef<[u8]>` and make
  inner `bytes` field public.
  - The change was necessary for internal reasons.
  - Migrate from `module_reference.as_ref()`: use `&module_reference.bytes` instead.
- Replace `OwnedParameter::new` with `OwnedParameter::from_serial`, which also
  ensures a valid length.
  - Migrate from `new(x)`: Use `from_serial(x).unwrap()` (if known to be valid length).
- Add an `empty` method for both `OwnedParameter` and `Parameter`.
- Implement `Default` for `Parameter`.
- Add `StateBuilder::new_state_container` method which allows contract developers to use
  their own container types atop blockchain storage
- Move the type `AccountBalance` to `concordium-contracts-common`.

## concordium-std 6.0.1 (2023-02-28)

- Fix testing of crypto primitives using secp256k1 signature scheme.

## concordium-std 6.0.0 (2023-02-08)

- [`wee_alloc`](https://docs.rs/wee_alloc/latest/wee_alloc/index.html) is no
  longer set as the allocator in `concordium-std` but can be enabled via the
  feature `wee_alloc`. The consequence is that unless `std` feature is
  enabled either `wee_alloc` must be enabled, or another global allocator
  must be set in the smart contract. In `std` builds, unless `wee_alloc`
  feature is used, the allocator provided by the Rust standard library is used.

## concordium-std 5.1.0 (2022-12-14)

- Add a new primitive `get_random` for generating random numbers in Wasm code testing; `get_random` can be used in tests only, not available for smart contracts on the chain.
- Fix a linking issue when compiling contracts to native code on Windows and OSX.

## concordium-std 5.0.0 (2022-11-21)

- Add `upgrade` method to `HasHost` for upgrading a smart contract instance to use a new smart contract module.
- Support mocking `upgrade` calls in `TestHost`. An `upgrade` is mocked by specifying a module reference and a `UpgradeResult` as the outcome of upgrading to this module.
- Add the chain queries `account_balance`, `contract_balance` and `exchange_rates` to `HasHost` for querying balances and the current exchange rates.
- Support mocking chain queries `account_balance`, `contract_balance` and `exchange_rates` in `TestHost`. For each parameter a corresponding response can be setup.

## concordium-std 4.0.0 (2022-08-24)

- Add rollback functionality to the `TestHost`.
  - Add a function `TestHost::with_rollback` for calling receive functions,
    which rolls back the host and state if the receive function returns an error.
  - Add a `StateClone` trait.
    - The `TestHost` requires the `State` to implement `StateClone` (breaking change).
    - `StateClone` is implemented for all `Clone` types, and can be derived similarly to `DeserialWithState`.
  - Add the method `cursor_position` to the `Seek` trait.

## concordium-std 3.1.0 (2022-08-04)

- Change SchemaType implementation for cryptographic primitives to ByteArray, meaning that the primitives(e.g., hashes and signatures) are now supplied as hex strings in JSON.
- Add `Seek` requirement for `HasParameter`.
- Implement `Seek` for `ExternParameter`.
- Add wrapper type `TestParameterCursor` instead of exposing `Cursor` directly, when using `TestContext`. This is changing the type returned by `parameter_cursor` for `TestContext`, but provides the same interface.
- Make using policies more ergonomic
  - Add `attributes` method to `HasPolicy` that gives an iterator over `(AttributeTag, AttributeValue)`.
  - Change `OwnedPolicy` to use `AttributeValue` instead of `OwnedAttributeValue` (breaking change)

## concordium-std 3.0.0 (2022-05-17)
- Remove support for v0 smart contracts and add support for v1:
  - Replace message passing with synchronous calls:
    - Remove the `Action` type.
    - Add `HasHost`, which has (synchronous) functions for making
      transfers, `invoke_transfer`, and calling other contracts, `invoke_contract`.
  - Enable arbitary, serializable, return values for contract functions.
  - Overhaul test infrastructure to support v1 contracts:
    - Add ability to mock contract invocations.
    - Add a number of helper functions and types to ease testing.
  - Change of the contract state works
    - Make the state a tree of byte arrays instead of a bytearray.
    - Remove the 16kb limit to state size.
    - Introduce high-level abstractions over the new state, including the
      `StateBuilder`, `StateMap`, `StateSet`, and `StateBox`.
    - Add new traits for the low-level state interaction: `HasStateApi` and `HasStateEntry`.
  - The Seek trait now works with i32 instead of i64. This is more efficient,
    and sufficient for the target architecture.
- Expose the module of primitive host functions with an unsafe API.
- Add cryptographic primitives:
  - Add a new attribute `crypto-primitives` (on both init and receive functions), which gives the function an additional parameter, `&impl HasCryptoPrimitives`.
  - Add the trait `HasCryptoPrimitives` with two implementations (host-backed + test).
   - For the test implementation, the default option uses mocks. But the actual implementations can be used if you enable the feature `crypto-primitives`.
  - Add new feature flag `crypto-primitives`.

## concordium-std 2.0.0 (2022-01-05)

- Update references to token to match token name (CCD).
- Improve `claim_eq` and `claim_ne` macros such that:
  - Arguments are only evaluated once.
  - Type inference works as you would expect.

## concordium-std 1.0.0 (2021-10-05)

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
