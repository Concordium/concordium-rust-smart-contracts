# Changelog

## Unreleased changes

## concordium-std-derive 3.1.0 (2022-08-04)

- Removed `derive(Serial)` and `derive(Deserial)` (moved to `concordium-contracts-common-derive`).

## concordium-std-derive 3.0.0 (2022-05-17)

- Add `#[concordium_cfg_not_test]` macro, that excludes parts of code for testing.
- Add `derive(Deletable)` macro for deriving the `Deletable` trait.
- Add `derive(DeserialWithState)` macro.
- Change `receive` and `init` macros to support the new V1 contract state and
  sync calls.

## concordium-std-derive 2.0.0 (2022-01-05)

- Update references to token to match token name (CCD).
- Remove support for v0 smart contracts and add support for v1:
  - Update the code generated with `init` and `receive` attributes for v1.
  - Remove `contract_state` annotation.
  - Add `return_value` to the `init` and `receive` attributes.
    - It describes the schema for the return_value (similar to `parameter`).

## concordium-std-derive 1.0.0 (2021-10-05)

- Validate contract and receive names
- Improve precision of error locations in init and receive_workers
- Improve precision of error locations for `size_length`
- Unify the `map_size_length`, `set_size_length`, and `string_size_length`
  into `size_length`.
- Make `ensure_ordered` work without having to specify a size length.

## concordium-std-derive 0.5.0 (2021-05-12)

- Add macros for deriving error implementations.
- Make derive macros slightly more hygienic.
- Enable renaming of enum variants and field names for the schema with a
  `#[concordium(rename = "<new-name>")]` attribute.
