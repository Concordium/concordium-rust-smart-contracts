# Changelog

## Unreleased changes

- Add `#[concordium_cfg_not_test]` macro, that excludes parts of code for testing.

## concordium-std-derive 2.0.0 (2022-01-05)

- Update references to token to match token name (CCD).

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
