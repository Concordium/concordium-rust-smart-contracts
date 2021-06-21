# Changelog

## Unreleased changes
- Validate contract and receive names
- Improve precision of error locations in init and receive_workers
- Improve precision of error locations for `size_length`
- Unify the `map_size_length`, `set_size_length`, and `string_size_length`
  into `size_length`.
- Make `ensure_ordered` work without having to specify a size length.

## concordium-std-derive 0.5.0 (2021-05-12)

- Add macros for deriving error implementations.
- Make derive macros slightly more hygienic.
