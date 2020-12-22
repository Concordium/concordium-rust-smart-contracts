# Changelog

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
