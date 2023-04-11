//! Functionality and types for invoking contract entrypoints.
//!
//! Contract invocation is effectful and transactional.
//! We therefore keep track of changes during execution in a
//! [`ChangeSet`][types::ChangeSet].
//!
//! Once the execution (transaction) has finished, the changes can then be
//! persisted (saved) or discarded, dependent on whether it succeeded or not.
//!
//! The changes that may occur are:
//!  - Mutations to contract state,
//!  - Contract upgrades (changing the module),
//!  - Balances of contracts and accounts.

mod impls;
mod types;
pub(crate) use types::{ChangeSet, EntrypointInvocationHandler, TestConfigurationError};
