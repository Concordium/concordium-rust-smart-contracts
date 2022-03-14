//! Piggy bank smart contract.
//!
//! Allows anyone to insert CCD, but only the owner can "smash" it and
//! retrieve the CCD. Prevents more CCD to be inserted after being smashed.
//!
//! This smart contract module is developed as part of the
//! [Piggy Bank Tutorial](https://developer.concordium.software/en/mainnet/smart-contracts/tutorials/piggy-bank).
//!
//! Covers:
//! - Reading owner, sender and self_balance from the context and host.
//! - The `ensure` macro.
//! - The `payable` attribute.
//! - The `mutable` attribute.
//! - Invoking a transfer with the host.

// Pulling in everything from the smart contract standard library.
use concordium_std::*;

/// The state of the piggy bank
#[derive(Debug, Serialize, PartialEq, Eq)]
enum PiggyBankState {
    /// Alive and well, allows for CCD to be inserted.
    Intact,
    /// The piggy bank has been emptied, preventing further CCD to be inserted.
    Smashed,
}

/// Setup a new Intact piggy bank.
#[init(contract = "PiggyBank")]
fn piggy_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<PiggyBankState> {
    // Always succeeds
    Ok(PiggyBankState::Intact)
}

/// Insert some CCD into a piggy bank, allowed by anyone.
#[receive(contract = "PiggyBank", name = "insert", payable)]
fn piggy_insert<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<PiggyBankState, StateApiType = S>,
    _amount: Amount,
) -> ReceiveResult<()> {
    // Ensure the piggy bank has not been smashed already.
    ensure!(*host.state() == PiggyBankState::Intact);
    // Just accept since the CCD balance is managed by the chain.
    Ok(())
}

/// Smash a piggy bank retrieving the CCD, only allowed by the owner.
#[receive(contract = "PiggyBank", name = "smash", mutable)]
fn piggy_smash<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<PiggyBankState, StateApiType = S>,
) -> ReceiveResult<()> {
    // Get the contract owner, i.e. the account who initialized the contract.
    let owner = ctx.owner();
    // Get the sender, who triggered this function, either a smart contract or
    // an account.
    let sender = ctx.sender();

    // Ensure only the owner can smash the piggy bank.
    ensure!(sender.matches_account(&owner));
    // Ensure the piggy bank has not been smashed already.
    ensure!(*host.state() == PiggyBankState::Intact);
    // Set the state to be smashed.
    *host.state_mut() = PiggyBankState::Smashed;

    // Get the current balance of the smart contract.
    let balance = host.self_balance();
    // Result in a transfer of the whole balance to the contract owner.
    Ok(host.invoke_transfer(&owner, balance)?)
}
