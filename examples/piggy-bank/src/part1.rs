//! Piggy bank smart contract.
//!
//! Allows anyone to insert money, but only the owner can "smash" it and
//! retrieve the money. Prevents more money to be inserted after being smashed.
//!
//! This smart contract module is developed as part of a upcoming tutorial on
//! developing smart contracts.
//!
//! Covers:
//! - Reading owner, sender and self_balance from the context.
//! - The `ensure` macro.
//! - The `payable` attribute.
//! - Creating a simple transfer action.
//!

// Pulling in everything from the smart contract standard library.
use concordium_std::*;

/// The state of the piggy bank
#[derive(Debug, Serialize, PartialEq, Eq)]
enum PiggyBankState {
    /// Alive and well, allows for GTU to be inserted.
    Intact,
    /// The piggy bank have been emptied, preventing further GTU to be inserted.
    Smashed,
}

/// Setup a new Intact piggy bank.
#[init(contract = "PiggyBank")]
fn piggy_init(_ctx: &impl HasInitContext) -> InitResult<PiggyBankState> {
    // Always succeeds
    Ok(PiggyBankState::Intact)
}

/// Insert some GTU into a piggy bank, allowed by anyone.
#[receive(contract = "PiggyBank", name = "insert", payable)]
fn piggy_insert<A: HasActions>(
    _ctx: &impl HasReceiveContext,
    _amount: Amount,
    state: &mut PiggyBankState,
) -> ReceiveResult<A> {
    // Ensure the piggy bank have not been smashed already.
    ensure!(*state == PiggyBankState::Intact);
    // Just accept since the GTU balance is managed by the chain.
    Ok(A::accept())
}

/// Smash a piggy bank retrieving the money, only allowed by the owner.
#[receive(contract = "PiggyBank", name = "smash")]
fn piggy_smash<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut PiggyBankState,
) -> ReceiveResult<A> {
    // Get the contract owner, i.e. the account who initialized the contract.
    let owner = ctx.owner();
    // Get the sender, who triggered this function, either a smart contract or
    // an account.
    let sender = ctx.sender();

    // Ensure only the owner can smash the piggy bank.
    ensure!(sender.matches_account(&owner));
    // Ensure the piggy bank have not been smashed already.
    ensure!(*state == PiggyBankState::Intact);
    // Set the state to be smashed.
    *state = PiggyBankState::Smashed;

    // Get the current balance of the smart contract.
    let balance = ctx.self_balance();
    // Result in a transfer of the whole balance to the contract owner.
    Ok(A::simple_transfer(&owner, balance))
}
