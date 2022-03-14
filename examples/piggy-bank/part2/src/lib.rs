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
//! - Unit testing, targeting Wasm.
//! - Custom errors.

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

#[derive(Debug, PartialEq, Eq, Reject)]
enum SmashError {
    NotOwner,
    AlreadySmashed,
    TransferError, // If this occurs, there is a bug in the contract.
}

/// Smash a piggy bank retrieving the CCD, only allowed by the owner.
#[receive(contract = "PiggyBank", name = "smash", mutable)]
fn piggy_smash<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<PiggyBankState, StateApiType = S>,
) -> Result<(), SmashError> {
    // Get the contract owner, i.e. the account who initialized the contract.
    let owner = ctx.owner();
    // Get the sender, who triggered this function, either a smart contract or
    // an account.
    let sender = ctx.sender();

    // Ensure only the owner can smash the piggy bank.
    ensure!(sender.matches_account(&owner), SmashError::NotOwner);
    // Ensure the piggy bank has not been smashed already.
    ensure!(*host.state() == PiggyBankState::Intact, SmashError::AlreadySmashed);
    // Set the state to be smashed.
    *host.state_mut() = PiggyBankState::Smashed;

    // Get the current balance of the smart contract.
    let balance = host.self_balance();

    // Transfer the whole balance to the contract owner.
    let transfer_result = host.invoke_transfer(&owner, balance);
    // The transfer can never fail, since the owner is known to exist, and the
    // contract has sufficient balance.
    ensure!(transfer_result.is_ok(), SmashError::TransferError);

    Ok(())
}

// Unit tests for the smart contract "PiggyBank"
#[concordium_cfg_test]
mod tests {
    use super::*;
    // Pulling in the testing utils found in concordium_std.
    use test_infrastructure::*;

    // Running the initialization ensuring nothing fails and the state of the
    // piggy bank is intact.
    #[concordium_test]
    fn test_init() {
        // Setup
        let ctx = TestInitContext::empty();
        let mut state_builder = TestStateBuilder::new();

        // Call the init function
        let state_result = piggy_init(&ctx, &mut state_builder);

        // Inspect the result
        let state = state_result.expect_report("Contract initialization results in error.");

        claim_eq!(
            state,
            PiggyBankState::Intact,
            "Piggy bank state should be intact after initialization."
        );
    }

    #[concordium_test]
    fn test_insert_intact() {
        // Setup
        let ctx = TestReceiveContext::empty();
        let host = TestHost::new(PiggyBankState::Intact);
        let amount = Amount::from_micro_ccd(100);

        // Trigger the insert
        let result = piggy_insert(&ctx, &host, amount);

        claim!(result.is_ok(), "Inserting CCD results in error");
        assert_eq!(
            *host.state(),
            PiggyBankState::Intact,
            "Piggy bank state should still be intact."
        );
    }

    #[concordium_test]
    fn test_insert_smashed() {
        // Setup
        let ctx = TestReceiveContext::empty();
        let amount = Amount::from_micro_ccd(100);
        let host = TestHost::new(PiggyBankState::Smashed);

        // Trigger the insert
        let result = piggy_insert(&ctx, &host, amount);

        // Inspect the result
        claim!(result.is_err(), "Should fail when piggy bank is smashed.");
    }

    #[concordium_test]
    fn test_smash_intact() {
        // Setup the context

        let mut ctx = TestReceiveContext::empty();
        let owner = AccountAddress([0u8; 32]);
        ctx.set_owner(owner);
        let sender = Address::Account(owner);
        ctx.set_sender(sender);
        let mut host = TestHost::new(PiggyBankState::Intact);
        let balance = Amount::from_micro_ccd(100);
        host.set_self_balance(balance);

        // Trigger the smash
        let result = piggy_smash(&ctx, &mut host);

        // Inspect the result
        claim!(result.is_ok(), "Smashing intact piggy bank results in error.");
        claim_eq!(*host.state(), PiggyBankState::Smashed, "Piggy bank should be smashed.");
        claim_eq!(
            host.get_transfers(),
            [(owner, balance)],
            "Smashing did not produce the correct transfers."
        );
    }

    #[concordium_test]
    fn test_smash_intact_not_owner() {
        // Setup the context

        let mut ctx = TestReceiveContext::empty();
        let owner = AccountAddress([0u8; 32]);
        ctx.set_owner(owner);
        let sender = Address::Account(AccountAddress([1u8; 32]));
        ctx.set_sender(sender);
        let mut host = TestHost::new(PiggyBankState::Intact);
        let balance = Amount::from_micro_ccd(100);
        host.set_self_balance(balance);

        // Trigger the smash
        let result = piggy_smash(&ctx, &mut host);

        claim_eq!(result, Err(SmashError::NotOwner), "Expected to fail with error NotOwner.");
    }

    #[concordium_test]
    fn test_smash_smashed() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        let owner = AccountAddress([0u8; 32]);
        ctx.set_owner(owner);
        let sender = Address::Account(owner);
        ctx.set_sender(sender);
        let mut host = TestHost::new(PiggyBankState::Smashed);
        let balance = Amount::from_micro_ccd(100);
        host.set_self_balance(balance);

        // Trigger the smash
        let result = piggy_smash(&ctx, &mut host);

        claim_eq!(
            result,
            Err(SmashError::AlreadySmashed),
            "Expected to fail with error AlreadySmashed."
        );
    }

    #[concordium_test]
    fn test_smash_account_missing() {
        // This test tests a scenario that cannot occur. Namely that the transfer to the
        // owner account gives a MissingAccount error. The example, however, is
        // illustrative for how to test for transfers to missing accounts.

        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        let owner = AccountAddress([0u8; 32]);
        ctx.set_owner(owner);
        let sender = Address::Account(owner);
        ctx.set_sender(sender);
        let mut host = TestHost::new(PiggyBankState::Intact);
        let balance = Amount::from_micro_ccd(100);
        host.set_self_balance(balance);

        // By default, all accounts are assumed to exist.
        // This makes the owner account not exist, which will make transfers to it
        // return a TransferError::MissingAccount.
        host.make_account_missing(owner);

        // Trigger the smash
        let result = piggy_smash(&ctx, &mut host);

        claim_eq!(
            result,
            Err(SmashError::TransferError),
            "Expected to fail with error TransferError."
        );
    }
}
