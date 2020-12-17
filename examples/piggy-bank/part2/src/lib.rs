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
//! - Unit testing
//! - Custom errors

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

#[derive(Debug, PartialEq, Eq)]
enum SmashError {
    NotOwner,
    AlreadySmashed,
}

/// Smash a piggy bank retrieving the money, only allowed by the owner.
#[receive(contract = "PiggyBank", name = "smash")]
fn piggy_smash<A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: &mut PiggyBankState,
) -> Result<A, SmashError> {
    // Get the contract owner, i.e. the account who initialized the contract.
    let owner = ctx.owner();
    // Get the sender, who triggered this function, either a smart contract or
    // an account.
    let sender = ctx.sender();

    // Ensure only the owner can smash the piggy bank.
    ensure!(sender.matches_account(&owner), SmashError::NotOwner);
    // Ensure the piggy bank have not been smashed already.
    ensure!(*state == PiggyBankState::Intact, SmashError::AlreadySmashed);
    // Set the state to be smashed.
    *state = PiggyBankState::Smashed;

    // Get the current balance of the smart contract.
    let balance = ctx.self_balance();
    // Result in a transfer of the whole balance to the contract owner.
    Ok(A::simple_transfer(&owner, balance))
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
        let ctx = InitContextTest::empty();

        // Call the init function
        let result = piggy_init(&ctx);

        // Inspect the result
        let state = match result {
            Ok(state) => state,
            Err(_) => fail!("Contract initialization failed."),
        };

        claim_eq!(
            state,
            PiggyBankState::Intact,
            "Piggy bank state should be intact after initialization."
        );
    }

    #[concordium_test]
    fn test_insert_intact() {
        // Setup
        let ctx = ReceiveContextTest::empty();
        let amount = Amount::from_micro_gtu(100);
        let mut state = PiggyBankState::Intact;

        // Trigger the insert
        let result: ReceiveResult<ActionsTree> = piggy_insert(&ctx, amount, &mut state);

        // Inspect the result
        let actions = match result {
            Ok(actions) => actions,
            Err(_) => fail!("Contract initialization failed."),
        };

        claim_eq!(state, PiggyBankState::Intact, "Piggy bank state should still be intact.");
        claim_eq!(actions, ActionsTree::accept(), "No action should be produced.");
    }

    #[concordium_test]
    fn test_insert_smashed() {
        // Setup
        let ctx = ReceiveContextTest::empty();
        let amount = Amount::from_micro_gtu(100);
        let mut state = PiggyBankState::Smashed;

        // Trigger the insert
        let result: ReceiveResult<ActionsTree> = piggy_insert(&ctx, amount, &mut state);

        // Inspect the result
        claim!(result.is_err(), "Should failed when piggy bank is smashed.");
    }

    #[concordium_test]
    fn test_smash_intact() {
        // Setup the context
        let owner = AccountAddress([0u8; 32]);
        let amount = Amount::from_micro_gtu(100);

        let mut ctx = ReceiveContextTest::empty();
        ctx.set_owner(owner);
        ctx.set_self_balance(amount);
        ctx.set_sender(Address::Account(owner));

        let mut state = PiggyBankState::Intact;

        // Trigger the smash
        let result: Result<ActionsTree, _> = piggy_smash(&ctx, &mut state);

        // Inspect the result
        let actions = match result {
            Ok(actions) => actions,
            Err(_) => fail!("Contract initialization failed."),
        };
        claim_eq!(actions, ActionsTree::simple_transfer(&owner, amount));
    }

    #[concordium_test]
    fn test_smash_intact_not_owner() {
        // Setup the context
        let owner = AccountAddress([0u8; 32]);
        let sender = Address::Account(AccountAddress([1u8; 32]));
        let amount = Amount::from_micro_gtu(100);

        let mut ctx = ReceiveContextTest::empty();
        ctx.set_owner(owner);
        ctx.set_self_balance(amount);
        ctx.set_sender(sender);

        let mut state = PiggyBankState::Intact;

        // Trigger the smash
        let result: Result<ActionsTree, _> = piggy_smash(&ctx, &mut state);

        match result {
            Ok(_) => fail!("Contract is expected to fail."),
            Err(err) => {
                claim_eq!(err, SmashError::NotOwner, "Expected to fail with error NotOwner")
            }
        };
    }

    #[concordium_test]
    fn test_smash_smashed() {
        // Setup the context
        let owner = AccountAddress([0u8; 32]);
        let sender = Address::Account(owner);
        let amount = Amount::from_micro_gtu(100);

        let mut ctx = ReceiveContextTest::empty();
        ctx.set_owner(owner);
        ctx.set_self_balance(amount);
        ctx.set_sender(sender);

        let mut state = PiggyBankState::Smashed;

        // Trigger the smash
        let result: Result<ActionsTree, _> = piggy_smash(&ctx, &mut state);

        match result {
            Ok(_) => fail!("Contract is expected to fail."),
            Err(err) => claim_eq!(
                err,
                SmashError::AlreadySmashed,
                "Expected  to fail with error AlreadySmashed"
            ),
        };
    }
}
