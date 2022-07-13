#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::{collections::*, *};
use std::collections::HashSet;

type SettlementID = u64;

#[derive(Clone, Serialize, SchemaType)]
struct AddressAmount {
    address: AccountAddress,
    amount: Amount,
}

// A transfer consisting of possibly multiple inputs with different amounts and several receivers
#[derive(Clone, Serialize, SchemaType)]
struct Transfer {
    send_transfers: Vec<AddressAmount>,
    receive_transfers: Vec<AddressAmount>,
    //This is not used directly by the smart contract
    //it could contain information relevant to the judge
    meta_data: Vec<u8>,
}

#[derive(Clone, Serialize, SchemaType)]
struct Settlement {
    id: SettlementID,
    transfer: Transfer,
    finality_time: Timestamp,
}

#[derive(Serialize, SchemaType)]
struct ContractConfig {
    validator: AccountAddress,
    judge: AccountAddress,
    time_to_finality: Duration,
}

#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
pub struct State<S> {
    // The initial configuration of the contract
    config: ContractConfig,

    // The next settlement id
    next_id: SettlementID,

    // Proposed settlements
    settlements: Vec<Settlement>,

    // Balance sheet
    balance_sheet: StateMap<AccountAddress, Amount, S>,
}

#[derive(Debug, PartialEq, Eq, Reject)]
enum InitError {
    /// Failed parsing the parameter
    #[from(ParseError)]
    ParseParams,
}
type InitResult<A> = Result<A, InitError>;

#[derive(Debug, PartialEq, Eq, Reject)]
enum ReceiveError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Sender cannot be a contract,
    ContractSender,
    /// Not enough funds
    InsufficientFunds,
    /// Invalid settlement
    InvalidTransfer,
    /// End time is not expressible, i.e., would overflow.
    TimeOverflow,
    /// We have reached the end of our IDs (unlikely to happe)
    CounterOverflow,
    /// Not authorized as validator
    NotAValidator,
    /// Not authorized as judge
    NotAJudge,
    /// Cannot withdraw 0 CCDs
    ZeroWithdrawal,
}
type ContractResult<A> = Result<A, ReceiveError>;

// Initialize contract with empty balance sheet and no settlements
#[init(contract = "offchain-transfers", parameter = "ContractConfig")]
#[inline(always)]
fn contract_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S>> {
    let config: ContractConfig = ctx.parameter_cursor().get()?;
    let state = State {
        config,
        next_id: 0u64,
        settlements: Vec::new(),
        balance_sheet: state_builder.new_map(),
    };

    Ok(state)
}

// Deposit amount of CCD to the smart contract and add amount to balance sheet of sender
#[receive(contract = "offchain-transfers", name = "deposit", payable, mutable)]
#[inline(always)]
fn contract_receive_deposit<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    amount: Amount,
) -> ContractResult<()> {
    let sender_address = match ctx.sender() {
        Address::Contract(_) => bail!(ReceiveError::ContractSender),
        Address::Account(account_address) => account_address,
    };
    let mut balance = host
        .state_mut()
        .balance_sheet
        .entry(sender_address)
        .or_insert(Amount::zero());
    *balance += amount;

    Ok(())
}

// Withdraw amount from smart contract.
// Only possible if the the user has sufficient funds in the worst case,
// i.e., even if all outstanding payments to that user get cancelled and all payments from that user are valid,
// there should be enough funds left to withdraw the requested payout.
#[receive(
    contract = "offchain-transfers",
    name = "withdraw",
    mutable,
    parameter = "Amount"
)]
#[inline(always)]
fn contract_receive_withdraw<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    let sender_address = match ctx.sender() {
        Address::Contract(_) => bail!(ReceiveError::ContractSender),
        Address::Account(account_address) => account_address,
    };

    let payout: Amount = ctx.parameter_cursor().get()?;
    // The payout needs to be strictly positive
    ensure!(payout > Amount::zero(), ReceiveError::ZeroWithdrawal);

    // get expenses that the user has in the balance sheet
    let mut expenses = Amount::zero();
    for settlement in host.state().settlements.iter() {
        for sender in settlement.transfer.send_transfers.iter() {
            if sender_address == sender.address {
                expenses += sender.amount;
            }
        }
    }

    {
        // ensure that user has sufficient funds even in the worst case if all expenses are deducted and nothing is added
        let mut balance = host
            .state_mut()
            .balance_sheet
            .entry(sender_address)
            .occupied_or(ReceiveError::InsufficientFunds)?;
        ensure!(
            *balance >= expenses + payout,
            ReceiveError::InsufficientFunds
        );

        // execute transfer
        *balance -= payout;
    }
    host.invoke_transfer(&sender_address, payout).unwrap_abort();

    Ok(())
}

/// Checks whether a transfer is synatically valid.
/// That is, it checks that the sent and received amounts match
fn is_settlement_transfer(transfer: &Transfer) -> bool {
    let mut send_amount = Amount::zero();
    let mut receive_amount = Amount::zero();

    for send_transfer in &transfer.send_transfers {
        send_amount += send_transfer.amount;
    }
    for receive_transfer in &transfer.receive_transfers {
        receive_amount += receive_transfer.amount;
    }

    // settlement is valid if sent and received amounts match
    send_amount == receive_amount
}

/// Allows the validator to add new settlements.
/// The validator provides the Transfer part while the smart contracts add the id and the finality time.
/// The call is lazy in the sense that it does not check whether the settlement could be applied to the current balance sheet
/// We use an increasing
#[receive(
    contract = "offchain-transfers",
    name = "add-settlement",
    mutable,
    parameter = "Transfer"
)]
#[inline(always)]
fn contract_receive_add_settlement<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    let sender = ctx.sender();
    //Only the validator may call this function
    ensure!(
        sender.matches_account(&host.state().config.validator),
        ReceiveError::NotAValidator
    );

    let transfer: Transfer = ctx.parameter_cursor().get()?;

    //Syntactically verify transfer information
    ensure!(
        is_settlement_transfer(&transfer),
        ReceiveError::InvalidTransfer
    );

    //Create a new settlement
    let now = ctx.metadata().slot_time();
    let settlement = Settlement {
        id: host.state().next_id,
        transfer,
        finality_time: now
            .checked_add(host.state().config.time_to_finality)
            .ok_or(ReceiveError::TimeOverflow)?,
    };
    //Increase ID counter
    host.state_mut()
        .next_id
        .checked_add(1)
        .ok_or(ReceiveError::CounterOverflow);
    //Add settlement
    host.state_mut().settlements.push(settlement);
    Ok(())
}

// Veto a settlement. Removes this settlement from the list of outstanding settlements.
// Only the judge is allowed to call this function. Furthermore, it must be called before the finality_time of the settlement.
#[receive(contract = "offchain-transfers", name = "veto", payable, mutable)]
#[inline(always)]
fn contract_receive_veto<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {
    let sender = ctx.sender();
    //Only the validator may call this function
    ensure!(
        sender.matches_account(&host.state().config.validator),
        ReceiveError::NotAJudge
    );
    let s_id: SettlementID = ctx.parameter_cursor().get()?;

    // delete all settlements with the given ID from the list
    host.state_mut().settlements.retain(|s| s.id != s_id);

    Ok(())
}

fn is_settlement_valid<S: HasStateApi>(
    settlement: &Settlement,
    balance_sheet: &StateMap<AccountAddress, Amount, S>,
) -> bool {
    // check whether all senders have sufficient funds with respect to the updated state
    // first get set of all senders (to avoid duplicate checks) and then check for each sender in set
    let mut sender_addresses = HashSet::new();
    for send_transfer in settlement.transfer.send_transfers.iter() {
        sender_addresses.insert(send_transfer.address);
    }
    for sender_address in sender_addresses {
        // get current balance of sender
        let mut sender_balance = Amount::zero();
        if let Some(sender_amount) = balance_sheet.get(&sender_address) {
            sender_balance = *sender_amount;
        }

        // get total amount of outgoing transactions
        let mut outgoing_amount = Amount::zero();
        for sender in settlement.transfer.send_transfers.iter() {
            if sender_address == sender.address {
                outgoing_amount += sender.amount;
            }
        }

        // get total amount of incoming transactions
        let mut incoming_amount = Amount::zero();
        for receiver in settlement.transfer.receive_transfers.iter() {
            if sender_address == receiver.address {
                incoming_amount += receiver.amount;
            }
        }

        if sender_balance + incoming_amount < outgoing_amount {
            return false;
        }
    }

    true
}

// Execute all settlements with passed finality_time.
#[receive(
    contract = "offchain-transfers",
    name = "execute-settlements",
    payable,
    mutable
)]
#[inline(always)]
fn contract_receive_execute_settlements<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {
    let current_time = ctx.metadata().slot_time();

    let state_mut = host.state_mut();

    for settlement in state_mut.settlements.iter() {
        // only execute settlements for which finality time has passed and if they are valid
        if current_time >= settlement.finality_time
            && is_settlement_valid(settlement, &state_mut.balance_sheet)
        {
            // first add balances of all receivers and then subtract of senders
            // together with the validity of settlements, this implies nonnegative amounts for all accounts
            for receive_transfer in settlement.transfer.receive_transfers.iter() {
                let mut receiver_balance = state_mut
                    .balance_sheet
                    .entry(receive_transfer.address)
                    .or_insert(Amount::zero());
                *receiver_balance += receive_transfer.amount;
            }

            for send_transfer in settlement.transfer.send_transfers.iter() {
                let mut sender_balance = state_mut
                    .balance_sheet
                    .entry(send_transfer.address)
                    .or_insert(Amount::zero());
                *sender_balance -= send_transfer.amount;
            }
        }
    }

    // remove all settlements for which finality time has passed from list
    state_mut
        .settlements
        .retain(|s| current_time < s.finality_time);

    Ok(())
}

// Tests //

#[concordium_cfg_test]
mod tests {
    use super::*;
    use concordium_std::test_infrastructure::*;

    fn get_test_state(config: ContractConfig, amount: Amount) -> TestHost<State<TestStateApi>> {
        let mut state_builder = TestStateBuilder::new();
        let state = State {
            config,
            next_id: 0u64,
            settlements: Vec::new(),
            balance_sheet: state_builder.new_map(),
        };
        let mut host = TestHost::new(state, state_builder);
        host.set_self_balance(amount);
        host
    }

    #[concordium_test]
    fn test_deposit() {
        //Accounts
        let account1 = AccountAddress([1u8; 32]); //Validator
        let account2 = AccountAddress([2u8; 32]); //Judge
        let account3 = AccountAddress([3u8; 32]); //Caller

        let deposit = Amount::from_ccd(100);

        //Initial State
        let mut host = get_test_state(
            ContractConfig {
                validator: account1,
                judge: account2,
                time_to_finality: Duration::from_seconds(600),
            },
            Amount::zero(),
        );

        //Test 1: Try to deposit money for new account holder
        let mut ctx = TestReceiveContext::empty();
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(100));
        ctx.set_sender(Address::Account(account3));

        let res: ContractResult<()> = contract_receive_deposit(&ctx, &mut host, deposit);

        claim!(res.is_ok(), "Should allow account holder to deposit CCDs");

        let balance = *host.state().balance_sheet.get(&account3).unwrap();
        claim_eq!(balance, deposit, "Balance should match deposit");

        //Test 2: Try to deposit money for existing account holder
        let res: ContractResult<()> = contract_receive_deposit(&ctx, &mut host, deposit);

        claim!(
            res.is_ok(),
            "Should allow existing account holder to deposit CCDs"
        );

        let balance = *host.state().balance_sheet.get(&account3).unwrap();
        claim_eq!(balance, 2 * deposit, "Balance should match 2*deposit");
    }

    #[concordium_test]
    fn test_withdrawal_simple() {
        //Accounts
        let account1 = AccountAddress([1u8; 32]); //Validator
        let account2 = AccountAddress([2u8; 32]); //Judge
        let account3 = AccountAddress([3u8; 32]); //Caller

        let balance = Amount::from_ccd(100);
        let toobig_payout = Amount::from_ccd(120);
        let payout = Amount::from_ccd(90);

        //Initial State
        let mut host = get_test_state(
            ContractConfig {
                validator: account1,
                judge: account2,
                time_to_finality: Duration::from_seconds(600),
            },
            balance,
        );
        //Set account3 balance
        host.state_mut().balance_sheet.insert(account3, balance);

        //Test 1: Try to withdraw too much money from Account 3
        let mut ctx = TestReceiveContext::empty();
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(100));
        ctx.set_sender(Address::Account(account3));
        let parameter_bytes = to_bytes(&toobig_payout);
        ctx.set_parameter(&parameter_bytes);

        let res: ContractResult<()> = contract_receive_withdraw(&ctx, &mut host);

        claim_eq!(
            res,
            ContractResult::Err(ReceiveError::InsufficientFunds),
            "Should fail with InsufficientFunds"
        );

        //Test 3: Try to withdraw 0 from Account 3
        let parameter_bytes = to_bytes(&Amount::zero());
        ctx.set_parameter(&parameter_bytes);
        let res: ContractResult<()> = contract_receive_withdraw(&ctx, &mut host);

        claim_eq!(
            res,
            ContractResult::Err(ReceiveError::ZeroWithdrawal),
            "Should fail with ZeroWithdrawal"
        );

        //Test 3: Try to withdraw money from Account 3
        let parameter_bytes = to_bytes(&payout);
        ctx.set_parameter(&parameter_bytes);
        let res: ContractResult<()> = contract_receive_withdraw(&ctx, &mut host);

        claim!(
            res.is_ok(),
            "Should allow account holder withdraw CCDs from balance."
        );

        let new_balance = *host.state().balance_sheet.get(&account3).unwrap();
        claim_eq!(
            new_balance,
            balance - payout,
            "New balance should match balance - payout"
        );

        let transfers = host.get_transfers();
        claim_eq!(transfers.len(), 1, "There should be one transfers");
        claim_eq!(transfers[0].0, account3, "Should be sent to account3");
        claim_eq!(transfers[0].1, payout, "payout CCDs should have been sents");

        //Test 4: Try to withdraw money from non-existing account (1)
        ctx.set_sender(Address::Account(account1));

        let res: ContractResult<()> = contract_receive_withdraw(&ctx, &mut host);

        claim_eq!(
            res,
            ContractResult::Err(ReceiveError::InsufficientFunds),
            "Should fail with InsufficientFunds"
        );
    }

    #[concordium_test]
    fn test_withdrawal_complex() {
        //Accounts
        let account1 = AccountAddress([1u8; 32]); //Validator
        let account2 = AccountAddress([2u8; 32]); //Judge
                                                  //User
        let alice = AccountAddress([3u8; 32]);
        let bob = AccountAddress([4u8; 32]);
        let charlie = AccountAddress([5u8; 32]);
        //Balances
        let alice_balance = Amount::from_ccd(100);
        let bob_balance = Amount::from_ccd(100);
        let charlie_balance = Amount::from_ccd(100);

        //Initial State
        let mut host = get_test_state(
            ContractConfig {
                validator: account1,
                judge: account2,
                time_to_finality: Duration::from_seconds(600),
            },
            //Total balance of all user
            alice_balance + bob_balance + charlie_balance,
        );
        //Set balance sheet
        host.state_mut().balance_sheet.insert(alice, alice_balance);
        host.state_mut().balance_sheet.insert(bob, bob_balance);
        host.state_mut()
            .balance_sheet
            .insert(charlie, charlie_balance);

        //Define settlements
        let settlement1 = Settlement {
            id: 1,
            transfer: Transfer {
                send_transfers: vec![AddressAmount {
                    address: alice,
                    amount: Amount::from_ccd(50),
                },AddressAmount {
                    address: bob,
                    amount: Amount::from_ccd(25),
                }],
                receive_transfers: vec![AddressAmount {
                    address: charlie,
                    amount: Amount::from_ccd(75),
                }],
                meta_data: Vec::new(),
            },
            finality_time: Timestamp::from_timestamp_millis(1000 * 600),
        };
        host.state_mut().settlements.push(settlement1);
        let settlement2 = Settlement {
            id: 1,
            transfer: Transfer {
                send_transfers: vec![AddressAmount {
                    address: charlie,
                    amount: Amount::from_ccd(20),
                },AddressAmount {
                    address: alice,
                    amount: Amount::from_ccd(10),
                }],
                receive_transfers: vec![AddressAmount {
                    address: bob,
                    amount: Amount::from_ccd(30),
                }],
                meta_data: Vec::new(),
            },
            finality_time: Timestamp::from_timestamp_millis(1000 * 600),
        };
        host.state_mut().settlements.push(settlement2);
        let settlement3 = Settlement {
            id: 1,
            transfer: Transfer {
                send_transfers: vec![AddressAmount {
                    address: bob,
                    amount: Amount::from_ccd(5),
                },AddressAmount {
                    address: charlie,
                    amount: Amount::from_ccd(10),
                }],
                receive_transfers: vec![AddressAmount {
                    address: alice,
                    amount: Amount::from_ccd(15),
                }],
                meta_data: Vec::new(),
            },
            finality_time: Timestamp::from_timestamp_millis(1000 * 600),
        };
        host.state_mut().settlements.push(settlement3);

        //Test 1: Alice should have 40 CCDs available -> Try to withdraw 41
        let mut ctx = TestReceiveContext::empty();
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(100));
        ctx.set_sender(Address::Account(alice));
        let parameter_bytes = to_bytes(&Amount::from_ccd(41));
        ctx.set_parameter(&parameter_bytes);

        let res: ContractResult<()> = contract_receive_withdraw(&ctx, &mut host);

        claim_eq!(
            res,
            ContractResult::Err(ReceiveError::InsufficientFunds),
            "Should fail with InsufficientFunds"
        );

        //Test 2: Bob should have 70 CCDs available -> Try to withdraw 70
        let payout = Amount::from_ccd(70);
        ctx.set_sender(Address::Account(bob));
        let parameter_bytes = to_bytes(&payout);
        ctx.set_parameter(&parameter_bytes);

        let res: ContractResult<()> = contract_receive_withdraw(&ctx, &mut host);  
        claim!(
            res.is_ok(),
            "Should allow account holder withdraw CCDs from balance."
        );

        let new_balance = *host.state().balance_sheet.get(&bob).unwrap();
        claim_eq!(
            new_balance,
            bob_balance - payout,
            "New balance should match balance - payout"
        );

        let transfers = host.get_transfers();
        claim_eq!(transfers.len(), 1, "There should be one transfers");
        claim_eq!(transfers[0].0, bob, "Should be sent to account3");
        claim_eq!(transfers[0].1, payout, "payout CCDs should have been sents");
        
        claim_eq!(host.state().settlements.len(),3, "This should not change the number of settlements.")
    }

    #[concordium_test]
    fn test_add_settlement() {
        //Accounts
        let account1 = AccountAddress([1u8; 32]); //Validator
        let account2 = AccountAddress([2u8; 32]); //Judge
        let account3 = AccountAddress([3u8; 32]); //Random caller

        //Adding settlement should work even with an empty balance sheet and no CCDs in the contract
        let balance = Amount::from_ccd(0);

        //Initial State
        let mut host = get_test_state(
            ContractConfig {
                validator: account1,
                judge: account2,
                time_to_finality: Duration::from_seconds(600),
            },
            balance,
        );
        
        //Test 1: Random caller tries to add valid settlement
        let good_transfer = Transfer {
            send_transfers: vec![AddressAmount{address: account3, amount:Amount::from_ccd(100)}],
            receive_transfers: vec![AddressAmount{address: account2, amount:Amount::from_ccd(50)}, AddressAmount{address: account1, amount:Amount::from_ccd(50)}],
            meta_data: Vec::new(),
        };
        let mut ctx = TestReceiveContext::empty();
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(100));
        ctx.set_sender(Address::Account(account3));
        let parameter_bytes = to_bytes(&good_transfer);
        ctx.set_parameter(&parameter_bytes);

        let res: ContractResult<()> = contract_receive_add_settlement(&ctx, &mut host);

        claim_eq!(
            res,
            ContractResult::Err(ReceiveError::NotAValidator),
            "Should fail with NotAValidator"
        );

        //Test 2: Validator tries to add valid settlement
        ctx.set_sender(Address::Account(account1));

        let res: ContractResult<()> = contract_receive_add_settlement(&ctx, &mut host);

        claim!(
            res.is_ok(),
            "Should allow validator to add settlement."
        );

        claim_eq!(host.state().settlements.len(),1,"There should be one settlement");
        claim_eq!(host.state().balance_sheet.iter().count(),0,"There should be no change to the balance sheet");

        //Test 3: Validator tries to add strange but valid settlement
        let strange_but_ok_transfer = Transfer {
            send_transfers: vec![AddressAmount{address: account3, amount:Amount::from_ccd(100)},AddressAmount{address: account3, amount:Amount::zero()}],
            receive_transfers: vec![AddressAmount{address: account3, amount:Amount::from_ccd(50)}, AddressAmount{address: account3, amount:Amount::from_ccd(50)}],
            meta_data: vec![1u8,2u8,3u8],
        };
        let parameter_bytes = to_bytes(&strange_but_ok_transfer);
        ctx.set_parameter(&parameter_bytes);

        let res: ContractResult<()> = contract_receive_add_settlement(&ctx, &mut host);     
          
        claim!(
            res.is_ok(),
            "Should allow validator to add settlement."
        );

        claim_eq!(host.state().settlements.len(),2,"There should be two settlements");
        claim_eq!(host.state().balance_sheet.iter().count(),0,"There should be no change to the balance sheet");

        //Test 4: Validator tries to add invalid settlement
        let bad_transfer = Transfer {
            send_transfers: vec![AddressAmount{address: account3, amount:Amount::from_ccd(50)}],
            receive_transfers: vec![AddressAmount{address: account1, amount:Amount::from_ccd(50)}, AddressAmount{address: account1, amount:Amount::from_ccd(50)}],
            meta_data: Vec::new(),
        };
        let parameter_bytes = to_bytes(&bad_transfer);
        ctx.set_parameter(&parameter_bytes);

        let res: ContractResult<()> = contract_receive_add_settlement(&ctx, &mut host); 

        claim_eq!(
            res,
            ContractResult::Err(ReceiveError::InvalidTransfer),
            "Should fail with InvalidTransfer"
        );
    }
}
