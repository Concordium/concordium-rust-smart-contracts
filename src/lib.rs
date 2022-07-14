#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;
use std::collections::HashSet;
use std::convert::TryInto;

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
    /// The validator's address
    /// In an application, this should be replaced by a committee of validators (with approval threshold)
    /// See the two-stage transfer example on how to implement such a validator committee
    validator: AccountAddress,

    /// The judge's address 
    judge: AccountAddress,

    /// Time until a settlement becomes final
    time_to_finality: Duration,
    
    /// Bound on the amount of pending settlements 
    settlement_limit: u32,
}

#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
pub struct State<S> {
    /// The initial configuration of the contract
    config: ContractConfig,

    /// The next settlement id
    next_id: SettlementID,

    /// Proposed settlements
    settlements: Vec<Settlement>,

    /// Balance sheet
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
    /// Settlement queue full,
    SettlementQueueFull
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

/// Checks whether a transfer is syntactically valid.
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

    //Ensure there is space for the incoming settlement
    ensure!(
        host.state().settlements.len() < host.state().config.settlement_limit.try_into().unwrap(),
        ReceiveError::SettlementQueueFull
    );

    let transfer: Transfer = ctx.parameter_cursor().get()?;

    //Syntactically verify transfer information
    ensure!(
        is_settlement_transfer(&transfer),
        ReceiveError::InvalidTransfer
    );
    let id = host.state().next_id;
    //Create a new settlement
    let now = ctx.metadata().slot_time();
    let settlement = Settlement {
        id,
        transfer,
        finality_time: now
            .checked_add(host.state().config.time_to_finality)
            .ok_or(ReceiveError::TimeOverflow)?,
    };
    //Increase ID counter
    host.state_mut().next_id = id.checked_add(1).ok_or(ReceiveError::CounterOverflow)?;
    //Add settlement
    host.state_mut().settlements.push(settlement);
    Ok(())
}

/// Veto a settlement. Removes this settlement from the list of outstanding settlements.
/// Only the judge is allowed to call this function. Furthermore, it must be called before the finality_time of the settlement.
#[receive(contract = "offchain-transfers", name = "veto", mutable)]
#[inline(always)]
fn contract_receive_veto<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    let sender = ctx.sender();
    //Only the validator may call this function
    ensure!(
        sender.matches_account(&host.state().config.judge),
        ReceiveError::NotAJudge
    );
    let s_id: SettlementID = ctx.parameter_cursor().get()?;
    let now = ctx.metadata().slot_time();

    // delete all settlements with the given ID from the list that are not final
    host.state_mut()
        .settlements
        .retain(|s| s.id != s_id || s.finality_time <= now);

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
#[receive(contract = "offchain-transfers", name = "execute-settlements", mutable)]
#[inline(always)]
fn contract_receive_execute_settlements<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
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
    fn test_init() {
        //Accounts
        let account1 = AccountAddress([1u8; 32]); //Validator
        let account2 = AccountAddress([2u8; 32]); //Judge
        let time_to_finality = Duration::from_seconds(666);

        let parameter = ContractConfig {
            validator: account1,
            judge: account2,
            time_to_finality,
            settlement_limit: 1000,
        };
        let parameter_bytes = to_bytes(&parameter);

        let mut ctx = TestInitContext::empty();
        ctx.set_parameter(&parameter_bytes);

        let mut state_builder = TestStateBuilder::new();

        let result = contract_init(&ctx, &mut state_builder);

        let state = match result {
            Ok(s) => s,
            Err(_) => fail!("Contract initialization failed."),
        };

        claim_eq!(
            state.config.validator,
            account1,
            "Account 1 should be validator"
        );
        claim_eq!(state.config.judge, account2, "Account 1 should be judge");
        claim_eq!(
            state.config.time_to_finality,
            time_to_finality,
            "time to finality should be time_to_finality"
        );
        claim_eq!(
            state.balance_sheet.iter().count(),
            0,
            "No balances should exist"
        );
        claim_eq!(state.settlements.len(), 0, "No settlements should exist");
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
                settlement_limit: 1000,
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
                settlement_limit: 1000,
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
                settlement_limit: 1000,
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
                send_transfers: vec![
                    AddressAmount {
                        address: alice,
                        amount: Amount::from_ccd(50),
                    },
                    AddressAmount {
                        address: bob,
                        amount: Amount::from_ccd(25),
                    },
                ],
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
            id: 2,
            transfer: Transfer {
                send_transfers: vec![
                    AddressAmount {
                        address: charlie,
                        amount: Amount::from_ccd(20),
                    },
                    AddressAmount {
                        address: alice,
                        amount: Amount::from_ccd(10),
                    },
                ],
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
            id: 3,
            transfer: Transfer {
                send_transfers: vec![
                    AddressAmount {
                        address: bob,
                        amount: Amount::from_ccd(5),
                    },
                    AddressAmount {
                        address: charlie,
                        amount: Amount::from_ccd(10),
                    },
                ],
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

        claim_eq!(
            host.state().settlements.len(),
            3,
            "This should not change the number of settlements."
        )
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
                settlement_limit: 2,
            },
            balance,
        );

        //Test 1: Random caller tries to add valid settlement
        let good_transfer = Transfer {
            send_transfers: vec![AddressAmount {
                address: account3,
                amount: Amount::from_ccd(100),
            }],
            receive_transfers: vec![
                AddressAmount {
                    address: account2,
                    amount: Amount::from_ccd(50),
                },
                AddressAmount {
                    address: account1,
                    amount: Amount::from_ccd(50),
                },
            ],
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

        claim!(res.is_ok(), "Should allow validator to add settlement.");

        claim_eq!(
            host.state().settlements.len(),
            1,
            "There should be one settlement"
        );
        claim_eq!(
            host.state().balance_sheet.iter().count(),
            0,
            "There should be no change to the balance sheet"
        );
        claim_eq!(host.state().next_id, 1, "The ID should be increased");

        //Test 3: Validator tries to add invalid settlement
        let bad_transfer = Transfer {
            send_transfers: vec![AddressAmount {
                address: account3,
                amount: Amount::from_ccd(50),
            }],
            receive_transfers: vec![
                AddressAmount {
                    address: account1,
                    amount: Amount::from_ccd(50),
                },
                AddressAmount {
                    address: account1,
                    amount: Amount::from_ccd(50),
                },
            ],
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

        //Test 4: Validator tries to add strange but valid settlement
        let strange_but_ok_transfer = Transfer {
            send_transfers: vec![
                AddressAmount {
                    address: account3,
                    amount: Amount::from_ccd(100),
                },
                AddressAmount {
                    address: account3,
                    amount: Amount::zero(),
                },
            ],
            receive_transfers: vec![
                AddressAmount {
                    address: account3,
                    amount: Amount::from_ccd(50),
                },
                AddressAmount {
                    address: account3,
                    amount: Amount::from_ccd(50),
                },
            ],
            meta_data: vec![1u8, 2u8, 3u8],
        };
        let parameter_bytes = to_bytes(&strange_but_ok_transfer);
        ctx.set_parameter(&parameter_bytes);

        let res: ContractResult<()> = contract_receive_add_settlement(&ctx, &mut host);

        claim!(res.is_ok(), "Should allow validator to add settlement.");

        claim_eq!(
            host.state().settlements.len(),
            2,
            "There should be two settlements"
        );
        claim_eq!(
            host.state().balance_sheet.iter().count(),
            0,
            "There should be no change to the balance sheet"
        );
        claim_eq!(host.state().next_id, 2, "The ID should be increased");

        //Test 5: Validator tries to add to a full quueue
        let parameter_bytes = to_bytes(&good_transfer);
        ctx.set_parameter(&parameter_bytes);

        let res: ContractResult<()> = contract_receive_add_settlement(&ctx, &mut host);

        claim_eq!(
            res,
            ContractResult::Err(ReceiveError::SettlementQueueFull),
            "Should fail with SettlementQueueFull"
        );
    }

    #[concordium_test]
    fn test_execute_settlements() {
        //Accounts
        let account1 = AccountAddress([1u8; 32]); //Validator
        let account2 = AccountAddress([2u8; 32]); //Judge

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
                settlement_limit: 1000,
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

        // First settlement is fine and with past finality
        let settlement1 = Settlement {
            id: 1,
            transfer: Transfer {
                send_transfers: vec![
                    AddressAmount {
                        address: alice,
                        amount: Amount::from_ccd(50),
                    },
                    AddressAmount {
                        address: bob,
                        amount: Amount::from_ccd(25),
                    },
                ],
                receive_transfers: vec![AddressAmount {
                    address: charlie,
                    amount: Amount::from_ccd(75),
                }],
                meta_data: Vec::new(),
            },
            finality_time: Timestamp::from_timestamp_millis(1000 * 600),
        };
        host.state_mut().settlements.push(settlement1);

        // Second settlement tries to withdraw more from Alice than available after first settlement and should be skipped
        let settlement2 = Settlement {
            id: 1,
            transfer: Transfer {
                send_transfers: vec![
                    AddressAmount {
                        address: alice,
                        amount: Amount::from_ccd(60),
                    },
                    AddressAmount {
                        address: bob,
                        amount: Amount::from_ccd(5),
                    },
                ],
                receive_transfers: vec![AddressAmount {
                    address: charlie,
                    amount: Amount::from_ccd(65),
                }],
                meta_data: Vec::new(),
            },
            finality_time: Timestamp::from_timestamp_millis(1000 * 600),
        };
        host.state_mut().settlements.push(settlement2);

        // Thid settlement is fine but with future finality and should thus also be skipped
        let settlement3 = Settlement {
            id: 1,
            transfer: Transfer {
                send_transfers: vec![
                    AddressAmount {
                        address: alice,
                        amount: Amount::from_ccd(1),
                    },
                    AddressAmount {
                        address: bob,
                        amount: Amount::from_ccd(1),
                    },
                ],
                receive_transfers: vec![AddressAmount {
                    address: charlie,
                    amount: Amount::from_ccd(1),
                }],
                meta_data: Vec::new(),
            },
            finality_time: Timestamp::from_timestamp_millis(1000 * 800),
        };
        host.state_mut().settlements.push(settlement3);

        // Fourth settlement is fine and with past finality and should thus be executed
        let settlement4 = Settlement {
            id: 1,
            transfer: Transfer {
                send_transfers: vec![
                    AddressAmount {
                        address: alice,
                        amount: Amount::from_ccd(50),
                    },
                    AddressAmount {
                        address: bob,
                        amount: Amount::from_ccd(5),
                    },
                ],
                receive_transfers: vec![AddressAmount {
                    address: charlie,
                    amount: Amount::from_ccd(55),
                }],
                meta_data: Vec::new(),
            },
            finality_time: Timestamp::from_timestamp_millis(1000 * 600),
        };
        host.state_mut().settlements.push(settlement4);

        // Test execution
        let mut ctx = TestReceiveContext::empty();
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(1000 * 700));
        ctx.set_sender(Address::Account(account1));

        let res: ContractResult<()> = contract_receive_execute_settlements(&ctx, &mut host);

        claim_eq!(res, Ok(()), "Execution should succeed.");

        claim_eq!(
            *host.state().balance_sheet.get(&alice).unwrap(),
            Amount::from_ccd(0),
            "Alice has incorrect amount."
        );

        claim_eq!(
            *host.state().balance_sheet.get(&bob).unwrap(),
            Amount::from_ccd(70),
            "Bob has incorrect amount."
        );

        claim_eq!(
            *host.state().balance_sheet.get(&charlie).unwrap(),
            Amount::from_ccd(230),
            "Charlie has incorrect amount."
        );
    }

    #[concordium_test]
    fn test_veto() {
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
                time_to_finality: Duration::from_millis(100),
                settlement_limit: 1000,
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
                send_transfers: vec![
                    AddressAmount {
                        address: alice,
                        amount: Amount::from_ccd(50),
                    },
                    AddressAmount {
                        address: bob,
                        amount: Amount::from_ccd(25),
                    },
                ],
                receive_transfers: vec![AddressAmount {
                    address: charlie,
                    amount: Amount::from_ccd(75),
                }],
                meta_data: Vec::new(),
            },
            finality_time: Timestamp::from_timestamp_millis(100),
        };
        host.state_mut().settlements.push(settlement1);
        let settlement2 = Settlement {
            id: 2,
            transfer: Transfer {
                send_transfers: vec![
                    AddressAmount {
                        address: charlie,
                        amount: Amount::from_ccd(20),
                    },
                    AddressAmount {
                        address: alice,
                        amount: Amount::from_ccd(10),
                    },
                ],
                receive_transfers: vec![AddressAmount {
                    address: bob,
                    amount: Amount::from_ccd(30),
                }],
                meta_data: Vec::new(),
            },
            finality_time: Timestamp::from_timestamp_millis(110),
        };
        host.state_mut().settlements.push(settlement2);

        //Test 1 NonJudge trying to veto settlement
        let mut ctx = TestReceiveContext::empty();
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(90));
        ctx.set_sender(Address::Account(account1)); //Use a validator instead
        let id_bytes = to_bytes(&1u64);
        ctx.set_parameter(&id_bytes);

        let res: ContractResult<()> = contract_receive_veto(&ctx, &mut host);

        claim_eq!(
            res,
            ContractResult::Err(ReceiveError::NotAJudge),
            "Should fail with NotAJudge"
        );

        //Test 2 judge trying to veto non-existing settlement (THIS IS FINE)
        ctx.set_sender(Address::Account(account2)); //Use a validator instead
        let id_bytes = to_bytes(&42u64);
        ctx.set_parameter(&id_bytes);

        let res: ContractResult<()> = contract_receive_veto(&ctx, &mut host);
        claim!(
            res.is_ok(),
            "Should allow judge to veto non-existing settlement."
        );

        claim_eq!(
            host.state().settlements.len(),
            2,
            "There should still be two settlements."
        );

        //Test 3 judge vetoes existing settlement
        ctx.set_sender(Address::Account(account2));
        let id_bytes = to_bytes(&1u64);
        ctx.set_parameter(&id_bytes);

        let res: ContractResult<()> = contract_receive_veto(&ctx, &mut host);
        claim!(
            res.is_ok(),
            "Should allow judge to veto existing settlement."
        );

        claim_eq!(
            host.state().settlements.len(),
            1,
            "There should one settlement."
        );

        //Test 4 judge tries to veto existing settlement after finality
        ctx.set_sender(Address::Account(account2));
        let id_bytes = to_bytes(&2u64);
        ctx.set_parameter(&id_bytes);
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(120));

        let res: ContractResult<()> = contract_receive_veto(&ctx, &mut host);

        claim!(res.is_ok(), "Should succeed (but without effect)");
        claim_eq!(
            host.state().settlements.len(),
            1,
            "There should still be one settlement."
        );
    }

    // test using all functions
    #[concordium_test]
    fn test_lifecycle() {
        let validator_address = AccountAddress([1u8; 32]);
        let judge_address = AccountAddress([2u8; 32]);
        let alice_address = AccountAddress([3u8; 32]);
        let bob_address = AccountAddress([4u8; 32]);
        let charlie_address = AccountAddress([5u8; 32]);

        // first initialize contract
        let mut ctx = TestInitContext::empty();
        let mut state_builder = TestStateBuilder::new();

        let parameter = ContractConfig {
            validator: validator_address,
            judge: judge_address,
            time_to_finality: Duration::from_millis(100),
            settlement_limit: 1000,
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let init_result = contract_init(&ctx, &mut state_builder);
        let state = match init_result {
            Ok(s) => s,
            Err(_) => fail!("Contract initialization failed."),
        };

        let mut host = TestHost::new(state, state_builder);

        // next let participants deposit some CCD
        let deposit = Amount::from_ccd(100);
        host.set_self_balance(deposit); //The host balance is not updated automatically
        let mut ctx = TestReceiveContext::empty();
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(100));
        ctx.set_sender(Address::Account(alice_address));
        let res: ContractResult<()> = contract_receive_deposit(&ctx, &mut host, deposit);
        claim!(res.is_ok(), "Should allow Alice to deposit CCDs");

        host.set_self_balance(host.self_balance() + deposit);
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(120));
        ctx.set_sender(Address::Account(bob_address));
        let res: ContractResult<()> =
            contract_receive_deposit(&ctx, &mut host, Amount::from_ccd(100));
        claim!(res.is_ok(), "Should allow Bob holder to deposit CCDs");

        host.set_self_balance(host.self_balance() + deposit);
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(130));
        ctx.set_sender(Address::Account(charlie_address));
        let res: ContractResult<()> =
            contract_receive_deposit(&ctx, &mut host, Amount::from_ccd(100));
        claim!(res.is_ok(), "Should allow Charlie holder to deposit CCDs");

        claim_eq!(
            host.self_balance(),
            3 * deposit,
            "Test should be written consistently."
        );

        // try to withdraw too much from Bob
        let parameter_bytes = to_bytes(&Amount::from_ccd(120));
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(180));
        ctx.set_sender(Address::Account(bob_address));
        ctx.set_parameter(&parameter_bytes);
        let res: ContractResult<()> = contract_receive_withdraw(&ctx, &mut host);
        claim_eq!(
            res,
            ContractResult::Err(ReceiveError::InsufficientFunds),
            "Should fail with InsufficientFunds"
        );

        // withdraw valid amount from Bob
        let payout = Amount::from_ccd(40);
        let parameter_bytes = to_bytes(&payout);
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(190));
        ctx.set_sender(Address::Account(bob_address));
        ctx.set_parameter(&parameter_bytes);
        let res: ContractResult<()> = contract_receive_withdraw(&ctx, &mut host);

        claim!(res.is_ok(), "Should allow Bob to withdraw amount.");

        //Add settlements
        let transfer1 = Transfer {
            send_transfers: vec![
                AddressAmount {
                    address: alice_address,
                    amount: Amount::from_ccd(50),
                },
                AddressAmount {
                    address: charlie_address,
                    amount: Amount::from_ccd(20),
                },
            ],
            receive_transfers: vec![AddressAmount {
                address: charlie_address,
                amount: Amount::from_ccd(70),
            }],
            meta_data: Vec::new(),
        };
        let parameter_bytes = to_bytes(&transfer1);
        ctx.set_parameter(&parameter_bytes);
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(200));
        ctx.set_sender(Address::Account(validator_address));
        let res: ContractResult<()> = contract_receive_add_settlement(&ctx, &mut host);
        claim!(res.is_ok(), "Should allow the validator to add settlement.");

        // withdraw too much from Alice (reserved balance)
        let parameter_bytes = to_bytes(&Amount::from_ccd(60));
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(210));
        ctx.set_sender(Address::Account(alice_address));
        ctx.set_parameter(&parameter_bytes);
        let res: ContractResult<()> = contract_receive_withdraw(&ctx, &mut host);
        claim_eq!(
            res,
            ContractResult::Err(ReceiveError::InsufficientFunds),
            "Should fail with InsufficientFunds"
        );

        //Add another settlement
        let transfer2 = Transfer {
            send_transfers: vec![AddressAmount {
                address: charlie_address,
                amount: Amount::from_ccd(90),
            }],
            receive_transfers: vec![
                AddressAmount {
                    address: alice_address,
                    amount: Amount::from_ccd(50),
                },
                AddressAmount {
                    address: bob_address,
                    amount: Amount::from_ccd(40),
                },
            ],
            meta_data: Vec::new(),
        };
        let parameter_bytes = to_bytes(&transfer2);
        ctx.set_parameter(&parameter_bytes);
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(220));
        ctx.set_sender(Address::Account(validator_address));
        let res: ContractResult<()> = contract_receive_add_settlement(&ctx, &mut host);
        claim!(res.is_ok(), "Should allow the validator to add settlement.");

        // Veto one
        ctx.set_sender(Address::Account(judge_address));
        let id_bytes = to_bytes(&0u64);
        ctx.set_parameter(&id_bytes);
        let res: ContractResult<()> = contract_receive_veto(&ctx, &mut host);
        claim!(
            res.is_ok(),
            "Should allow judge to veto existing settlement."
        );
        claim_eq!(
            host.state().settlements.len(),
            1,
            "There should one settlement."
        );

        // Withdraw now 
        let parameter_bytes = to_bytes(&Amount::from_ccd(60));
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(230));
        ctx.set_sender(Address::Account(alice_address));
        ctx.set_parameter(&parameter_bytes);
        let res: ContractResult<()> = contract_receive_withdraw(&ctx, &mut host);
        claim!(
            res.is_ok(),
            "Should allow Alice to withdraw funds."
        );

        // Execute settlement too early
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(310));
        ctx.set_sender(Address::Account(bob_address));
        let res: ContractResult<()> = contract_receive_execute_settlements(&ctx, &mut host);
        claim!(
            res.is_ok(),
            "Should allow Bob to execute all final settlement."
        );
        claim_eq!(
            host.state().settlements.len(),
            1,
            "There should one settlement."
        );

        // Execute settlement
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(320));
        ctx.set_sender(Address::Account(bob_address));
        let res: ContractResult<()> = contract_receive_execute_settlements(&ctx, &mut host);
        claim!(
            res.is_ok(),
            "Should allow Bob to execute settlement."
        );
        claim_eq!(
            host.state().settlements.len(),
            0,
            "There should one settlement."
        );

        // Withdraw final
        let parameter_bytes = to_bytes(&Amount::from_ccd(90));
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(330));
        ctx.set_sender(Address::Account(alice_address));
        ctx.set_parameter(&parameter_bytes);
        let res: ContractResult<()> = contract_receive_withdraw(&ctx, &mut host);
        claim!(
            res.is_ok(),
            "Should allow Alice to withdraw funds."
        );
        let balance = *host.state().balance_sheet.get(&alice_address).unwrap();
        claim_eq!(balance,Amount::zero(),"Alice should have no money left.");

        let parameter_bytes = to_bytes(&Amount::from_ccd(100));
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(340));
        ctx.set_sender(Address::Account(bob_address));
        ctx.set_parameter(&parameter_bytes);
        let res: ContractResult<()> = contract_receive_withdraw(&ctx, &mut host);
        claim!(
            res.is_ok(),
            "Should allow Bob to withdraw funds."
        );
        let balance = *host.state().balance_sheet.get(&bob_address).unwrap();
        claim_eq!(balance,Amount::zero(),"Bob should have no money left.");

        let parameter_bytes = to_bytes(&Amount::from_ccd(10));
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(330));
        ctx.set_sender(Address::Account(charlie_address));
        ctx.set_parameter(&parameter_bytes);
        let res: ContractResult<()> = contract_receive_withdraw(&ctx, &mut host);
        claim!(
            res.is_ok(),
            "Should allow Charlie to withdraw funds."
        );
        let balance = *host.state().balance_sheet.get(&charlie_address).unwrap();
        claim_eq!(balance,Amount::zero(),"Charlie should have no money left.");
        
        //There should be no money left in the contract
        claim_eq!(
            host.self_balance(),
            Amount::zero(),
            "Contract should contain no money."
        );

    }
}
