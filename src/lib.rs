#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::{collections::*, *};

type SettlementID = u64;

#[derive(Clone, Serialize, SchemaType)]
struct AddressAmount {
    address : AccountAddress,
    amount : Amount
}

// A transfer consisting of possibly multiple inputs with different amounts and several receivers
#[derive(Clone, Serialize, SchemaType)]
struct Transfer {
    send_transfers: Vec<AddressAmount>,
    receive_transfers: Vec<AddressAmount>
}

#[derive(Clone,Serialize, SchemaType)]
struct Settlement {
    id : SettlementID,
    transfer: Transfer,
    finality_time: Timestamp
}

#[derive(Serialize, SchemaType)]
struct ContractConfig {
    validator: AccountAddress,
    judge: AccountAddress,
    time_to_finality: Duration
}

#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
pub struct State<S> {
    // The initial configuration of the contract
    config: ContractConfig,

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
    // Sender cannot be a contract,
    ContractSender,
    // Not enough funds
    InsufficientFunds
}
type ContractResult<A> = Result<A, ReceiveError>;


// Initialize contract with empty balance sheet and no settlements
#[init(contract = "offchain-transfers", parameter = "ContractConfig")]
#[inline(always)]
fn contract_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>
)-> InitResult<State<S>>{
    let config: ContractConfig = ctx.parameter_cursor().get()?;
    let state = State {
        config,
        settlements: Vec::new(),
        balance_sheet: state_builder.new_map()
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
    let mut balance = host.state_mut().balance_sheet.entry(sender_address).or_insert(Amount::zero());
    *balance += amount;
    
    Ok(())
}

// Withdraw amount from smart contract.
// Only possible if the the user has sufficient funds in the worst case,
// i.e., even if all outstanding payments to that user get cancelled and all payments from that user are valid,
// there should be enough funds left to withdraw the requested payout.
#[receive(contract = "offchain-transfers", name = "withdraw", mutable, parameter = "Amount")]
#[inline(always)]
fn contract_receive_withdraw<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>
) -> ContractResult<()> {

    let sender_address = match ctx.sender() {
        Address::Contract(_) => bail!(ReceiveError::ContractSender),
        Address::Account(account_address) => account_address,
    };

    let payout: Amount = ctx.parameter_cursor().get()?;

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
        let mut balance = host.state_mut().balance_sheet.entry(sender_address).occupied_or(ReceiveError::InsufficientFunds)?;
        ensure!(*balance >= expenses + payout, ReceiveError::InsufficientFunds);

        // execute transfer
        *balance -= payout;
    }
    host.invoke_transfer(&sender_address, payout).unwrap_abort();

    Ok(())
}

// Checks whether a settlement is valid.
// This consists of checking that the sum of sent amount matches the sum of received amounts.
fn is_settlement_valid(settlement: Settlement) -> bool {
    let mut send_amount = Amount::zero();
    let mut receive_amount = Amount::zero();

    for send_transfer in settlement.transfer.send_transfers {
        send_amount += send_transfer.amount;
    }
    for receive_transfer in settlement.transfer.receive_transfers {
        receive_amount += receive_transfer.amount;
    }

    // settlement is valid if sent and received amounts match
    send_amount == receive_amount
}

// Add a settlement to the list of outstanding settlements.
// Checks validity of settlement and then adds it to the list of outstanding settlements.
#[receive(contract = "offchain-transfers", name = "settle", payable, mutable)]
#[inline(always)]
fn contract_receive_settle<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {
    Ok(())
}

// Veto a settlement. Removes this settlement from the list of outstanding settlements.
// Only the judge is allowed to call this function. Furthermore, it must be called before the finality_time of the settlement.
#[receive(contract = "offchain-transfers", name = "veto", payable, mutable)]
#[inline(always)]
fn contract_receive_veto<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {
    Ok(())
}

// Execute all settlements with passed finality_time.
#[receive(contract = "offchain-transfers", name = "execute-settlements", payable, mutable)]
#[inline(always)]
fn contract_receive_execute_settlements<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {
    Ok(())
}





#[concordium_cfg_test]
mod tests {
    use super::*;
    use concordium_std::test_infrastructure::*;

    fn get_test_state(
        config: ContractConfig,
        amount: Amount,
    ) -> TestHost<State<TestStateApi>> {
        let mut state_builder = TestStateBuilder::new();
        let state = State {
            config,
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
            ContractConfig{
                validator: account1,
                judge: account2,
                time_to_finality: Duration::from_seconds(600)      
            },
            Amount::zero()
        );

        //Test 1: Try to deposit money for new account holder
        let mut ctx = TestReceiveContext::empty();
        ctx.metadata_mut()
            .set_slot_time(Timestamp::from_timestamp_millis(100));
        ctx.set_sender(Address::Account(account3));

        let res: ContractResult<()> = contract_receive_deposit(&ctx, &mut host, deposit);

        claim!(res.is_ok(), "Should allow account holder to deposit CCDs");

        let balance = *host.state().balance_sheet.get(&account3).unwrap();
        claim_eq!(
            balance,
            deposit,
            "Balance should match deposit"
        );

        //Test 2: Try to deposit money for existing account holder
        let res: ContractResult<()> = contract_receive_deposit(&ctx, &mut host, deposit);

        claim!(res.is_ok(), "Should allow existing account holder to deposit CCDs");

        let balance = *host.state().balance_sheet.get(&account3).unwrap();
        claim_eq!(
            balance,
            2*deposit,
            "Balance should match 2*deposit"
        );

    }

    #[concordium_test]
    fn test_withdrawl() {
        //Accounts
        let account1 = AccountAddress([1u8; 32]); //Validator
        let account2 = AccountAddress([2u8; 32]); //Judge
        let account3 = AccountAddress([3u8; 32]); //Caller

        let balance = Amount::from_ccd(100);
        let toobig_payout = Amount::from_ccd(120);
        let payout = Amount::from_ccd(90);

        //Initial State
        let mut host = get_test_state(
            ContractConfig{
                validator: account1,
                judge: account2,
                time_to_finality: Duration::from_seconds(600)      
            },
            balance
        );
        //Set account3 balance
        host.state_mut().balance_sheet.insert(account3,balance);

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

        //Test 2: Try to withdraw money from Account 3
        let parameter_bytes = to_bytes(&payout);
        ctx.set_parameter(&parameter_bytes);
        let res: ContractResult<()> = contract_receive_withdraw(&ctx, &mut host);
    
        claim!(res.is_ok(), "Should allow account holder withdraw CCDs from balance.");

        let new_balance = *host.state().balance_sheet.get(&account3).unwrap();
        claim_eq!(
            new_balance,
            balance - payout,
            "New balance should match balance - payout"
        );

        let transfers = host.get_transfers();
        claim_eq!(transfers.len(), 1, "There should be one transfers");
        claim_eq!(
            transfers[0].0,
            account3,
            "Should be sent to account3"
        );
        claim_eq!(transfers[0].1, payout, "payout CCDs should have been sents");


    }
}
