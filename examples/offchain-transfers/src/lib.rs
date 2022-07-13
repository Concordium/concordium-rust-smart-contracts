#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::{collections::*, *};

type SettlementID = u64;

#[derive(Clone, Serialize, SchemaType)]
struct Transfer {
    senders: Vec<(AccountAddress,Amount)>,
    receivers: Vec<(AccountAddress,Amount)>,
}

#[derive(Clone,Serialize, SchemaType)]
struct Settlement {
    id : SettlementID,
    transfer: Transfer,
    finality_time: Duration
}

#[derive(Serialize, SchemaType)]
struct ContractConfig {
    validator: AccountAddress,
    judge: AccountAddress,
    time_to_finality: Timestamp
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
    let mut balance = *host.state_mut().balance_sheet.entry(sender_address).or_insert(Amount::zero());
    balance += amount;

    Ok(())
}

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
        for sender in settlement.transfer.senders.iter() {
            if let (sender_address, value) = sender {
                expenses += *value;
            }
        }
    }

    // ensure that user has sufficient funds even in the worst case if all expenses are deducted and nothing is added
    let mut balance = *host.state_mut().balance_sheet.entry(sender_address).occupied_or(ReceiveError::InsufficientFunds)?;
    ensure!(balance >= expenses + payout, ReceiveError::InsufficientFunds);

    // execute transfer
    balance -= payout;
    host.invoke_transfer(&sender_address, payout).unwrap_abort();

    Ok(())
}

#[receive(contract = "offchain-transfers", name = "settle", payable, mutable)]
#[inline(always)]
fn contract_receive_settle<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {
    Ok(())
}

#[receive(contract = "offchain-transfers", name = "veto", payable, mutable)]
#[inline(always)]
fn contract_receive_veto<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {
    Ok(())
}

#[receive(contract = "offchain-transfers", name = "execute-settlements", payable, mutable)]
#[inline(always)]
fn contract_receive_execute_settlements<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {
    Ok(())
}




#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
