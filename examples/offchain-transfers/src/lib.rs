#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::{collections::*, *};

type SettlementID = u64;

#[derive(Clone, Serialize, SchemaType)]
struct Transfer {
    senders: Vec<(AccountAddress,Amount)>,
    receivers: Vec<(AccountAddress,Amount)>,
}

struct Settlement {
    transfer: Transfer,
    finality_time: Duration
}

struct BalanceInfo {
    real_balance: Amount,
    optimistic_balance: Amount
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
    settlements: StateMap<SettlementID, Settlement, S>,

    // Balance sheet
    balance_sheet: StateMap<AccountAddress, BalanceInfo, S>,
    
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
    ContractSender
}
type ContractResult<A> = Result<A, ReceiveError>;

#[init(contract = "offchain-transfers", parameter = "ContractConfig", payable)]
#[inline(always)]
fn contract_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
    _amount: Amount,
)-> InitResult<State<S>>{
    let config: ContractConfig = ctx.parameter_cursor().get()?;
    let state = State {
        config,
        settlements: state_builder.new_map(),
        balance_sheet: state_builder.new_map()
    };

    Ok(state)
}

#[receive(contract = "bilateral-transfers", name = "deposit", payable)]
#[inline(always)]
fn contract_receive_deposit<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {

    let sender_address = match ctx.sender() {
        Address::Contract(_) => bail!(ReceiveError::ContractSender),
        Address::Account(account_address) => account_address,
    };


    Ok(())
}

#[receive(contract = "bilateral-transfers", name = "withdraw", payable)]
#[inline(always)]
fn contract_receive_withdraw<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
    amount: Amount,
) -> ContractResult<()> {

    let sender_address = match ctx.sender() {
        Address::Contract(_) => bail!(ReceiveError::ContractSender),
        Address::Account(account_address) => account_address,
    };
    Ok(())
}

#[receive(contract = "bilateral-transfers", name = "settle", payable)]
#[inline(always)]
fn contract_receive_settle<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {
    Ok(())
}

#[receive(contract = "bilateral-transfers", name = "veto", payable)]
#[inline(always)]
fn contract_receive_veto<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {
    Ok(())
}

#[receive(contract = "bilateral-transfers", name = "execute-settlements", payable)]
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
