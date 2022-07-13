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
    transfer: Transfer,
    finality_time: Duration
}

#[derive(Clone,Serialize, SchemaType)]
struct BalanceInfo {
    real_balance: Amount,
    optimistic_balance: Amount
}
impl BalanceInfo {
    fn new(x: u64) -> BalanceInfo {
        BalanceInfo { real_balance: Amount::from_micro_ccd(x), optimistic_balance: Amount::from_micro_ccd(x) }
    }
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

#[init(contract = "offchain-transfers", parameter = "ContractConfig")]
#[inline(always)]
fn contract_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>
)-> InitResult<State<S>>{
    let config: ContractConfig = ctx.parameter_cursor().get()?;
    let state = State {
        config,
        settlements: state_builder.new_map(),
        balance_sheet: state_builder.new_map()
    };

    Ok(state)
}


#[receive(contract = "bilateral-transfers", name = "deposit", payable, mutable)]
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
    let mut balance_info = host.state_mut().balance_sheet.entry(sender_address).or_insert(BalanceInfo::new(0));
    balance_info.real_balance.checked_add(amount);
    balance_info.real_balance.checked_add(amount);
    //TODO: Reinsert
    Ok(())
}

#[receive(contract = "bilateral-transfers", name = "withdraw", payable, mutable)]
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

#[receive(contract = "bilateral-transfers", name = "settle", payable, mutable)]
#[inline(always)]
fn contract_receive_settle<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {
    Ok(())
}

#[receive(contract = "bilateral-transfers", name = "veto", payable, mutable)]
#[inline(always)]
fn contract_receive_veto<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
    _amount: Amount,
) -> ContractResult<()> {
    Ok(())
}

#[receive(contract = "bilateral-transfers", name = "execute-settlements", payable, mutable)]
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
