/*!
 * An example implementation of an optimistic settlement layer for off-chain
 * transactions.
 *
 *  **Warning**
 *  This contract is is **UNSUITABLE FOR DEPLOYMENT**, and **PROVIDED AS
 * Proof-Of-Concept ONLY**.
 *
 * # Description
 * This contract implements a simple settlement mechanism for off-chain
 * payments. It is an example of so-called "rollups" since it allows to roll
 * multiple off-chain transactions up into a single on-chain settlement
 * transaction (and thereby save transaction fees). The intended use of the
 * contract is as follows:
 *  * The smart contract is initialized with [contract_init] by appointing a
 *    "judge" and a "validator", and setting a "time to finality" duration.
 *  * Users deposit a collateral to the smart contract using the
 *    [contract_receive_deposit] function. This adds the deposited amount to
 *    the available balance in the balance sheet of the smart contract.
 *  * Afterwards, users can transact off-chain using their deposited
 *    collateral as balance.
 *  * Once users are done with their off-chain transactions, the validator
 *    can settle the transactions by adding a settlement to the chain using
 *    [contract_receive_add_settlement]. A settlement is described by a
 *    [Transfer], two `Vec`s of  addresses and amounts specifying which
 *    addresses have to pay which amounts and which addresses receive which
 *    amounts, respectively. Settlements can only be added by the validator
 *    to prevent DoS attacks.
 *  * After a settlement, users can already (optimistically) use the updated
 *    balances from that settlement off-chain and in future settlements.
 *    Withdrawing received amounts, however, is only possible after the
 *    settlement was finalized.
 *  * If users object to a published settlement, they can off-chain complain
 *    to the judge. If the judge deems a settlement invalid before it has
 *    been finalized, the judge can veto it using [contract_receive_veto].
 *  * Settlements that have not been vetoed for the "time to finality"
 *    duration become finalized and cannot be reverted anymore.
 *  * The function [contract_receive_execute_settlements] executes all
 *    finalized settlements and updates the balance sheet accordingly.
 *    Everyone can call this function periodically.
 *  * Users can withdraw funds from the smart contract using
 *    [contract_receive_withdraw]. The maximal allowed amount to withdraw
 *    corresponds to the worst-case amount that is guaranteed to be
 *    available no matter which outstanding settlements are vetoed.
 *
 * # Limitations
 *  * The `settlement_limit` in [ContractConfig] needs to be set such that
 *    both `contract_receive_veto` and
 *    `contract_receive_execute_settlements` can run on a full settlement
 *    queue given the energy limit of a single block.
 *  * The data structures have not been optimized for deployment. In
 *    particular, the use of `Vec` in the smart contract state can degrade
 *    performance.
 *
 */

#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;
use std::{collections::HashSet, convert::TryInto};

/// Unique identifier for settlements
pub type SettlementID = u64;

/// A tuple describing either a sender or receiver with an amount in a transfer
#[derive(Clone, Serialize, SchemaType, PartialEq, Eq)]
pub struct AddressAmount {
    /// The sender or receiver
    address: AccountAddress,
    /// The sent/received amount
    amount:  Amount,
}

/// A transfer consisting of possibly multiple inputs with different amounts and
/// several receivers A transfer is syntactically valid if the sent amounts
/// match the received amounts
#[derive(Clone, Serialize, SchemaType, PartialEq, Eq)]
pub struct Transfer {
    /// The list of senders
    pub send_transfers:    Vec<AddressAmount>,
    /// The list of receivers
    pub receive_transfers: Vec<AddressAmount>,
    /// The meta-data is not used by the smart contract
    /// it could contain information relevant to the judge
    pub meta_data:         Vec<u8>,
}

/// A settlement defines a (potential) update to the balance sheet
#[derive(Clone, Serialize, SchemaType, PartialEq, Eq)]
pub struct Settlement {
    /// Unique ID
    id:            SettlementID,
    /// The update described as a transfer
    transfer:      Transfer,
    /// Point in time when the settlement becomes final
    finality_time: Timestamp,
}

/// The configuration of the smart contract
#[derive(Clone, Serialize, SchemaType)]
pub struct ContractConfig {
    /// The validator's address
    /// In an application, this should be replaced by a committee of validators
    /// (with approval threshold) See the two-stage transfer example on how
    /// to implement such a validator committee
    pub validator: AccountAddress,

    /// The judge's address
    pub judge: AccountAddress,

    /// Time until a settlement becomes final
    pub time_to_finality: Duration,

    /// Bound on the amount of pending settlements
    pub settlement_limit: u32,
}

/// The smart contract state
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
pub struct State<S> {
    /// The configuration of the contract
    config: ContractConfig,

    /// The next settlement id, starts at 0
    next_id: SettlementID,

    /// Proposed settlements
    ///
    /// Note that the settlement queue could be implemented with a more
    /// efficient data structure
    settlements: Vec<Settlement>,

    /// Balance sheet
    balance_sheet: StateMap<AccountAddress, Amount, S>,
}

/// The different errors the initialization can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject)]
pub enum InitError {
    /// Failed parsing the parameter
    #[from(ParseError)]
    ParseParams,
}
/// The result type for smart contract initialization
type InitResult<A> = Result<A, InitError>;

/// The different errors the smart contract calls can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject)]
pub enum ReceiveError {
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
    /// We have reached the end of our IDs (unlikely to happen)
    CounterOverflow,
    /// Not authorized as validator
    NotAValidator,
    /// Not authorized as judge
    NotAJudge,
    /// Cannot withdraw 0 CCDs
    ZeroWithdrawal,
    /// Settlement queue full,
    SettlementQueueFull,
    /// Invalid receiver when invoking a transfer.
    InvokeTransferMissingAccount,
    /// Insufficient funds when invoking a transfer.
    InvokeTransferInsufficientFunds,
}

/// Mapping errors related to transfer invocations to CustomContractError.
impl From<TransferError> for ReceiveError {
    fn from(te: TransferError) -> Self {
        match te {
            TransferError::AmountTooLarge => Self::InvokeTransferInsufficientFunds,
            TransferError::MissingAccount => Self::InvokeTransferMissingAccount,
        }
    }
}

/// The result type for smart contract calls
type ContractResult<A> = Result<A, ReceiveError>;

/// Initialize contract with empty balance sheet and no settlements
///
/// # Parameter
///
/// [ContractConfig] - the contract configuration
///
/// # Description
///
/// Creates a new instance of the smart contract from the given configuration.
/// The balance sheet and the settlement queue are initially empty.
#[init(contract = "offchain-transfers", parameter = "ContractConfig")]
#[inline(always)]
pub fn contract_init<S: HasStateApi>(
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

/// Deposit funds in smart contract
///
/// # Description
///
/// Allow the user (the caller) to deposit `amount` CCDs to the smart contract.
/// The amount is added to their balance sheet.
/// A new entry is created if the user did not exist before.
#[receive(contract = "offchain-transfers", name = "deposit", payable, mutable)]
#[inline(always)]
pub fn contract_receive_deposit<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    amount: Amount,
) -> ContractResult<()> {
    // Smart contracts are not allowed to call this function
    let sender_address = match ctx.sender() {
        Address::Contract(_) => bail!(ReceiveError::ContractSender),
        Address::Account(account_address) => account_address,
    };
    let mut balance =
        host.state_mut().balance_sheet.entry(sender_address).or_insert(Amount::zero()); //if the sender does not exist
    *balance += amount;

    Ok(())
}

/// Compute liabilities from given settlements for a sender address
fn get_liabilities(settlements: &[Settlement], sender_address: AccountAddress) -> Amount {
    let mut liabilities = Amount::zero();
    for settlement in settlements.iter() {
        for sender in settlement.transfer.send_transfers.iter() {
            if sender_address == sender.address {
                liabilities += sender.amount;
            }
        }
    }
    liabilities
}

/// Withdraw funds from smart contract.
///
/// # Parameter
///
/// [Amount] - the requested `payout`.
///
/// # Description
/// Allow the user (the caller) to withdraw funds from the settlement contract.
/// This is only possible if the user has sufficient funds in the worst case,
/// i.e., even if all outstanding payments to that user get cancelled and all
/// payments from that user are valid, there should be enough funds left to
/// withdraw the requested payout.
///
/// In short, a user as sufficient funds to withdraw `payout` CCDs if:
/// > balance - outstanding liabilities >= payout
///
/// This defensive payout mechanism ensures that user balance sheet
/// stays positive for any possible finalization of (a subset) outstanding
/// settlements.   
#[receive(contract = "offchain-transfers", name = "withdraw", mutable, parameter = "Amount")]
#[inline(always)]
pub fn contract_receive_withdraw<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    // Smart contracts are not allowed to call this function
    let sender_address = match ctx.sender() {
        Address::Contract(_) => bail!(ReceiveError::ContractSender),
        Address::Account(account_address) => account_address,
    };
    // Get request payout
    let payout: Amount = ctx.parameter_cursor().get()?;
    // The payout needs to be strictly positive
    ensure!(payout > Amount::zero(), ReceiveError::ZeroWithdrawal);

    // Add up liabilities that the user has in the pending settlements
    let liabilities = get_liabilities(&host.state().settlements, sender_address);

    {
        // ensure that the user has sufficient funds even in the worst case
        // where all liabilities are deducted and no credit is added
        let mut balance = host
            .state_mut()
            .balance_sheet
            .entry(sender_address)
            .occupied_or(ReceiveError::InsufficientFunds)?;

        ensure!(*balance >= liabilities + payout, ReceiveError::InsufficientFunds);

        // deduct payout
        *balance -= payout;
    }

    // If all ok, send the funds
    host.invoke_transfer(&sender_address, payout).unwrap_abort();

    Ok(())
}

/// Checks whether a transfer is syntactically valid.
/// That is, it checks that the sent and received amounts match
fn is_transfer_valid(transfer: &Transfer) -> bool {
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

/// Add new settlements to the contract.
///
/// # Parameter
///
/// [Transfer] - the transfer describing the settlement
///
/// # Description
///
/// Allows the validator to add a new settlement to the queue.
/// The validator provides the [Transfer] part which describes
/// the effect of the settlement in the form of a multi input-output
/// transfer.
/// The transfer is syntactically valid if it does not generate or delete funds.
///
/// To form the [Settlement] the smart contract adds a unique id
/// and the finality time. The finality time is computed from the timestamp
/// of the call and the `finality_time` in the smart contract config
///
/// The call is lazy in the sense that it does not check whether the
/// settlement could be applied to the current balance sheet.
#[receive(
    contract = "offchain-transfers",
    name = "add-settlement",
    mutable,
    parameter = "Transfer"
)]
#[inline(always)]
pub fn contract_receive_add_settlement<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    let sender = ctx.sender();
    // Only the validator may call this function
    ensure!(sender.matches_account(&host.state().config.validator), ReceiveError::NotAValidator);

    // Ensure there is space for the incoming settlement
    ensure!(
        host.state().settlements.len() < host.state().config.settlement_limit.try_into().unwrap(),
        ReceiveError::SettlementQueueFull
    );

    let transfer: Transfer = ctx.parameter_cursor().get()?;

    // Syntactically verify transfer information
    ensure!(is_transfer_valid(&transfer), ReceiveError::InvalidTransfer);
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

/// Veto settlement to remove it from the list of outstanding settlements.
///
/// # Parameter
///
/// [SettlementID]  - the ID of the vetoed settlement
///
/// # Description
///
/// Allows the judge to remove a *non-final* settlement from the list of
/// outstanding settlements.
///
/// The call is lazy in the sense that it does not check whether the
/// new settlement queue could be applied to the current balance sheet.
#[receive(contract = "offchain-transfers", name = "veto", mutable)]
#[inline(always)]
pub fn contract_receive_veto<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    let sender = ctx.sender();
    // Only the validator may call this function
    ensure!(sender.matches_account(&host.state().config.judge), ReceiveError::NotAJudge);
    // Get the ID
    let s_id: SettlementID = ctx.parameter_cursor().get()?;
    let now = ctx.metadata().slot_time(); //and time

    // Delete all settlements with the given ID from the list that are not final
    host.state_mut().settlements.retain(|s| s.id != s_id || s.finality_time <= now);

    Ok(())
}

fn is_settlement_valid<S: HasStateApi>(
    settlement: &Settlement,
    balance_sheet: &StateMap<AccountAddress, Amount, S>,
) -> bool {
    // check whether all senders have sufficient funds with respect to the updated
    // state first get of all senders (to avoid duplicate checks) and then
    // check for each sender in set
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

/// Execute all settlements with passed finality_time.
///
/// # Description
/// This function can periodically be called by everyone. It goes over the list
/// of settlements in the order in which they have been received and for those
/// whose finality time has passed, it does the following:
/// * Check whether the settlement is semantically valid. That means all senders
///   have sufficient funds to pay for the outgoing transfers. For this, the
///   updated funds including previous settlements are considered.
/// * If the settlement is valid, add the contained amounts to the corresponding
///   receivers and deduct them from the senders.
/// * Finally, all settlements with passed finality time (valid or not) are
///   removed from the list of outstanding settlements.
#[receive(contract = "offchain-transfers", name = "execute-settlements", mutable)]
#[inline(always)]
pub fn contract_receive_execute_settlements<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    let current_time = ctx.metadata().slot_time();
    let state_mut = host.state_mut();

    for settlement in state_mut.settlements.iter() {
        // only execute settlements for which finality time has passed and if they are
        // valid
        if current_time >= settlement.finality_time
            && is_settlement_valid(settlement, &state_mut.balance_sheet)
        {
            // first add balances of all receivers and then subtract of senders
            // together with the validity of settlements, this implies nonnegative amounts
            // for all accounts
            for receive_transfer in settlement.transfer.receive_transfers.iter() {
                let mut receiver_balance = state_mut
                    .balance_sheet
                    .entry(receive_transfer.address)
                    .or_insert(Amount::zero());
                *receiver_balance += receive_transfer.amount;
            }

            for send_transfer in settlement.transfer.send_transfers.iter() {
                let mut sender_balance =
                    state_mut.balance_sheet.entry(send_transfer.address).or_insert(Amount::zero());
                *sender_balance -= send_transfer.amount;
            }
        }
    }

    // remove all settlements for which finality time has passed from list
    state_mut.settlements.retain(|s| current_time < s.finality_time);

    Ok(())
}

/// Get the balance of given address.
///
/// # Description
///
/// Gets the currently available balance of a given address.
/// This is the amount that could be withdrawn by the
/// given address.
#[receive(
    contract = "offchain-transfers",
    name = "settled-balance-of",
    parameter = "AccountAddress",
    return_value = "Amount"
)]
pub fn contract_available_balance_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<Amount> {
    // Parse the parameter.
    let query_address: AccountAddress = ctx.parameter_cursor().get()?;
    // Build the response.
    // Add up liabilities that the user has in the pending settlements
    let liabilities = get_liabilities(&host.state().settlements, query_address);
    let balance = host.state().balance_sheet.get(&query_address);
    let balance = match balance {
        None => Amount::zero(),
        Some(value) => *value,
    };
    let mut result = Amount::zero();
    if balance - liabilities > Amount::zero() {
        result = balance - liabilities;
    }
    Ok(result)
}

/// Get a settlement from a given ID
///
/// # Description
///
/// Looks up the settlement for a given ID. Returns
/// None if none exists.
#[receive(
    contract = "offchain-transfers",
    name = "get-settlement",
    parameter = "SettlementID",
    return_value = "Settlement"
)]
pub fn contract_get_settlement<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<Option<Settlement>> {
    // Parse the parameter.
    let id: SettlementID = ctx.parameter_cursor().get()?;
    // Build the response.
    let result = host.state().settlements.iter().find(|s| s.id == id);

    match result {
        None => Ok(None),
        Some(settlement) => Ok(Some(settlement.clone())),
    }
}

// Tests //
