/*!
 * A contract that acts like an account (can send, store and accept CCD),
 * but requires n > 1 ordained accounts to agree to the sending of CCD
 * before it is accepted. This is useful for storing CCD where the security
 * of just one account isn’t considered high enough.
 *
 * Transfer requests time out if not agreed to within the contract's
 * specified time-to-live for transfer requests
 *
 * Transfer requests are given IDs to disambiguate otherwise identical
 * requests, since they might have different motivations behind the scenes,
 * making them not-quite fungible (e.g. for accounting purposes it might be
 * necessary for account holders to track a particular named transfer).
 *
 * Depositing funds:
 *   Allowed at any time from anyone.
 *
 * Transferring funds:
 *   Only requestable by accounts named at initialization, and only with the
 *   agreement of at least n of those accounts, but can send to any account.
 *
 * At the point when a transfer/withdrawal is requested, the account balance
 * is checked. Either there are not enough funds and the request is
 * rejected, or there are enough funds and the requested sum is set aside
 * (and can be re-added to the balance if the request times out).
 *
 * TODO Consider allowing the person who initially made the request to
 * cancel it, iff it is still outstanding.
 */

#![cfg_attr(not(feature = "std"), no_std)]

use concordium_std::{collections::*, *};

// Types
#[derive(Serialize, SchemaType)]
enum Message {
    /// Indicates that the user sending the message would like to make a request
    /// to send funds to the given address with the given ID and amount.
    /// This is a no-op if the given ID already exists and has not timed out.
    RequestTransfer(TransferRequestId, Amount, AccountAddress),

    /// Indicates that the user sending the message votes in favour of the
    /// transfer with the given ID and amount to the given account address.
    /// This is a no-op if the given ID does not exist (potentially due to
    /// timing out), or exists with a different amount or address.
    SupportTransfer(TransferRequestId, Amount, AccountAddress),
}

type TransferRequestId = u64;

type TransferRequestTimeToLiveMilliseconds = Duration;
type TimeoutSlotTimeMilliseconds = Timestamp;

#[derive(Clone, Serialize, SchemaType)]
struct TransferRequest {
    transfer_amount: Amount,
    target_account:  AccountAddress,
    times_out_at:    TimeoutSlotTimeMilliseconds,
    supporters:      BTreeSet<AccountAddress>,
}

#[derive(Serialize, SchemaType, Clone)]
struct InitParams {
    /// Who is authorized to withdraw funds from this lockup (must be non-empty)
    #[concordium(size_length = 1)]
    account_holders: BTreeSet<AccountAddress>,

    /// How many of the account holders need to agree before funds are released
    transfer_agreement_threshold: u8,

    /// How long to wait before dropping a request due to lack of support
    /// N.B. If this is set too long, in practice the chain might !ome busy
    /// enough that requests time out before they can be agreed to by all
    /// parties, so be wary of setting this too low. On the other hand,
    /// if this is set too high, a bunch of pending requests can get into
    /// a murky state where some account holders may consider the request
    /// obsolete, only for another account holder to "resurrect" it, so
    /// having _some_ time out gives some security against old requests
    /// being surprisingly accepted.
    transfer_request_ttl: TransferRequestTimeToLiveMilliseconds,
}

#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
pub struct State<S> {
    /// The initial configuration of the contract
    init_params: InitParams,

    /// Requests which have not been dropped due to timing out or due to being
    /// agreed to yet The request ID, the associated amount, when it times
    /// out, who is making the transfer and which account holders support
    /// this transfer
    requests: StateMap<TransferRequestId, TransferRequest, S>,
}

// Contract implementation

#[derive(Debug, PartialEq, Eq, Reject, Serial)]
enum InitError {
    /// Failed parsing the parameter
    #[from(ParseError)]
    ParseParams,
    /// Not enough account holders: At least two are needed for this contract
    /// to be valid.
    InsufficientAccountHolders,
    /// The threshold for agreeing account holders to allow a transfer must be
    /// less than or equal to the number of unique account holders, else a
    /// transfer can never be made!
    ThresholdAboveAccountHolders,
    /// The number of account holders required to accept a transfer must be two
    /// or more else you would be better off with a normal account!
    ThresholdBelowTwo,
}

#[init(contract = "two-step-transfer", parameter = "InitParams", payable)]
#[inline(always)]
fn contract_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
    _amount: Amount,
) -> Result<State<S>, InitError> {
    let init_params: InitParams = ctx.parameter_cursor().get()?;
    ensure!(init_params.account_holders.len() >= 2, InitError::InsufficientAccountHolders);
    ensure!(
        init_params.transfer_agreement_threshold <= init_params.account_holders.len() as u8,
        InitError::ThresholdAboveAccountHolders
    );
    ensure!(init_params.transfer_agreement_threshold >= 2, InitError::ThresholdBelowTwo);

    let state = State {
        init_params,
        requests: state_builder.new_map(),
    };

    Ok(state)
}

#[receive(contract = "two-step-transfer", name = "deposit", payable)]
#[inline(always)]
fn contract_receive_deposit<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    _host: &impl HasHost<State<S>, StateApiType = S>,
    _amount: Amount,
) -> ReceiveResult<()> {
    Ok(())
}

#[derive(Debug, PartialEq, Eq, Reject, Serial, SchemaType)]
enum ReceiveError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    /// Only account holders can interact with this contract.
    NotAccountHolder,
    /// Sender cannot be a contract.
    ContractSender,
    /// A request with this ID already exists.
    RequestAlreadyExists,
    /// Not enough available funds for the requested transfer.
    InsufficientAvailableFunds,
    /// No such transfer to support.
    UnknownTransfer,
    /// The request have timed out.
    RequestTimeout,
    /// Transfer amount or account is different from the request.
    MismatchingRequestInformation,
    /// You have already supported this transfer.
    RequestAlreadySupported,
    /// End time is not expressible, i.e., would overflow.
    Overflow,
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

type ContractResult<A> = Result<A, ReceiveError>;

#[receive(
    contract = "two-step-transfer",
    name = "receive",
    parameter = "Message",
    payable,
    mutable,
    error = "ReceiveError"
)]
#[inline(always)]
fn contract_receive_message<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    amount: Amount,
) -> ContractResult<()> {
    let sender = ctx.sender();
    ensure!(
        host.state()
            .init_params
            .account_holders
            .iter()
            .any(|account_holder| sender.matches_account(account_holder)),
        ReceiveError::NotAccountHolder
    );
    let sender_address = match sender {
        Address::Contract(_) => bail!(ReceiveError::ContractSender),
        Address::Account(account_address) => account_address,
    };
    let now = ctx.metadata().slot_time();

    let msg: Message = ctx.parameter_cursor().get()?;
    match msg {
        Message::RequestTransfer(req_id, transfer_amount, target_account) => {
            // Remove outdated requests and calculate the reserved balance
            let mut reserved_balance = Amount::zero();
            let mut active_requests: BTreeMap<TransferRequestId, TransferRequest> = BTreeMap::new();
            for (key, req) in host.state().requests.iter() {
                if req.times_out_at > now {
                    active_requests.insert(*key, req.clone());
                    reserved_balance += req.transfer_amount;
                }
            }

            // Persist the active requests
            host.state_mut().requests = host.state_builder().new_map();
            for (key, req) in active_requests.iter() {
                let _ = host.state_mut().requests.insert(*key, req.clone());
            }

            // Check if a request already exists
            let mut contains = false;
            for (k, _) in host.state().requests.iter() {
                if *k == req_id {
                    contains = true;
                    break;
                }
            }
            ensure!(!contains, ReceiveError::RequestAlreadyExists);

            // Ensure enough funds for the requested transfer
            let balance = amount + host.self_balance();
            ensure!(
                balance - reserved_balance >= transfer_amount,
                ReceiveError::InsufficientAvailableFunds
            );

            // Create the request with the sender as the only supporter
            let mut supporters = BTreeSet::new();
            supporters.insert(sender_address);
            let new_request = TransferRequest {
                transfer_amount,
                target_account,
                times_out_at: now
                    .checked_add(host.state().init_params.transfer_request_ttl)
                    .ok_or(ReceiveError::Overflow)?,
                supporters,
            };

            let _ = host.state_mut().requests.insert(req_id, new_request);
            Ok(())
        }

        Message::SupportTransfer(transfer_request_id, transfer_amount, target_account) => {
            let transfer = {
                let threshold = host.state().init_params.transfer_agreement_threshold;
                let mut matching_request = host
                    .state_mut()
                    .requests
                    .entry(transfer_request_id)
                    .occupied_or(ReceiveError::UnknownTransfer)?;

                ensure!(matching_request.times_out_at > now, ReceiveError::RequestTimeout);
                ensure!(
                    matching_request.transfer_amount == transfer_amount,
                    ReceiveError::MismatchingRequestInformation
                );
                ensure!(
                    matching_request.target_account == target_account,
                    ReceiveError::MismatchingRequestInformation
                );
                ensure!(
                    !matching_request.supporters.contains(&sender_address),
                    ReceiveError::RequestAlreadySupported
                );
                matching_request.supporters.insert(sender_address);
                matching_request.supporters.len() >= usize::from(threshold)
            };

            if transfer {
                host.invoke_transfer(&target_account, transfer_amount)?;
                host.state_mut().requests.remove(&transfer_request_id);
            }
            Ok(())
        }
    }
}

// Tests

#[concordium_cfg_test]
#[allow(deprecated)]
mod tests {
    use super::*;
    use concordium_std::test_infrastructure::*;

    /// Total reserved balance determined by active requests relative to `now`
    fn sum_reserved_balance<S: HasStateApi>(state: &State<S>, now: Timestamp) -> Amount {
        state
            .requests
            .iter()
            .filter(|(_, req)| req.times_out_at > now)
            .map(|(_, req)| req.transfer_amount)
            .sum()
    }

    #[concordium_test]
    /// Initialise contract with account holders
    fn test_init() {
        // Setup context
        let account1 = AccountAddress([1u8; 32]);
        let account2 = AccountAddress([2u8; 32]);

        let mut account_holders = BTreeSet::new();
        account_holders.insert(account1);
        account_holders.insert(account2);

        let parameter = InitParams {
            account_holders,
            transfer_agreement_threshold: 2,
            transfer_request_ttl: TransferRequestTimeToLiveMilliseconds::from_millis(10),
        };
        let parameter_bytes = to_bytes(&parameter);

        let mut ctx = TestInitContext::empty();
        ctx.set_parameter(&parameter_bytes);

        let amount = Amount::from_micro_ccd(0);
        let mut state_builder = TestStateBuilder::new();
        // call the init function
        let out = contract_init(&ctx, &mut state_builder, amount);

        // and inspect the result.
        let state = match out {
            Ok(s) => s,
            Err(_) => fail!("Contract initialization failed."),
        };
        claim!(
            state.init_params.account_holders.contains(&account1),
            "Should contain the first account holder"
        );
        claim!(
            state.init_params.account_holders.contains(&account2),
            "Should contain the second account holder"
        );
        claim_eq!(
            state.init_params.account_holders.len(),
            2,
            "Should not contain more account holders"
        );
        // and make sure the correct logs were produced.
        claim_eq!(state.requests.iter().count(), 0, "No transfer request at initialisation");
    }

    #[concordium_test]
    /// Creates the request
    ///
    /// - Mutates the state with the request
    /// - Sets the right amount aside for the request
    /// - Only have the sender support the request at this point
    fn test_receive_request() {
        // Setup context
        let account1 = AccountAddress([1u8; 32]);
        let account2 = AccountAddress([2u8; 32]);
        let target_account = AccountAddress([3u8; 32]);

        let request_id = 0;
        let transfer_amount = Amount::from_micro_ccd(50);
        // Create Request with id 0, to transfer 50 to target_account
        let parameter = Message::RequestTransfer(request_id, transfer_amount, target_account);
        let parameter_bytes = to_bytes(&parameter);

        let mut ctx = TestReceiveContext::empty();
        ctx.set_parameter(&parameter_bytes);
        ctx.set_sender(Address::Account(account1));
        ctx.metadata_mut().set_slot_time(Timestamp::from_timestamp_millis(0));

        // Setup state
        let mut account_holders = BTreeSet::new();
        account_holders.insert(account1);
        account_holders.insert(account2);
        let init_params = InitParams {
            account_holders,
            transfer_agreement_threshold: 2,
            transfer_request_ttl: TransferRequestTimeToLiveMilliseconds::from_millis(10),
        };

        let mut state_builder = TestStateBuilder::new();
        let state = State {
            init_params,
            requests: state_builder.new_map(),
        };
        let mut host = TestHost::new(state, state_builder);
        host.set_self_balance(Amount::from_micro_ccd(0));

        let receive_amount = Amount::from_micro_ccd(100);
        // Execution
        let res = contract_receive_message(&ctx, &mut host, receive_amount);
        claim!(res.is_ok(), "Contract receive failed, but it should not have.");

        claim_eq!(
            sum_reserved_balance(host.state(), Timestamp::from_timestamp_millis(0)),
            Amount::from_micro_ccd(50),
            "Contract receive did not reserve requested amount"
        );
        let request = host.state().requests.get(&request_id).unwrap();
        claim_eq!(request.supporters.len(), 1, "Only one is supporting the request from start");
        claim!(request.supporters.contains(&account1), "The request sender supports the request");
    }

    #[concordium_test]
    /// Support a request without entering the threshold
    ///
    /// - Mutates the request in the state by adding the supporter
    fn test_receive_support_no_transfer() {
        // Setup context
        let account1 = AccountAddress([1u8; 32]);
        let account2 = AccountAddress([2u8; 32]);
        let account3 = AccountAddress([3u8; 32]);
        let target_account = AccountAddress([3u8; 32]);

        let request_id = 0;
        let transfer_amount = Amount::from_micro_ccd(50);
        let parameter = Message::SupportTransfer(request_id, transfer_amount, target_account);
        let parameter_bytes = to_bytes(&parameter);

        let mut ctx = TestReceiveContext::empty();
        ctx.set_parameter(&parameter_bytes);
        ctx.metadata_mut().set_slot_time(Timestamp::from_timestamp_millis(100));
        ctx.set_sender(Address::Account(account2));

        // Setup state
        let mut account_holders = BTreeSet::new();
        account_holders.insert(account1);
        account_holders.insert(account2);
        account_holders.insert(account3);
        let init_params = InitParams {
            account_holders,
            transfer_agreement_threshold: 3,
            transfer_request_ttl: TransferRequestTimeToLiveMilliseconds::from_millis(10),
        };
        let mut supporters = BTreeSet::new();
        supporters.insert(account1);
        let request = TransferRequest {
            supporters,
            target_account,
            times_out_at: Timestamp::from_timestamp_millis(200),
            transfer_amount,
        };

        let mut state_builder = TestStateBuilder::new();
        let mut requests = state_builder.new_map();
        let _ = requests.insert(request_id, request);
        let state = State {
            init_params,
            requests,
        };
        let mut host = TestHost::new(state, state_builder);

        let receive_amount = Amount::from_micro_ccd(75);

        // Execution
        let res: ContractResult<()> = contract_receive_message(&ctx, &mut host, receive_amount);

        claim!(res.is_ok(), "Contract receive support failed, but it should not have.:");
        claim_eq!(
            sum_reserved_balance(host.state(), Timestamp::from_timestamp_millis(0)),
            Amount::from_micro_ccd(50),
            "Contract receive did not reserve the requested amount"
        );
        let request = host.state().requests.get(&request_id).unwrap();
        claim_eq!(request.supporters.len(), 2, "Two should support the transfer request");
        claim!(request.supporters.contains(&account2), "The support sender supports the request");
    }

    #[concordium_test]
    /// Support a request triggering the transfer
    ///
    /// - Results in the transfer
    /// - Removes the request from state
    /// - Updates the reserved_balance
    fn test_receive_support_transfer() {
        // Setup context
        let account1 = AccountAddress([1u8; 32]);
        let account2 = AccountAddress([2u8; 32]);
        let account3 = AccountAddress([3u8; 32]);
        let target_account = AccountAddress([3u8; 32]);

        let request_id = 0;
        let transfer_amount = Amount::from_micro_ccd(50);
        let parameter = Message::SupportTransfer(request_id, transfer_amount, target_account);
        let parameter_bytes = to_bytes(&parameter);

        let mut ctx = TestReceiveContext::empty();
        ctx.set_parameter(&parameter_bytes);
        ctx.set_sender(Address::Account(account2));
        ctx.metadata_mut().set_slot_time(Timestamp::from_timestamp_millis(0));

        // Setup state
        let mut account_holders = BTreeSet::new();
        account_holders.insert(account1);
        account_holders.insert(account2);
        account_holders.insert(account3);
        let init_params = InitParams {
            account_holders,
            transfer_agreement_threshold: 2,
            transfer_request_ttl: TransferRequestTimeToLiveMilliseconds::from_millis(10),
        };
        let mut supporters = BTreeSet::new();
        supporters.insert(account1);
        let request = TransferRequest {
            supporters,
            target_account,
            times_out_at: Timestamp::from_timestamp_millis(10),
            transfer_amount,
        };

        let mut state_builder = TestStateBuilder::new();
        let mut requests = state_builder.new_map();
        let _ = requests.insert(request_id, request);
        let state = State {
            init_params,
            requests,
        };

        let mut host = TestHost::new(state, state_builder);
        host.set_self_balance(Amount::from_micro_ccd(100)); //

        // Execution
        let res: ContractResult<()> =
            contract_receive_message(&ctx, &mut host, Amount::from_ccd(0));

        claim!(res.is_ok(), "Contract receive support failed, but it should not have.");
        claim_eq!(
            sum_reserved_balance(host.state(), Timestamp::from_timestamp_millis(0)),
            Amount::from_micro_ccd(0),
            "The transfer should be subtracted from the reserved balance"
        );
    }

    #[concordium_test]
    /// Test handling of a duplicate transfer request
    ///
    /// This test also showcases how to use rollbacks on rejections in tests.
    ///
    /// - Starts out with two requests, id 0, outdated, and id 1, active.
    /// - A duplicate transfer request with id 1 is sent.
    /// - The outdated request is removed from the state.
    /// - The entrypoint rejects because the new request is a duplicate.
    /// - The state is rolled back to the starting point.
    fn test_receive_duplicate_request() {
        // Setup context
        let account1 = AccountAddress([1u8; 32]);
        let account2 = AccountAddress([2u8; 32]);
        let target_account = AccountAddress([3u8; 32]);

        let request_id_outdated = 0;
        let request_id_active = 1;
        let transfer_amount = Amount::from_micro_ccd(50);
        // Create Request with id 0, to transfer 50 to target_account
        let parameter =
            Message::RequestTransfer(request_id_active, transfer_amount, target_account);
        let parameter_bytes = to_bytes(&parameter);

        let mut ctx = TestReceiveContext::empty();
        ctx.set_parameter(&parameter_bytes);
        ctx.set_sender(Address::Account(account1));
        ctx.metadata_mut().set_slot_time(Timestamp::from_timestamp_millis(1000));

        // Setup state
        let mut account_holders = BTreeSet::new();
        account_holders.insert(account1);
        account_holders.insert(account2);
        let init_params = InitParams {
            account_holders,
            transfer_agreement_threshold: 2,
            transfer_request_ttl: TransferRequestTimeToLiveMilliseconds::from_millis(10),
        };

        let mut state_builder = TestStateBuilder::new();
        let mut requests = state_builder.new_map();

        let mut supporters = BTreeSet::new();
        supporters.insert(account1);

        // Outdated request
        let _ = requests.insert(request_id_outdated, TransferRequest {
            transfer_amount,
            target_account,
            times_out_at: ctx
                .metadata()
                .slot_time()
                .checked_sub(init_params.transfer_request_ttl) // In the past.
                .expect_report("Checked sub for times_out_at failed."),
            supporters: supporters.clone(),
        });

        // Active request
        let _ = requests.insert(request_id_active, TransferRequest {
            transfer_amount,
            target_account,
            times_out_at: ctx
                .metadata()
                .slot_time()
                .checked_add(init_params.transfer_request_ttl) // In the future.
                .expect_report("Checked sub for times_out_at failed."),
            supporters,
        });

        let state = State {
            init_params,
            requests,
        };
        let mut host = TestHost::new(state, state_builder);
        host.set_self_balance(Amount::from_micro_ccd(100));

        // Execution. Note the use for `with_rollback`.
        let res = host.with_rollback(|host| contract_receive_message(&ctx, host, Amount::zero()));
        claim_eq!(res, Err(ReceiveError::RequestAlreadyExists));

        // Check that both initial requests still exist in the state since it was rolled
        // back.
        claim!(host.state().requests.get(&request_id_outdated).is_some());
        claim!(host.state().requests.get(&request_id_active).is_some());
    }

    /// Assume a single transfer request in the requests map with arbitrary
    /// `request_id`, `transfer_amount`, and `target_account`, such that it
    /// is not expired and supported by two addresses (including the sender).
    ///
    /// Then, sending a `SupportTransfer` message with the same `request_id`,
    /// `transfer_amount`, and `target_account` results in success and zero
    /// reserved balance (as defined by `sum_reserved_balance`).
    ///
    /// The call comes from an arbitrary `sender`, such that it is in the
    /// list of account_holders along with two other addresses.
    ///
    /// By "arbitrary" we mean random values generated by QuickCheck's.
    /// The `tests` attribute specifies the number of tests to run
    #[concordium_quickcheck(num_tests = 500)]
    fn prop_receive_support_transfer(
        sender: AccountAddress,
        account1: AccountAddress,
        account2: AccountAddress,
        request_id: u64,
        target_account: AccountAddress,
        transfer_amount: Amount,
        ccd_amount: Amount,
    ) -> bool {
        // Setup context
        let parameter = Message::SupportTransfer(request_id, transfer_amount, target_account);
        let parameter_bytes = to_bytes(&parameter);

        let mut ctx = TestReceiveContext::empty();
        ctx.set_parameter(&parameter_bytes);
        ctx.set_sender(Address::Account(sender));
        ctx.metadata_mut().set_slot_time(Timestamp::from_timestamp_millis(0));

        // Setup state
        let mut account_holders = BTreeSet::new();
        account_holders.insert(sender);
        account_holders.insert(account1);
        account_holders.insert(account2);
        let init_params = InitParams {
            account_holders,
            transfer_agreement_threshold: 2,
            transfer_request_ttl: TransferRequestTimeToLiveMilliseconds::from_millis(10),
        };
        let mut supporters = BTreeSet::new();
        // we add one more account to `supporters` so with the sender account the number
        // of supporters reaches the threshold
        supporters.insert(account1);
        let request = TransferRequest {
            supporters,
            target_account,
            times_out_at: Timestamp::from_timestamp_millis(10),
            transfer_amount,
        };

        let mut state_builder = TestStateBuilder::new();
        let mut requests = state_builder.new_map();
        let _ = requests.insert(request_id, request);
        let state = State {
            init_params,
            requests,
        };

        let mut host = TestHost::new(state, state_builder);
        host.set_self_balance(transfer_amount);

        // Execution
        // Note: `ccd_amount` doesn't affect the outcome
        // Maybe the contract should reject if it's not zero
        let res: ContractResult<()> = contract_receive_message(&ctx, &mut host, ccd_amount);
        // The contract execution shouldn't fail and the sum of reserved balances should
        // be zero
        res.is_ok()
            && (sum_reserved_balance(host.state(), Timestamp::from_timestamp_millis(0))
                == Amount::from_micro_ccd(0))
    }
}
