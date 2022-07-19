#![cfg_attr(not(feature = "std"), no_std)]

use concordium_std::*;

/// The different errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject)]
enum MyContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
    AmountTooLarge,
    MissingAccount,
    LeftOverAmount,
}

type ContractResult<A> = Result<A, MyContractError>;

/// Mapping errors related to contract invocations to CustomContractError.
impl From<TransferError> for MyContractError {
    fn from(err: TransferError) -> Self {
        match err {
            TransferError::MissingAccount => MyContractError::MissingAccount,
            TransferError::AmountTooLarge => MyContractError::AmountTooLarge,
        }
    }
}

// Contract functions

/// Initialize contract instance.
#[init(contract = "Multi")]
fn contract_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<()> {
    Ok(())
}

#[derive(Debug, Serial, Deserial)]
struct TransferParameter {
    #[concordium(size_length = 2)]
    transfers: Vec<Transfer>,
}

impl schema::SchemaType for TransferParameter {
    fn get_type() -> schema::Type {
        schema::Type::List(schema::SizeLength::U16, Box::new(Transfer::get_type()))
    }
}

/// A single transfer
#[derive(Debug, Serialize)]
struct Transfer {
    /// Receiver of the amount of tokens.
    account: AccountAddress,
    /// The amount of tokens
    amount:  Amount,
}

impl schema::SchemaType for Transfer {
    fn get_type() -> schema::Type {
        schema::Type::Struct(schema::Fields::Named(vec![
            ("account".to_string(), schema::Type::AccountAddress),
            ("amount".to_string(), schema::Type::Amount),
        ]))
    }
}

/// Execute a list of token transfers, in the order of the list.
#[receive(contract = "Multi", name = "transfer", parameter = "TransferParameter", payable)]
fn contract_transfer<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<(), StateApiType = S>,
    total_amount: Amount,
) -> ContractResult<()> {
    // Parse the parameter.
    let TransferParameter {
        transfers,
    } = ctx.parameter_cursor().get()?;

    let mut sum = Amount::from_micro_ccd(0);
    for Transfer {
        amount,
        account,
    } in transfers
    {
        sum += amount;
        host.invoke_transfer(&account, amount)?;
    }
    ensure_eq!(sum, total_amount, MyContractError::LeftOverAmount);
    Ok(())
}

// Tests

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    const ACCOUNT_0: AccountAddress = AccountAddress([5u8; 32]);
    const ACCOUNT_1: AccountAddress = AccountAddress([1u8; 32]);
    const ACCOUNT_2: AccountAddress = AccountAddress([2u8; 32]);
    const ACCOUNT_3: AccountAddress = AccountAddress([3u8; 32]);
    const ACCOUNT_4: AccountAddress = AccountAddress([4u8; 32]);

    #[concordium_test]
    fn test_transfer_to_5() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();

        let parameter = TransferParameter {
            transfers: vec![
                Transfer {
                    amount:  Amount::from_micro_ccd(100),
                    account: ACCOUNT_0,
                },
                Transfer {
                    amount:  Amount::from_micro_ccd(200),
                    account: ACCOUNT_1,
                },
                Transfer {
                    amount:  Amount::from_micro_ccd(300),
                    account: ACCOUNT_2,
                },
                Transfer {
                    amount:  Amount::from_micro_ccd(400),
                    account: ACCOUNT_3,
                },
                Transfer {
                    amount:  Amount::from_micro_ccd(500),
                    account: ACCOUNT_4,
                },
            ],
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let state_builder = TestStateBuilder::new();

        let mut host = TestHost::new((), state_builder);
        let amount = Amount::from_micro_ccd(1500);
        host.set_self_balance(amount);

        // Call the contract function.
        let result: ContractResult<()> = contract_transfer(&ctx, &host, amount);

        result.expect_report("Rejects");

        let transfers = host.get_transfers();
        claim_eq!(transfers.len(), 5, "Missing result")
    }

    #[concordium_test]
    fn test_transfer_fails_with_insufficient_amount() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();

        let parameter = TransferParameter {
            transfers: vec![
                Transfer {
                    amount:  Amount::from_micro_ccd(100),
                    account: ACCOUNT_0,
                },
                Transfer {
                    amount:  Amount::from_micro_ccd(200),
                    account: ACCOUNT_1,
                },
                Transfer {
                    amount:  Amount::from_micro_ccd(300),
                    account: ACCOUNT_2,
                },
                Transfer {
                    amount:  Amount::from_micro_ccd(400),
                    account: ACCOUNT_3,
                },
                Transfer {
                    amount:  Amount::from_micro_ccd(500),
                    account: ACCOUNT_4,
                },
            ],
        };
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let state_builder = TestStateBuilder::new();

        let mut host = TestHost::new((), state_builder);
        let amount = Amount::from_micro_ccd(1000);
        host.set_self_balance(amount);

        // Call the contract function.
        let result: ContractResult<()> = contract_transfer(&ctx, &host, amount);
        let err = result.expect_err_report("Did not fail");
        claim_eq!(err, MyContractError::AmountTooLarge);
    }
}
