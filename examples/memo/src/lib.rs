use concordium_std::*;
use core::fmt::Debug;

/// # Implementation of a smart contract that can receive transfers with a memo
/// message and forward them to the owner account.

/// The contract has no state.
#[derive(Debug, Serialize, SchemaType)]
struct MemoState;

#[derive(Serialize, SchemaType)]
/// The contract has no initialization parameters.
struct InitParameter;

/// Init function that creates a new contract.
#[init(contract = "memo", parameter = "InitParameter", low_level)]
fn memo_init(_ctx: &impl HasInitContext, _state: &mut impl HasContractState) -> InitResult<()> {
    Ok(())
}

const EXPECTED_PARAMETER_SIZE: u32 = 32;

pub type ReceiveParameter = [u8; 32];

/// Receive a transaction with a message. This ensures that the message is 32
/// bytes and that the sender of the message is an account.
#[receive(contract = "memo", name = "receive", parameter = "ReceiveParameter", payable, low_level)]
fn memo_receive<A: HasActions>(
    ctx: &impl HasReceiveContext,
    amount: Amount,
    _state: &mut impl HasContractState,
) -> ReceiveResult<A> {
    matches!(ctx.sender(), Address::Account(..));
    ensure!(ctx.parameter_cursor().size() == EXPECTED_PARAMETER_SIZE);
    // Forward the received funds to the owner of the contract.
    let act = A::simple_transfer(&ctx.owner(), amount);
    Ok(act)
}
