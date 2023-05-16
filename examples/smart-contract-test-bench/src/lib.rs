//! Smart contract test bench
#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;

/// The different errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
enum ContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams,
}

const _PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([
    55, 162, 168, 229, 46, 250, 217, 117, 219, 246, 88, 14, 119, 52, 228, 242, 73, 234, 165, 234,
    138, 118, 62, 147, 74, 134, 113, 205, 126, 68, 100, 153,
]);

const _SIGNATURE: SignatureEd25519 = SignatureEd25519([
    99, 47, 86, 124, 147, 33, 64, 92, 226, 1, 160, 163, 134, 21, 218, 65, 239, 226, 89, 237, 225,
    84, 255, 69, 173, 150, 205, 248, 96, 113, 142, 121, 189, 224, 124, 255, 114, 196, 209, 25, 198,
    68, 85, 42, 140, 127, 12, 65, 63, 92, 245, 57, 11, 14, 160, 69, 137, 147, 214, 214, 55, 75,
    217, 4,
]);

/// The contract state.
#[derive(Serial, Deserial, Clone, SchemaType)]
struct State {
    u8_value: u8,
    u16_value: u16,
    address_array: Vec<Address>,
    address_value: Address,
    account_address_value: AccountAddress,
    contract_address_value: ContractAddress,
}

/// Init function that creates this smart_contract_test_bench.
#[init(contract = "smart_contract_test_bench")]
fn contract_init<S: HasStateApi>(
    _ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<State> {
    Ok(State {
        u8_value: 0u8,
        u16_value: 0u16,
        address_array: vec![],
        address_value: Address::Account(AccountAddress([0u8; 32])),
        account_address_value: AccountAddress([0u8; 32]),
        contract_address_value: ContractAddress {
            index: 0,
            subindex: 0,
        },
    })
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "set_u8",
    parameter = "u8",
    error = "ContractError",
    mutable
)]
fn set_u8<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<(), ContractError> {
    let value: u8 = ctx.parameter_cursor().get()?;
    host.state_mut().u8_value = value;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "set_u8_payable",
    parameter = "u8",
    error = "ContractError",
    mutable,
    payable
)]
fn set_u8_payable<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
    _amount: Amount,
) -> Result<(), ContractError> {
    let value: u8 = ctx.parameter_cursor().get()?;
    host.state_mut().u8_value = value;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "get_u8",
    return_value = "u8",
    error = "ContractError",
    mutable
)]
fn get_u8<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<u8, ContractError> {
    Ok(host.state_mut().u8_value)
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "set_u16",
    parameter = "u16",
    error = "ContractError",
    mutable
)]
fn set_u16<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<(), ContractError> {
    let value: u16 = ctx.parameter_cursor().get()?;
    host.state_mut().u16_value = value;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "set_u16_payable",
    parameter = "u16",
    error = "ContractError",
    mutable,
    payable
)]
fn set_u16_payable<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
    _amount: Amount,
) -> Result<(), ContractError> {
    let value: u16 = ctx.parameter_cursor().get()?;
    host.state_mut().u16_value = value;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "get_u16",
    return_value = "u16",
    error = "ContractError",
    mutable
)]
fn get_u16<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<u16, ContractError> {
    Ok(host.state_mut().u16_value)
}


#[receive(
    contract = "smart_contract_test_bench",
    name = "set_address",
    parameter = "Address",
    error = "ContractError",
    mutable
)]
fn set_address<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<(), ContractError> {
    let value: Address = ctx.parameter_cursor().get()?;
    host.state_mut().address_value = value;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "set_address_payable",
    parameter = "Address",
    error = "ContractError",
    mutable,
    payable
)]
fn set_address_payable<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
    _amount: Amount,
) -> Result<(), ContractError> {
    let value: Address = ctx.parameter_cursor().get()?;
    host.state_mut().address_value = value;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "get_address",
    return_value = "Address",
    error = "ContractError",
    mutable
)]
fn get_address<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<Address, ContractError> {
    Ok(host.state_mut().address_value)
}


#[receive(
    contract = "smart_contract_test_bench",
    name = "set_contract_address",
    parameter = "ContractAddress",
    error = "ContractError",
    mutable
)]
fn set_contract_address<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<(), ContractError> {
    let value: ContractAddress = ctx.parameter_cursor().get()?;
    host.state_mut().contract_address_value = value;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "set_contract_address_payable",
    parameter = "ContractAddress",
    error = "ContractError",
    mutable,
    payable
)]
fn set_contract_address_payable<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
    _amount: Amount,
) -> Result<(), ContractError> {
    let value: ContractAddress = ctx.parameter_cursor().get()?;
    host.state_mut().contract_address_value = value;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "get_contract_address",
    return_value = "ContractAddress",
    error = "ContractError",
    mutable
)]
fn get_contract_address<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<ContractAddress, ContractError> {
    Ok(host.state_mut().contract_address_value)
}


#[receive(
    contract = "smart_contract_test_bench",
    name = "set_account_address",
    parameter = "AccountAddress",
    error = "ContractError",
    mutable
)]
fn set_account_address<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<(), ContractError> {
    let value: AccountAddress = ctx.parameter_cursor().get()?;
    host.state_mut().account_address_value = value;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "set_account_address_payable",
    parameter = "AccountAddress",
    error = "ContractError",
    mutable,
    payable
)]
fn set_account_address_payable<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
    _amount: Amount,
) -> Result<(), ContractError> {
    let value: AccountAddress = ctx.parameter_cursor().get()?;
    host.state_mut().account_address_value = value;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "get_account_address",
    return_value = "AccountAddress",
    error = "ContractError",
    mutable
)]
fn get_account_address<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<AccountAddress, ContractError> {
    Ok(host.state_mut().account_address_value)
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "set_address_array",
    parameter = "Vec<Address>",
    error = "ContractError",
    mutable
)]
fn set_address_array<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<(), ContractError> {
    let value: Vec<Address> = ctx.parameter_cursor().get()?;
    host.state_mut().address_array = value;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "set_address_array_payable",
    parameter = "Vec<Address>",
    error = "ContractError",
    mutable,
    payable
)]
fn set_address_array_payable<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
    _amount: Amount,
) -> Result<(), ContractError> {
    let value: Vec<Address> = ctx.parameter_cursor().get()?;
    host.state_mut().address_array = value;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "get_address_array",
    return_value = "Vec<Address>",
    error = "ContractError",
    mutable
)]
fn get_address_array<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<Vec<Address>, ContractError> {
    Ok(host.state_mut().address_array.clone())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "set_object",
    parameter = "State",
    error = "ContractError",
    mutable
)]
fn set_object<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<(), ContractError> {
    let value: State = ctx.parameter_cursor().get()?;
    host.state_mut().account_address_value = value.account_address_value;
    host.state_mut().contract_address_value = value.contract_address_value;
    host.state_mut().address_value = value.address_value;
    host.state_mut().u8_value = value.u8_value;
    host.state_mut().u16_value = value.u16_value;
    host.state_mut().address_array= value.address_array;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "set_object_payable",
    parameter = "State",
    error = "ContractError",
    mutable,
    payable
)]
fn set_object_payable<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
    _amount: Amount,
) -> Result<(), ContractError> {
    let value: State = ctx.parameter_cursor().get()?;
    host.state_mut().account_address_value = value.account_address_value;
    host.state_mut().contract_address_value = value.contract_address_value;
    host.state_mut().address_value = value.address_value;
    host.state_mut().u8_value = value.u8_value;
    host.state_mut().u16_value = value.u16_value;
    host.state_mut().address_array= value.address_array;

    Ok(())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "get_object",
    return_value = "State",
    error = "ContractError",
    mutable
)]
fn get_object<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> Result<State, ContractError> {
    Ok(host.state().clone())
}

#[receive(
    contract = "smart_contract_test_bench",
    name = "view",
    parameter = "HashSha2256",
    error = "ContractError",
    return_value = "State"
)]
fn view<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<State, StateApiType = S>,
) -> ReceiveResult<State> {
    Ok(host.state().clone())
}
