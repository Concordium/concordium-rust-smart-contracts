//! # A universal proxy contract
//!
//! This contract acts as a universal proxy, which you can put in front of
//! another smart contract. The proxy can act as a "public" address for your
//! contract (the proxied) contract. This allows you to replace the proxied
//! contract, for example when bugs are fixed, without changing the "public"
//! address of the contract, i.e. the proxy's address.
//!
//! The proxy contract uses the fallback mechanism to forward any CCD and
//! parameters to the invoked entrypoint on the proxied contract.
//! If the proxied contract returns a value, this will also be returned by the
//! proxy.
//!
//! The proxy also has the entrypoint "________reconfigure", which enables the
//! owner of the proxy to change the proxied contract. The entrypoint name is
//! prefixed by underscores to avoid naming conflicts with the proxied contract.
//!
//! For testing purposes, the contract "world_appender" is included, which
//! appends ", world" to the parameter and returns it.
//!
//! The tests are located in `/tests/tests.rs`.
use concordium_std::*;

/// The contract behind this proxy.
type State = ContractAddress;

/// Needed for the custom serial instance, which doesn't include the `Option`
/// tag and the length of the vector.
#[derive(PartialEq, Eq, Debug)]
pub struct RawReturnValue(Option<Vec<u8>>);

impl Serial for RawReturnValue {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        match &self.0 {
            Some(rv) => out.write_all(rv),
            None => Ok(()),
        }
    }
}

/// Initialize the contract by specifying the contract to be proxied.
#[init(contract = "proxy", parameter = "ContractAddress")]
fn init(ctx: &InitContext, _state_builder: &mut StateBuilder) -> InitResult<State> {
    let proxied_contract = ctx.parameter_cursor().get()?;
    Ok(proxied_contract)
}

/// The fallback method, which redirects the invocations to the proxied
/// contract.
#[receive(contract = "proxy", fallback, mutable, payable)]
fn receive_fallback(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    amount: Amount,
) -> ReceiveResult<RawReturnValue> {
    let entrypoint = ctx.named_entrypoint();
    let proxied_contract = *host.state();
    let mut parameter_buffer = vec![0; ctx.parameter_cursor().size() as usize];
    ctx.parameter_cursor().read_exact(&mut parameter_buffer)?;

    let return_value = host
        .invoke_contract_raw(
            &proxied_contract,
            // The parameter size must be valid since this receive function has been executed.
            Parameter::new_unchecked(&parameter_buffer[..]),
            entrypoint.as_entrypoint_name(),
            amount,
        )?
        .1;

    match return_value {
        Some(mut rv) => {
            let mut rv_buffer = vec![0; rv.size() as usize];
            rv.read_exact(&mut rv_buffer)?;
            Ok(RawReturnValue(Some(rv_buffer)))
        }
        None => Ok(RawReturnValue(None)),
    }
}

/// Change the proxied address. Only the owner is allowed to do so.
/// The underscores in the name are to avoid naming conflicts with entrypoints
/// in the proxied contract.
#[receive(
    contract = "proxy",
    name = "________reconfigure",
    mutable,
    parameter = "ContractAddress"
)]
fn receive_reconfigure(ctx: &ReceiveContext, host: &mut Host<State>) -> ReceiveResult<()> {
    ensure!(ctx.sender().matches_account(&ctx.owner()));
    *host.state_mut() = ctx.parameter_cursor().get()?;
    Ok(())
}

//////////////////////////////////////////

// Initialize the world_appender contract.
#[init(contract = "world_appender", parameter = "String")]
fn init_world_appender(_ctx: &InitContext, _state_builder: &mut StateBuilder) -> InitResult<()> {
    Ok(())
}

// Append receive method, which appends `", world"` to the parameter and returns
// it.
#[receive(contract = "world_appender", name = "append", parameter = "String")]
fn world_appender_append(ctx: &ReceiveContext, _host: &Host<()>) -> ReceiveResult<String> {
    let mut parameter: String = ctx.parameter_cursor().get()?;
    parameter.push_str(", world");
    Ok(parameter)
}
