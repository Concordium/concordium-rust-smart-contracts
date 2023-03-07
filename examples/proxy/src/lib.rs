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
use concordium_std::*;

/// The contract behind this proxy.
type State = ContractAddress;

/// Needed for the custom serial instance, which doesn't include the `Option`
/// tag and the length of the vector.
#[derive(PartialEq, Eq, Debug)]
struct RawReturnValue(Option<Vec<u8>>);

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
fn init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    _state_builder: &mut StateBuilder<S>,
) -> InitResult<State> {
    let proxied_contract = ctx.parameter_cursor().get()?;
    Ok(proxied_contract)
}

/// The fallback method, which redirects the invocations to the proxied
/// contract.
#[receive(contract = "proxy", fallback, mutable, payable)]
fn receive_fallback<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
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
#[receive(contract = "proxy", name = "________reconfigure", mutable, parameter = "ContractAddress")]
fn receive_reconfigure<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State, StateApiType = S>,
) -> ReceiveResult<()> {
    ensure!(ctx.sender().matches_account(&ctx.owner()));
    *host.state_mut() = ctx.parameter_cursor().get()?;
    Ok(())
}

#[concordium_cfg_test]
mod tests {
    use super::*;
    use concordium_std::test_infrastructure::*;

    #[concordium_test]
    fn proxy_forwards_and_returns_data_unaltered() {
        // Arrange
        let proxied_contract = ContractAddress {
            index:    0,
            subindex: 0,
        };
        let proxied_entrypoint = OwnedEntrypointName::new_unchecked("some_entrypoint".into());
        let mut ctx = TestReceiveContext::empty();
        ctx.set_named_entrypoint(proxied_entrypoint.clone());
        ctx.set_parameter(b"hello");

        let mut host = TestHost::new(proxied_contract, TestStateBuilder::new());
        host.setup_mock_entrypoint(
            proxied_contract,
            proxied_entrypoint,
            MockFn::new_v1(|parameter, _, &mut _, &mut _| {
                let mut rv = Into::<&[u8]>::into(parameter).to_vec();
                rv.extend_from_slice(b", world!");
                Ok((false, RawReturnValue(Some(rv))))
            }),
        );

        // Act
        let result = receive_fallback(&ctx, &mut host, Amount::zero());

        // Assert
        claim_eq!(result, Ok(RawReturnValue(Some(b"hello, world!".to_vec()))))
    }
}
