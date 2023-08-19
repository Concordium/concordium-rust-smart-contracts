//! CIS2 client is the intermediatory layer between any contract and
//! CIS2 compliant contract.
//!
//! # Description
//! It allows the contract to abstract away the logic of calling the
//! CIS2 contract for the following methods
//! - `supports_cis2` : Calls [`supports`](https://proposals.concordium.software/CIS/cis-0.html#supports)
//! - `operator_of` : Calls [`operatorOf`](https://proposals.concordium.software/CIS/cis-2.html#operatorof)
//! - `balance_of` : Calls [`balanceOf`](https://proposals.concordium.software/CIS/cis-2.html#balanceof)
//! - `transfer` : Calls [`transfer`](https://proposals.concordium.software/CIS/cis-2.html#transfer)
//! - `update_operator` : Calls [`updateOperator`](https://proposals.concordium.software/CIS/cis-2.html#updateoperator)

use crate::*;
use concordium_std::*;

const SUPPORTS_ENTRYPOINT_NAME: EntrypointName = EntrypointName::new_unchecked("supports");
const OPERATOR_OF_ENTRYPOINT_NAME: EntrypointName = EntrypointName::new_unchecked("operatorOf");
const BALANCE_OF_ENTRYPOINT_NAME: EntrypointName = EntrypointName::new_unchecked("balanceOf");
const TRANSFER_ENTRYPOINT_NAME: EntrypointName = EntrypointName::new_unchecked("transfer");
const UPDATE_OPERATOR_ENTRYPOINT_NAME: EntrypointName =
    EntrypointName::new_unchecked("updateOperator");

pub type InvokeContractError<T> = CallContractError<Cis2Error<T>>;

/// Errors which can be returned by the `Cis2Client`.
#[derive(Debug)]
pub enum Cis2ClientError<T> {
    /// Invoking the contract returned the given error.
    InvokeContractError(InvokeContractError<T>),
    /// The response from the contract could not be parsed.
    ParseResult,
    /// The response was not as expected, for example the response is an empty
    /// vector for a single query.
    InvalidResponse,
}

impl<T: Serial> Serial for Cis2ClientError<T> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        match self {
            Cis2ClientError::InvokeContractError(e) => {
                out.write_u8(2)?;
                match e {
                    CallContractError::AmountTooLarge => out.write_u8(0),
                    CallContractError::MissingAccount => out.write_u8(1),
                    CallContractError::MissingContract => out.write_u8(2),
                    CallContractError::MissingEntrypoint => out.write_u8(3),
                    CallContractError::MessageFailed => out.write_u8(4),
                    CallContractError::LogicReject {
                        reason,
                        return_value,
                    } => {
                        out.write_u8(5)?;
                        reason.serial(out)?;
                        return_value.serial(out)?;
                        Ok(())
                    }
                    CallContractError::Trap => out.write_u8(6),
                }
            }
            Cis2ClientError::ParseResult => out.write_u8(0),
            Cis2ClientError::InvalidResponse => out.write_u8(1),
        }
    }
}

impl<T: Read, R: Deserial> TryFrom<CallContractError<T>> for Cis2ClientError<R> {
    type Error = Cis2ClientError<R>;

    fn try_from(err: CallContractError<T>) -> Result<Cis2ClientError<R>, Cis2ClientError<R>> {
        match err {
            CallContractError::AmountTooLarge => {
                Ok(Cis2ClientError::InvokeContractError(InvokeContractError::AmountTooLarge))
            }
            CallContractError::MissingAccount => {
                Ok(Cis2ClientError::InvokeContractError(InvokeContractError::MissingAccount))
            }
            CallContractError::MissingContract => {
                Ok(Cis2ClientError::InvokeContractError(InvokeContractError::MissingContract))
            }
            CallContractError::MissingEntrypoint => {
                Ok(Cis2ClientError::InvokeContractError(InvokeContractError::MissingEntrypoint))
            }
            CallContractError::MessageFailed => {
                Ok(Cis2ClientError::InvokeContractError(InvokeContractError::MessageFailed))
            }
            CallContractError::LogicReject {
                reason,
                mut return_value,
            } => Ok(Cis2ClientError::InvokeContractError(InvokeContractError::LogicReject {
                reason,
                return_value: Cis2Error::<R>::deserial(&mut return_value)?,
            })),
            CallContractError::Trap => {
                Ok(Cis2ClientError::InvokeContractError(InvokeContractError::Trap))
            }
        }
    }
}

impl<T> From<ParseError> for Cis2ClientError<T> {
    fn from(_: ParseError) -> Self { Cis2ClientError::ParseResult }
}

/// Client for interacting with CIS2 compliant contracts.
///
/// ## Examples
/// ```rust
/// use concordium_cis2::Cis2Client;
/// use concordium_std::ContractAddress;
/// let cis_contract_address = ContractAddress::new(0, 0);
/// Cis2Client::new(cis_contract_address);
/// ```
pub struct Cis2Client {
    contract: ContractAddress,
}

impl Cis2Client {
    pub fn new(contract: ContractAddress) -> Self {
        Self {
            contract,
        }
    }

    /// Calls the `supports` entrypoint of the CIS2 contract to check if the
    /// given contract supports CIS2 standard.
    /// If the contract supports CIS2 standard, it returns
    /// `Ok(SupportResult::Support)`, else it returns
    /// `Ok(SupportResult::NoSupport)`. If the contract supports CIS2
    /// standard by another contract, it returns
    /// `Ok(SupportResult::SupportBy(Vec<ContractAddress>))`. If there is an
    /// error, it returns `Err`.
    ///
    /// # Examples
    /// ```rust
    /// use concordium_cis2::*;
    /// use concordium_std::{test_infrastructure::*, *};
    /// let mut host = TestHost::new((), TestStateBuilder::new());
    /// host.setup_mock_entrypoint(
    ///     ContractAddress::new(0, 0),
    ///     OwnedEntrypointName::new_unchecked("supports".to_string()),
    ///     MockFn::new_v1(|_, _, _, _| {
    ///         Ok((false, SupportsQueryResponse {
    ///             results: vec![SupportResult::Support],
    ///         }))
    ///     }),
    /// );
    ///
    /// let client = Cis2Client::new(ContractAddress::new(0, 0));
    /// let res: Result<SupportResult, Cis2ClientError<()>> = client.supports_cis2(&host);
    /// assert!(res.is_ok());
    /// match res.unwrap() {
    ///     SupportResult::NoSupport => fail!(),
    ///     SupportResult::Support => (),
    ///     SupportResult::SupportBy(_) => fail!(),
    /// }
    /// ```
    pub fn supports_cis2<State, E: Deserial>(
        &self,
        host: &impl HasHost<State>,
    ) -> Result<SupportResult, Cis2ClientError<E>> {
        let params = SupportsQueryParams {
            queries: vec![CIS2_STANDARD_IDENTIFIER.to_owned()],
        };
        let mut res: SupportsQueryResponse =
            self.invoke_contract_read_only(host, SUPPORTS_ENTRYPOINT_NAME, &params)?;
        let res = res.results.pop().ok_or(Cis2ClientError::InvalidResponse)?;

        Ok(res)
    }

    /// Calls the `operatorOf` entrypoint of the CIS2 contract to check if the
    /// given owner is an operator of the given contract. If the owner is an
    /// operator of the given contract, it returns `Ok(true)`,
    /// else it returns `Ok(false)`.
    /// If there is an error, it returns `Err`.
    ///
    /// # Examples
    /// ```rust
    /// use concordium_cis2::*;
    /// use concordium_std::{test_infrastructure::*, *};
    ///
    /// let mut host = TestHost::new((), TestStateBuilder::new());
    /// host.setup_mock_entrypoint(
    ///     ContractAddress::new(0, 0),
    ///     OwnedEntrypointName::new_unchecked("operatorOf".to_string()),
    ///     MockFn::new_v1(|_, _, _, _| {
    ///         Ok((false, OperatorOfQueryResponse {
    ///             0: vec![true],
    ///         }))
    ///     }),
    /// );
    ///
    /// let client = Cis2Client::new(ContractAddress::new(0, 0));
    /// let res: Result<bool, Cis2ClientError<()>> = client.operator_of(
    ///     &mut host,
    ///     Address::Account(AccountAddress([1; 32])),
    ///     Address::Contract(ContractAddress::new(1, 0)),
    /// );
    ///
    /// assert_eq!(res.unwrap(), true);
    /// ```
    pub fn operator_of<State, E: Deserial>(
        &self,
        host: &impl HasHost<State>,
        owner: Address,
        address: Address,
    ) -> Result<bool, Cis2ClientError<E>> {
        let params = &OperatorOfQueryParams {
            queries: vec![OperatorOfQuery {
                owner,
                address,
            }],
        };
        let mut res: OperatorOfQueryResponse =
            self.invoke_contract_read_only(host, OPERATOR_OF_ENTRYPOINT_NAME, params)?;
        let res = res.0.pop().ok_or(Cis2ClientError::InvalidResponse)?;

        Ok(res)
    }

    /// Calls the `balanceOf` entrypoint of the CIS2 contract to get the balance
    /// of the given owner for the given token. If the balance is returned,
    /// it returns `Ok(balance)`, else it returns `Err`.
    /// # Examples
    /// ```rust
    /// use concordium_cis2::*;
    /// use concordium_std::{test_infrastructure::*, *};
    /// let mut host = TestHost::new((), TestStateBuilder::new());
    /// host.setup_mock_entrypoint(
    ///     ContractAddress::new(0, 0),
    ///     OwnedEntrypointName::new_unchecked("balanceOf".to_string()),
    ///     MockFn::new_v1(|_, _, _, _| {
    ///         Ok((false, BalanceOfQueryResponse::<TokenAmountU8>(vec![1.into()])))
    ///     }),
    /// );
    ///
    /// let client = Cis2Client::new(ContractAddress::new(0, 0));
    /// let res: Result<TokenAmountU8, Cis2ClientError<()>> =
    ///     client.balance_of(&host, TokenIdU8(1), Address::Account(AccountAddress([1; 32])));
    /// assert!(res.is_ok());
    /// assert_eq!(res.unwrap(), 1.into());
    /// ```
    pub fn balance_of<State, T: IsTokenId, A: IsTokenAmount, E: Deserial>(
        &self,
        host: &impl HasHost<State>,
        token_id: T,
        address: Address,
    ) -> Result<A, Cis2ClientError<E>> {
        let params = BalanceOfQueryParams {
            queries: vec![BalanceOfQuery {
                token_id,
                address,
            }],
        };

        let mut res: BalanceOfQueryResponse<A> =
            self.invoke_contract_read_only(host, BALANCE_OF_ENTRYPOINT_NAME, &params)?;
        let res = res.0.pop().ok_or(Cis2ClientError::InvalidResponse)?;

        Ok(res)
    }

    /// Calls the `transfer` entrypoint of the CIS2 contract to transfer the
    /// given amount of tokens from the given owner to the given receiver.
    /// If the transfer is successful and the state is modified, it returns
    /// `Ok(true)`, else it returns `Ok(false)`. If there is an error, it
    /// returns `Err`.
    ///
    /// # Examples
    /// ```rust
    /// use concordium_cis2::*;
    /// use concordium_std::{test_infrastructure::*, *};
    /// let mut host = TestHost::new((), TestStateBuilder::new());
    /// host.setup_mock_entrypoint(
    ///     ContractAddress::new(0, 0),
    ///     OwnedEntrypointName::new_unchecked("transfer".to_string()),
    ///     MockFn::new_v1(|_, _, _, _| Ok((false, ()))),
    /// );
    ///
    /// let client = Cis2Client::new(ContractAddress::new(0, 0));
    /// let res: Result<bool, Cis2ClientError<()>> = client.transfer(&mut host, Transfer {
    ///     amount:   TokenAmountU8(1),
    ///     from:     Address::Account(AccountAddress([1; 32])),
    ///     to:       Receiver::Account(AccountAddress([2; 32])),
    ///     token_id: TokenIdU8(1),
    ///     data:     AdditionalData::empty(),
    /// });
    ///
    /// assert!(res.is_ok());
    /// ```
    pub fn transfer<State, T: IsTokenId, A: IsTokenAmount, E: Deserial>(
        &self,
        host: &mut impl HasHost<State>,
        transfer: Transfer<T, A>,
    ) -> Result<bool, Cis2ClientError<E>> {
        let params = TransferParams(vec![transfer]);
        let (state_modified, _): (bool, Option<()>) =
            self.invoke_contract(host, TRANSFER_ENTRYPOINT_NAME, &params)?;

        Ok(state_modified)
    }

    /// Calls the `updateOperator` of the CIS2 contract.
    /// If the update is successful and the state is modified, it returns
    /// `Ok(true)`, else it returns `Ok(false)`. If there is an error, it
    /// returns `Err`.
    ///
    /// # Examples
    /// ```rust
    /// use concordium_cis2::*;
    /// use concordium_std::{test_infrastructure::*, *};
    /// let mut host = TestHost::new((), TestStateBuilder::new());
    /// host.setup_mock_entrypoint(
    ///     ContractAddress::new(0, 0),
    ///     OwnedEntrypointName::new_unchecked("updateOperator".to_string()),
    ///     MockFn::new_v1(|_, _, _, _| Ok((false, ()))),
    /// );
    ///
    /// let client = Cis2Client::new(ContractAddress::new(0, 0));
    /// let res: Result<bool, Cis2ClientError<()>> = client.update_operator(
    ///     &mut host,
    ///     Address::Account(AccountAddress([1; 32])),
    ///     OperatorUpdate::Add,
    /// );
    ///
    /// assert!(res.is_ok());
    /// ```
    pub fn update_operator<State, E: Deserial>(
        &self,
        host: &mut impl HasHost<State>,
        operator: Address,
        update: OperatorUpdate,
    ) -> Result<bool, Cis2ClientError<E>> {
        let params = UpdateOperator {
            operator,
            update,
        };
        let (state_modified, _): (bool, Option<()>) =
            self.invoke_contract(host, UPDATE_OPERATOR_ENTRYPOINT_NAME, &params)?;

        Ok(state_modified)
    }

    fn invoke_contract_read_only<State, P: Serial, R: Deserial, E: Deserial>(
        &self,
        host: &impl HasHost<State>,
        method: EntrypointName,
        parameter: &P,
    ) -> Result<R, Cis2ClientError<E>> {
        let res =
            host.invoke_contract_read_only(&self.contract, parameter, method, Amount::from_ccd(0));

        let res = match res {
            Ok(val) => val,
            Err(err) => return Err(Cis2ClientError::<E>::try_from(err)?),
        };

        let res = match res {
            // Since the contract should return a response. If it doesn't, it is an error.
            Some(mut res) => R::deserial(&mut res)?,
            None => bail!(Cis2ClientError::InvalidResponse),
        };

        Ok(res)
    }

    fn invoke_contract<State, P: Serial, R: Deserial, E: Deserial>(
        &self,
        host: &mut impl HasHost<State>,
        method: EntrypointName,
        parameter: &P,
    ) -> Result<(bool, Option<R>), Cis2ClientError<E>> {
        let res = host.invoke_contract(&self.contract, parameter, method, Amount::from_ccd(0));

        let res = match res {
            Ok(val) => {
                let o = match val.1 {
                    Some(mut res) => Some(R::deserial(&mut res)?),
                    None => None,
                };
                (val.0, o)
            }
            Err(err) => return Err(Cis2ClientError::<E>::try_from(err)?),
        };

        Ok(res)
    }
}

#[cfg(test)]
mod test {
    use crate::*;
    use concordium_std::test_infrastructure::*;

    const INDEX: u64 = 0;
    const SUBINDEX: u64 = 0;
    type ContractTokenId = TokenIdU8;
    type ContractTokenAmount = TokenAmountU8;

    #[test]
    fn supports_cis2_test() {
        let mut host = TestHost::new((), TestStateBuilder::new());
        fn mock_supports(
            parameter: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut (),
        ) -> Result<(bool, SupportsQueryResponse), CallContractError<SupportsQueryResponse>>
        {
            // Check that parameters are deserialized correctly.
            let mut cursor = Cursor::new(parameter);
            let params: Result<SupportsQueryParams, ParseError> =
                SupportsQueryParams::deserial(&mut cursor);
            assert!(params.is_ok());
            let params = params.unwrap();
            assert_eq!(
                params.queries[0],
                StandardIdentifierOwned::new_unchecked("CIS-2".to_owned())
            );

            // Return a response with support.
            Ok((false, SupportsQueryResponse {
                results: vec![SupportResult::Support],
            }))
        }

        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        host.setup_mock_entrypoint(
            cis_contract_address,
            OwnedEntrypointName::new_unchecked("supports".to_string()),
            MockFn::new_v1(mock_supports),
        );

        let client = Cis2Client::new(cis_contract_address);
        let res: Result<SupportResult, Cis2ClientError<()>> = client.supports_cis2(&host);
        assert!(res.is_ok());
        match res.unwrap() {
            SupportResult::NoSupport => fail!(),
            SupportResult::Support => (),
            SupportResult::SupportBy(_) => fail!(),
        }
    }

    #[test]
    fn supports_cis2_test_no_support() {
        let mut host = TestHost::new((), TestStateBuilder::new());
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        fn mock_supports(
            _p: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut (),
        ) -> Result<(bool, SupportsQueryResponse), CallContractError<SupportsQueryResponse>>
        {
            Ok((false, SupportsQueryResponse {
                results: vec![SupportResult::NoSupport],
            }))
        }

        host.setup_mock_entrypoint(
            cis_contract_address,
            OwnedEntrypointName::new_unchecked("supports".to_string()),
            MockFn::new_v1(mock_supports),
        );

        let client = Cis2Client::new(cis_contract_address);
        let res: Result<SupportResult, Cis2ClientError<()>> = client.supports_cis2(&host);
        assert!(res.is_ok());
        match res.unwrap() {
            SupportResult::NoSupport => (),
            SupportResult::Support => fail!(),
            SupportResult::SupportBy(_) => fail!(),
        }
    }

    #[test]
    fn supports_cis2_test_supported_by_other_contract() {
        let mut host = TestHost::new((), TestStateBuilder::new());
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        fn mock_supports(
            _p: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut (),
        ) -> Result<(bool, SupportsQueryResponse), CallContractError<SupportsQueryResponse>>
        {
            Ok((false, SupportsQueryResponse {
                results: vec![SupportResult::SupportBy(vec![ContractAddress::new(
                    INDEX,
                    SUBINDEX + 1,
                )])],
            }))
        }

        host.setup_mock_entrypoint(
            cis_contract_address,
            OwnedEntrypointName::new_unchecked("supports".to_string()),
            MockFn::new_v1(mock_supports),
        );

        let client = Cis2Client::new(cis_contract_address);
        let res: Result<SupportResult, Cis2ClientError<()>> = client.supports_cis2(&host);
        match res.unwrap() {
            SupportResult::NoSupport => fail!(),
            SupportResult::Support => fail!(),
            SupportResult::SupportBy(addresses) => {
                assert_eq!(addresses.first(), Some(&ContractAddress::new(INDEX, SUBINDEX + 1)))
            }
        }
    }

    #[test]
    fn operator_of_test() {
        let mut host = TestHost::new((), TestStateBuilder::new());
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        let owner = Address::Account(AccountAddress([1; 32]));
        let current_contract_address = Address::Contract(ContractAddress::new(INDEX + 1, SUBINDEX));
        fn mock_operator_of(
            parameter: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut (),
        ) -> Result<(bool, OperatorOfQueryResponse), CallContractError<OperatorOfQueryResponse>>
        {
            // Check that parameters are deserialized correctly.
            let mut cursor = Cursor::new(parameter);
            let params: Result<OperatorOfQueryParams, ParseError> =
                OperatorOfQueryParams::deserial(&mut cursor);
            match params {
                Ok(params) => {
                    assert_eq!(
                        params.queries[0].address,
                        Address::Contract(ContractAddress::new(INDEX + 1, SUBINDEX))
                    );
                    assert_eq!(params.queries[0].owner, Address::Account(AccountAddress([1; 32])));
                }
                Err(_) => fail!(),
            };

            // Return a response with operator true.
            Ok((false, OperatorOfQueryResponse {
                0: vec![true],
            }))
        }

        host.setup_mock_entrypoint(
            cis_contract_address,
            OwnedEntrypointName::new_unchecked("operatorOf".to_string()),
            MockFn::new_v1(mock_operator_of),
        );

        let client = Cis2Client::new(cis_contract_address);
        let res: Result<bool, Cis2ClientError<()>> =
            client.operator_of(&mut host, owner, current_contract_address);

        assert_eq!(res.unwrap(), true);
    }

    #[test]
    fn balance_of_test() {
        let mut host = TestHost::new((), TestStateBuilder::new());
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        let owner = Address::Account(AccountAddress([1; 32]));
        fn mock_balance_of(
            parameter: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut (),
        ) -> Result<
            (bool, BalanceOfQueryResponse<ContractTokenAmount>),
            CallContractError<BalanceOfQueryResponse<ContractTokenAmount>>,
        > {
            // Check that parameters are deserialized correctly.
            let mut cursor = Cursor::new(parameter);
            let params: Result<BalanceOfQueryParams<ContractTokenId>, ParseError> =
                BalanceOfQueryParams::deserial(&mut cursor);
            assert!(params.is_ok());
            let params = params.unwrap();
            assert_eq!(params.queries[0].token_id, TokenIdU8(1));
            assert_eq!(params.queries[0].address, Address::Account(AccountAddress([1; 32])));

            // Return a balance of 1.
            Ok((false, BalanceOfQueryResponse(vec![1.into()])))
        }

        host.setup_mock_entrypoint(
            cis_contract_address,
            OwnedEntrypointName::new_unchecked("balanceOf".to_string()),
            MockFn::new_v1(mock_balance_of),
        );

        let client = Cis2Client::new(cis_contract_address);
        let res: Result<TokenAmountU8, Cis2ClientError<()>> =
            client.balance_of(&host, TokenIdU8(1), owner);

        assert!(res.is_ok());
        let res: ContractTokenAmount = res.unwrap();
        assert_eq!(res, 1.into());
    }

    #[test]
    fn transfer_test() {
        let mut host = TestHost::new((), TestStateBuilder::new());
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        let from = Address::Account(AccountAddress([1; 32]));
        let to_account = AccountAddress([2; 32]);
        let amount: ContractTokenAmount = 1.into();

        fn mock_transfer(
            parameter: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut (),
        ) -> Result<(bool, ()), CallContractError<()>> {
            // Check that parameters are deserialized correctly.
            let mut cursor = Cursor::new(parameter);
            let params: Result<TransferParams<ContractTokenId, ContractTokenAmount>, ParseError> =
                TransferParams::deserial(&mut cursor);
            assert!(params.is_ok());
            let params = params.unwrap();
            assert_eq!(params.0[0].token_id, TokenIdU8(1));
            assert_eq!(params.0[0].to.address(), Address::Account(AccountAddress([2; 32])));
            assert_eq!(params.0[0].amount, 1.into());

            // Return a successful transfer.
            Ok((false, ()))
        }

        host.setup_mock_entrypoint(
            cis_contract_address,
            OwnedEntrypointName::new_unchecked("transfer".to_string()),
            MockFn::new_v1(mock_transfer),
        );

        let client = Cis2Client::new(cis_contract_address);
        let res: Result<bool, Cis2ClientError<()>> = client.transfer(&mut host, Transfer {
            amount,
            from,
            to: Receiver::Account(to_account),
            token_id: TokenIdU8(1),
            data: AdditionalData::empty(),
        });

        assert!(res.is_ok());
    }

    #[test]
    fn update_operator_test() {
        fn mock_update_operator(
            parameter: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut (),
        ) -> Result<(bool, ()), CallContractError<()>> {
            // Check that parameters are deserialized correctly.
            let mut cursor = Cursor::new(parameter);
            let params: Result<UpdateOperator, ParseError> = UpdateOperator::deserial(&mut cursor);
            assert!(params.is_ok());
            let params = params.unwrap();
            assert_eq!(params.operator, Address::Account(AccountAddress([1; 32])));
            match params.update {
                OperatorUpdate::Add => (),
                OperatorUpdate::Remove => fail!(),
            }

            // Return a successful update.
            Ok((false, ()))
        }
        let mut host = TestHost::new((), TestStateBuilder::new());
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        host.setup_mock_entrypoint(
            cis_contract_address,
            OwnedEntrypointName::new_unchecked("updateOperator".to_string()),
            MockFn::new_v1(mock_update_operator),
        );

        let client = Cis2Client::new(cis_contract_address);
        let res: Result<bool, Cis2ClientError<()>> = client.update_operator(
            &mut host,
            Address::Account(AccountAddress([1; 32])),
            OperatorUpdate::Add,
        );

        assert!(res.is_ok());
    }
}
