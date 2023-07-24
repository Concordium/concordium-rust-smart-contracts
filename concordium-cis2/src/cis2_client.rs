//! CIS2 client is the intermediatory layer between any contract and
//! CIS2 comliant contract.
//!
//! # Description
//! It allows the contract to abstract away the logic of calling the
//! CIS2 contract for the following methods
//! - `supports_cis2` : Calls [`supports`](https://proposals.concordium.software/CIS/cis-0.html#supports)
//! - `operator_of` : Calls [`operatorOf`](https://proposals.concordium.software/CIS/cis-2.html#operatorof)
//! - `balance_of` : Calls [`balanceOf`](https://proposals.concordium.software/CIS/cis-2.html#balanceof)
//! - `transfer` : Calls [`transfer`](https://proposals.concordium.software/CIS/cis-2.html#transfer)

use concordium_std::*;

use crate::*;

const SUPPORTS_ENTRYPOINT_NAME: EntrypointName = EntrypointName::new_unchecked("supports");
const OPERATOR_OF_ENTRYPOINT_NAME: EntrypointName = EntrypointName::new_unchecked("operatorOf");
const BALANCE_OF_ENTRYPOINT_NAME: EntrypointName = EntrypointName::new_unchecked("balanceOf");
const TRANSFER_ENTRYPOINT_NAME: EntrypointName = EntrypointName::new_unchecked("transfer");
const UPDATE_OPERATOR_ENTRYPOINT_NAME: EntrypointName =
    EntrypointName::new_unchecked("updateOperator");

/// Errors which can be returned by the `Cis2Client`.
#[derive(Debug)]
pub enum Cis2ClientError<T> {
    /// When there is an error invoking the CIS2 contract.
    InvokeContractError(CallContractError<T>),
    /// When there is an error parsing the result.
    ParseResult,
    InvalidResponse,
}

impl<T> From<CallContractError<T>> for Cis2ClientError<T> {
    fn from(err: CallContractError<T>) -> Self { Cis2ClientError::InvokeContractError(err) }
}

impl<T> From<ParseError> for Cis2ClientError<T> {
    fn from(_: ParseError) -> Self { Cis2ClientError::ParseResult }
}

/// `Cis2Client`
/// # Examples
/// ```rust
/// use concordium_cis2::cis2_client::Cis2Client;
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

    // calls the `supports` entrypoint of the CIS2 contract to check if the given
    // contract supports CIS2 standard. If the contract supports CIS2 standard,
    // it returns the contract address, else it returns None.
    pub fn supports_cis2<State, S: HasStateApi, E: Read>(
        &self,
        host: &impl HasHost<State, StateApiType = S, ReturnValueType = E>,
    ) -> Result<SupportResult, Cis2ClientError<E>> {
        let params = SupportsQueryParams {
            queries: vec![StandardIdentifierOwned::new_unchecked(
                CIS2_STANDARD_IDENTIFIER.id.to_owned(),
            )],
        };
        let mut res: SupportsQueryResponse =
            self.invoke_contract_read_only(host, SUPPORTS_ENTRYPOINT_NAME, &params)?;
        Cis2Client::first(&mut res.results)
    }

    // calls the `operatorOf` entrypoint of the CIS2 contract to check if the given
    // owner is an operator of the given contract. If the owner is an operator
    // of the given contract, it returns true, else it returns false.
    pub fn operator_of<State, S: HasStateApi, E: Read>(
        &self,
        host: &impl HasHost<State, StateApiType = S, ReturnValueType = E>,
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
            self.invoke_contract_read_only(host, OPERATOR_OF_ENTRYPOINT_NAME, &params)?;
        Cis2Client::first(&mut res.0)
    }

    // calls the `balanceOf` entrypoint of the CIS2 contract to get the balance of
    // the given owner for the given token. Returns the balance of the owner for
    // the given token.
    pub fn balance_of<State, S: HasStateApi, T: IsTokenId, A: IsTokenAmount, E: Read>(
        &self,
        host: &impl HasHost<State, StateApiType = S, ReturnValueType = E>,
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
        Cis2Client::first(&mut res.0)
    }

    // calls the `transfer` entrypoint of the CIS2 contract to transfer the given
    // amount of tokens from the given owner to the given receiver.
    // If the transfer is successful, it returns `Ok(())`, else it returns an `Err`.
    pub fn transfer<State, S: HasStateApi, T: IsTokenId, A: IsTokenAmount, E: Read>(
        &self,
        host: &mut impl HasHost<State, StateApiType = S, ReturnValueType = E>,
        transfer: Transfer<T, A>,
    ) -> Result<(), Cis2ClientError<E>> {
        let params = TransferParams(vec![transfer]);
        self.invoke_contract(host, TRANSFER_ENTRYPOINT_NAME, &params)?;

        Ok(())
    }

    // calls the `updateOperator` entrypoint of tge CIS2 contract.
    // If the update is successful, it returns `Ok(())`, else it returns an `Err`.
    pub fn update_operator<State, S: HasStateApi, E: Read>(
        &self,
        host: &mut impl HasHost<State, StateApiType = S, ReturnValueType = E>,
        operator: Address,
        update: OperatorUpdate,
    ) -> Result<(), Cis2ClientError<E>> {
        let params = UpdateOperator {
            operator,
            update,
        };
        self.invoke_contract(host, UPDATE_OPERATOR_ENTRYPOINT_NAME, &params)?;

        Ok(())
    }

    fn invoke_contract_read_only<State, S: HasStateApi, P: Serial, R: Deserial, E: Read>(
        &self,
        host: &impl HasHost<State, StateApiType = S, ReturnValueType = E>,
        method: EntrypointName,
        parameter: &P,
    ) -> Result<R, Cis2ClientError<E>> {
        let res = match host.invoke_contract_read_only(
            &self.contract,
            parameter,
            method,
            Amount::from_ccd(0),
        )? {
            // Since the contract should return a response. If it doesn't, it is an error.
            None => bail!(Cis2ClientError::InvalidResponse),
            Some(mut res) => R::deserial(&mut res)?,
        };

        Ok(res)
    }

    fn invoke_contract<State, S: HasStateApi, P: Serial, E: Read>(
        &self,
        host: &mut impl HasHost<State, StateApiType = S, ReturnValueType = E>,
        method: EntrypointName,
        parameter: &P,
    ) -> Result<(bool, Option<E>), Cis2ClientError<E>> {
        let res = host.invoke_contract(&self.contract, parameter, method, Amount::from_ccd(0))?;

        Ok(res)
    }

    fn first<T, E>(array: &mut Vec<T>) -> Result<T, Cis2ClientError<E>> {
        // If the contract returns a response, but the response is empty, it is an
        // error. Since for a single query the response should be non-empty.
        ensure!(array.is_empty(), Cis2ClientError::InvalidResponse);

        Ok(array.swap_remove(0))
    }
}

#[cfg(test)]
mod test {
    use concordium_std::{test_infrastructure::*, *};

    use crate::*;

    use super::Cis2Client;

    #[derive(Serial, Deserial, Clone)]
    pub struct TestState;

    const INDEX: u64 = 0;
    const SUBINDEX: u64 = 0;
    type ContractTokenId = TokenIdU8;
    type ContractTokenAmount = TokenAmountU8;

    #[test]
    fn supports_cis2_test_support() {
        let state = TestState {};
        let state_builder = TestStateBuilder::new();
        let mut host = TestHost::new(state, state_builder);
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        fn mock_supports(
            parameter: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut TestState,
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

        host.setup_mock_entrypoint(
            cis_contract_address,
            OwnedEntrypointName::new_unchecked("supports".to_string()),
            MockFn::new_v1(mock_supports),
        );

        let client = Cis2Client::new(cis_contract_address);
        let res = client.supports_cis2(&host);
        assert!(res.is_ok());
        match res.unwrap() {
            SupportResult::NoSupport => fail!(),
            SupportResult::Support => (),
            SupportResult::SupportBy(_) => fail!(),
        }
    }

    #[test]
    fn supports_cis2_test_no_support() {
        let state = TestState {};
        let state_builder = TestStateBuilder::new();
        let mut host = TestHost::new(state, state_builder);
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        fn mock_supports(
            _p: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut TestState,
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
        let res = client.supports_cis2(&host);
        match res.unwrap() {
            SupportResult::NoSupport => (),
            SupportResult::Support => fail!(),
            SupportResult::SupportBy(_) => fail!(),
        }
    }

    #[test]
    fn supports_cis2_test_supported_by_other_contract() {
        let state = TestState {};
        let state_builder = TestStateBuilder::new();
        let mut host = TestHost::new(state, state_builder);
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        fn mock_supports(
            _p: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut TestState,
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
        let res = client.supports_cis2(&host);
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
        let state = TestState {};
        let state_builder = TestStateBuilder::new();
        let mut host = TestHost::new(state, state_builder);
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        let owner = Address::Account(AccountAddress([1; 32]));
        let current_contract_address = Address::Contract(ContractAddress::new(INDEX + 1, SUBINDEX));
        fn mock_operator_of(
            parameter: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut TestState,
        ) -> Result<(bool, OperatorOfQueryResponse), CallContractError<OperatorOfQueryResponse>>
        {
            // Check that parameters are deserialized correctly.
            let mut cursor = Cursor::new(parameter);
            let params: Result<OperatorOfQueryParams, ParseError> =
                OperatorOfQueryParams::deserial(&mut cursor);
            assert!(params.is_ok());
            let params = params.unwrap();
            assert_eq!(
                params.queries[0].address,
                Address::Contract(ContractAddress::new(INDEX + 1, SUBINDEX))
            );
            assert_eq!(params.queries[0].owner, Address::Account(AccountAddress([1; 32])));

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
        let res = client.operator_of(&mut host, owner, current_contract_address);

        assert_eq!(res.unwrap(), true);
    }

    #[test]
    fn balance_of_test() {
        let state = TestState {};
        let state_builder = TestStateBuilder::new();
        let mut host = TestHost::new(state, state_builder);
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        let owner = Address::Account(AccountAddress([1; 32]));
        fn mock_balance_of(
            parameter: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut TestState,
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
        let res = client.balance_of(&host, TokenIdU8(1), owner);

        assert!(res.is_ok());
        let res: ContractTokenAmount = res.unwrap();
        assert_eq!(res, 1.into());
    }

    #[test]
    fn transfer_test() {
        let state = TestState {};
        let state_builder = TestStateBuilder::new();
        let mut host = TestHost::new(state, state_builder);
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        let from = Address::Account(AccountAddress([1; 32]));
        let to_account = AccountAddress([2; 32]);
        let amount: ContractTokenAmount = 1.into();

        fn mock_transfer(
            parameter: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut TestState,
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
        let res = client.transfer(&mut host, Transfer {
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
        let state = TestState {};
        let state_builder = TestStateBuilder::new();
        let mut host = TestHost::new(state, state_builder);
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        let operator = Address::Account(AccountAddress([1; 32]));
        let update = OperatorUpdate::Add;

        fn mock_update_operator(
            parameter: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut TestState,
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

        host.setup_mock_entrypoint(
            cis_contract_address,
            OwnedEntrypointName::new_unchecked("updateOperator".to_string()),
            MockFn::new_v1(mock_update_operator),
        );

        let client = Cis2Client::new(cis_contract_address);
        let res = client.update_operator(&mut host, operator, update);

        assert!(res.is_ok());
    }
}
