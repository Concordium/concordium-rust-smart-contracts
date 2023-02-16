mod constants;
mod impls;
mod invocation;
mod types;

pub use types::Chain;

#[cfg(test)]
mod tests {
    use crate::types::*;

    use super::*;

    const ACC_0: AccountAddress = AccountAddress([0; 32]);
    const ACC_1: AccountAddress = AccountAddress([1; 32]);
    const WASM_TEST_FOLDER: &str =
        "../../concordium-node/concordium-consensus/testdata/contracts/v1";

    #[test]
    fn creating_accounts_work() {
        let mut chain = Chain::new();
        chain.create_account(ACC_0, AccountInfo::new(Amount::from_ccd(1)));
        chain.create_account(ACC_1, AccountInfo::new(Amount::from_ccd(2)));

        assert_eq!(chain.accounts.len(), 2);
        assert_eq!(
            chain.persistence_account_balance(ACC_0),
            Some(Amount::from_ccd(1))
        );
        assert_eq!(
            chain.persistence_account_balance(ACC_1),
            Some(Amount::from_ccd(2))
        );
    }

    #[test]
    fn deploying_valid_module_works() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res = chain
            .module_deploy_v1(ACC_0, "examples/icecream/icecream.wasm.v1")
            .expect("Deploying valid module should work");

        assert_eq!(chain.modules.len(), 1);
        assert_eq!(
            chain.persistence_account_balance(ACC_0),
            Some(initial_balance - res.transaction_fee)
        );
    }

    #[test]
    fn initializing_valid_contract_works() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy_v1(ACC_0, "examples/icecream/icecream.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_weather"),
                OwnedParameter::from_bytes(vec![0u8]),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");
        assert_eq!(
            chain.persistence_account_balance(ACC_0),
            Some(initial_balance - res_deploy.transaction_fee - res_init.transaction_fee)
        );
        assert_eq!(chain.contracts.len(), 1);
    }

    #[test]
    fn initializing_with_invalid_parameter_fails() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy_v1(ACC_0, "examples/icecream/icecream.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_weather"),
                OwnedParameter::from_bytes(vec![99u8]), // Invalid param
                Amount::zero(),
                Energy::from(10000),
            )
            .expect_err("Initializing with invalid params should fail");

        assert!(matches!(res_init, ContractInitError::ValidChainError(_)));
        match res_init {
            // Failed in the right way and account is still charged.
            ContractInitError::ValidChainError(FailedContractInteraction::Reject {
                transaction_fee,
                ..
            }) => assert_eq!(
                chain.persistence_account_balance(ACC_0),
                Some(initial_balance - res_deploy.transaction_fee - transaction_fee)
            ),
            _ => panic!("Expected valid chain error."),
        };
    }

    #[test]
    fn updating_valid_contract_works() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy_v1(ACC_0, "examples/icecream/icecream.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_weather"),
                OwnedParameter::from_bytes(vec![0u8]), // Starts as 0
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");

        let res_update = chain
            .contract_update(
                ACC_0,
                Address::Account(ACC_0),
                res_init.contract_address,
                EntrypointName::new_unchecked("set"),
                OwnedParameter::from_bytes(vec![1u8]), // Updated to 1
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Updating valid contract should work");

        let res_invoke_get = chain
            .contract_invoke(
                ACC_0,
                Address::Contract(res_init.contract_address), // Invoke with a contract as sender.
                res_init.contract_address,
                EntrypointName::new_unchecked("get"),
                OwnedParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Invoking get should work");

        // This also asserts that the account wasn't charged for the invoke.
        assert_eq!(
            chain.persistence_account_balance(ACC_0),
            Some(
                initial_balance
                    - res_deploy.transaction_fee
                    - res_init.transaction_fee
                    - res_update.transaction_fee
            )
        );
        assert_eq!(chain.contracts.len(), 1);
        assert!(res_update.state_changed);
        // Assert that the updated state is persisted.
        assert_eq!(res_invoke_get.return_value, [1u8]);
    }

    /// Test that updates and invocations where the sender is missing fail.
    #[test]
    fn updating_and_invoking_with_missing_sender_fails() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let missing_account = Address::Account(ACC_1);
        let missing_contract = Address::Contract(ContractAddress::new(100, 0));

        let res_deploy = chain
            .module_deploy_v1(ACC_0, "examples/icecream/icecream.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_weather"),
                OwnedParameter::from_bytes(vec![0u8]), // Starts as 0
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");

        let res_update_acc = chain.contract_update(
            ACC_0,
            missing_account,
            res_init.contract_address,
            EntrypointName::new_unchecked("get"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        );

        let res_invoke_acc = chain.contract_invoke(
            ACC_0,
            missing_account,
            res_init.contract_address,
            EntrypointName::new_unchecked("get"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        );

        let res_update_contr = chain.contract_update(
            ACC_0,
            missing_contract,
            res_init.contract_address,
            EntrypointName::new_unchecked("get"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        );

        let res_invoke_contr = chain.contract_invoke(
            ACC_0,
            missing_contract,
            res_init.contract_address,
            EntrypointName::new_unchecked("get"),
            OwnedParameter::empty(),
            Amount::zero(),
            Energy::from(10000),
        );

        assert!(matches!(
            res_update_acc,
            Err(ContractUpdateError::SenderDoesNotExist(addr)) if addr == missing_account));
        assert!(matches!(
            res_invoke_acc,
            Err(ContractUpdateError::SenderDoesNotExist(addr)) if addr == missing_account));
        assert!(matches!(
            res_update_contr,
            Err(ContractUpdateError::SenderDoesNotExist(addr)) if addr == missing_contract));
        assert!(matches!(
            res_invoke_contr,
            Err(ContractUpdateError::SenderDoesNotExist(addr)) if addr == missing_contract));
    }

    /// Tests using the integrate contract defined in
    /// concordium-rust-smart-contract on the 'kb/sc-integration-testing'
    /// branch.
    mod integrate_contract {
        use super::*;

        #[test]
        fn update_with_account_transfer_works() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(10000);
            let transfer_amount = Amount::from_ccd(1);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));
            chain.create_account(ACC_1, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_v1(ACC_0, "examples/integrate/a.wasm.v1")
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_integrate"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("receive"),
                    OwnedParameter::new(&ACC_1),
                    transfer_amount,
                    Energy::from(10000),
                )
                .expect("Updating valid contract should work");

            let res_view = chain
                .contract_invoke(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("view"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Invoking get should work");

            // This also asserts that the account wasn't charged for the invoke.
            assert_eq!(
                chain.persistence_account_balance(ACC_0),
                Some(
                    initial_balance
                        - res_deploy.transaction_fee
                        - res_init.transaction_fee
                        - res_update.transaction_fee
                        - transfer_amount
                )
            );
            assert_eq!(
                chain.persistence_account_balance(ACC_1),
                Some(initial_balance + transfer_amount)
            );
            assert_eq!(res_update.transfers(), [Transfer {
                from:   res_init.contract_address,
                amount: transfer_amount,
                to:     ACC_1,
            }]);
            assert_eq!(chain.contracts.len(), 1);
            assert!(res_update.state_changed);
            assert_eq!(res_update.return_value, [2, 0, 0, 0]);
            // Assert that the updated state is persisted.
            assert_eq!(res_view.return_value, [2, 0, 0, 0]);
        }

        #[test]
        fn update_with_account_transfer_to_missing_account_fails() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(10000);
            let transfer_amount = Amount::from_ccd(1);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_v1(ACC_0, "examples/integrate/a.wasm.v1")
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_integrate"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain.contract_update(
                ACC_0,
                Address::Account(ACC_0),
                res_init.contract_address,
                EntrypointName::new_unchecked("receive"),
                OwnedParameter::new(&ACC_1), // We haven't created ACC_1.
                transfer_amount,
                Energy::from(100000),
            );

            match res_update {
                Err(ContractUpdateError::ExecutionError {
                    failure_kind: InvokeFailure::ContractReject { code, .. },
                    transaction_fee,
                    ..
                }) => {
                    assert_eq!(code, -3); // The custom contract error code for missing account.
                    assert_eq!(
                        chain.persistence_account_balance(ACC_0),
                        Some(
                            initial_balance
                                - res_deploy.transaction_fee
                                - res_init.transaction_fee
                                - transaction_fee
                        )
                    );
                }
                _ => panic!("Expected contract update to fail"),
            }
        }

        #[test]
        fn update_with_integrate_reentry_works() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(10000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_v1(ACC_0, "examples/integrate/a.wasm.v1")
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_integrate"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("recurse"),
                    OwnedParameter::new(&10u32),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect("Updating valid contract should work");

            let res_view = chain
                .contract_invoke(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("view"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Invoking get should work");

            // This also asserts that the account wasn't charged for the invoke.
            assert_eq!(
                chain.persistence_account_balance(ACC_0),
                Some(
                    initial_balance
                        - res_deploy.transaction_fee
                        - res_init.transaction_fee
                        - res_update.transaction_fee
                )
            );
            assert_eq!(chain.contracts.len(), 1);
            assert!(res_update.state_changed);
            let expected_res = 10 + 7 + 11 + 3 + 7 + 11;
            assert_eq!(res_update.return_value, u32::to_le_bytes(expected_res));
            // Assert that the updated state is persisted.
            assert_eq!(res_view.return_value, u32::to_le_bytes(expected_res));
        }

        #[test]
        fn update_with_rollback_and_reentry_works() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_v1(ACC_0, "examples/integrate/a.wasm.v1")
                .expect("Deploying valid module should work");

            let input_param: u32 = 8;

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_integrate"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("inc-fail-on-zero"),
                    OwnedParameter::new(&input_param),
                    Amount::zero(),
                    Energy::from(100000000),
                )
                .expect("Updating valid contract should work");

            let res_view = chain
                .contract_invoke(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("view"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Invoking get should work");

            assert_eq!(
                chain.persistence_account_balance(ACC_0),
                Some(
                    initial_balance
                        - res_deploy.transaction_fee
                        - res_init.transaction_fee
                        - res_update.transaction_fee
                )
            );
            assert!(res_update.state_changed);
            let expected_res = 2u32.pow(input_param) - 1;
            assert_eq!(res_update.return_value, u32::to_le_bytes(expected_res));
            // Assert that the updated state is persisted.
            assert_eq!(res_view.return_value, u32::to_le_bytes(expected_res));
        }

        #[test]
        fn rollback_of_account_balances_after_failed_contract_invoke() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(10000);
            let transfer_amount = Amount::from_ccd(2);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));
            chain.create_account(ACC_1, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_v1(ACC_0, "examples/integrate/a.wasm.v1")
                .expect("Deploying valid module should work");

            let res_init_0 = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_integrate"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_init_1 = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_integrate_other"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let param = (res_init_1.contract_address, initial_balance, ACC_1);

            chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init_0.contract_address,
                    EntrypointName::new_unchecked("mutate_and_forward"),
                    OwnedParameter::new(&param),
                    transfer_amount,
                    Energy::from(100000),
                )
                .expect("Update should succeed");
        }
    }
    // TODO: Add tests that check:
    // - Correct account balances after init / update failures (when Amount > 0)

    #[test]
    fn update_with_fib_reentry_works() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(1000000);
        chain.create_account(ACC_0, AccountInfo::new(initial_balance));

        let res_deploy = chain
            .module_deploy_v1(ACC_0, "examples/fib/a.wasm.v1")
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                ACC_0,
                res_deploy.module_reference,
                ContractName::new_unchecked("init_fib"),
                OwnedParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Initializing valid contract should work");

        let res_update = chain
            .contract_update(
                ACC_0,
                Address::Account(ACC_0),
                res_init.contract_address,
                EntrypointName::new_unchecked("receive"),
                OwnedParameter::new(&6u64),
                Amount::zero(),
                Energy::from(4000000),
            )
            .expect("Updating valid contract should work");

        let res_view = chain
            .contract_invoke(
                ACC_0,
                Address::Account(ACC_0),
                res_init.contract_address,
                EntrypointName::new_unchecked("view"),
                OwnedParameter::empty(),
                Amount::zero(),
                Energy::from(10000),
            )
            .expect("Invoking get should work");

        // This also asserts that the account wasn't charged for the invoke.
        assert_eq!(
            chain.persistence_account_balance(ACC_0),
            Some(
                initial_balance
                    - res_deploy.transaction_fee
                    - res_init.transaction_fee
                    - res_update.transaction_fee
            )
        );
        assert_eq!(chain.contracts.len(), 1);
        assert!(res_update.state_changed);
        let expected_res = u64::to_le_bytes(13);
        assert_eq!(res_update.return_value, expected_res);
        // Assert that the updated state is persisted.
        assert_eq!(res_view.return_value, expected_res);
    }

    mod query_account_balance {
        use super::*;

        /// Queries the balance of another account and asserts that it is as
        /// expected.
        #[test]
        fn test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));
            chain.create_account(ACC_1, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/queries-account-balance.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            // TODO: Implement serial for four-tuples in contracts-common. Nesting tuples to
            // get around it here.
            // The contract will query the balance of ACC_1 and assert that the three
            // balances match this input.
            let input_param = (ACC_1, (initial_balance, Amount::zero(), Amount::zero()));

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert_eq!(
                chain.persistence_account_balance(ACC_0),
                Some(
                    initial_balance
                        - res_deploy.transaction_fee
                        - res_init.transaction_fee
                        - res_update.transaction_fee
                )
            );
            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }

        /// Queries the balance of the invoker account, which will have have the
        /// expected balance of:
        /// prior_balance - amount_sent - amount_to_cover_reserved_NRG.
        #[test]
        fn invoker_test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));
            chain.create_account(ACC_1, AccountInfo::new(initial_balance));

            let res_deploy = chain
            .module_deploy_wasm_v1(ACC_0, format!("{}/queries-account-balance.wasm", WASM_TEST_FOLDER)) // TODO: Add wasm files to the repo for tests.
            .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let update_amount = Amount::from_ccd(123);
            let energy_limit = Energy::from(100000);
            let invoker_reserved_amount = update_amount + chain.calculate_energy_cost(energy_limit);

            // The contract will query the balance of ACC_1, which is also the invoker, and
            // assert that the three balances match this input.
            let expected_balance = initial_balance - invoker_reserved_amount;
            let input_param = (ACC_1, (expected_balance, Amount::zero(), Amount::zero()));

            let res_update = chain
                .contract_update(
                    ACC_1,
                    Address::Account(ACC_1),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
                    update_amount,
                    energy_limit,
                )
                .expect("Updating valid contract should work");

            assert_eq!(
                chain.persistence_account_balance(ACC_0),
                Some(initial_balance - res_deploy.transaction_fee - res_init.transaction_fee)
            );
            assert_eq!(
                chain.persistence_account_balance(ACC_1),
                // Differs from `expected_balance` as it only includes the actual amount charged
                // for the NRG use. Not the reserved amount.
                Some(initial_balance - res_update.transaction_fee - update_amount)
            );
            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }

        /// Makes a transfer to an account, then queries its balance and asserts
        /// that it is as expected.
        #[test]
        fn transfer_test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));
            chain.create_account(ACC_1, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/queries-account-balance-transfer.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let amount_to_send = Amount::from_ccd(123);

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    amount_to_send, // Make sure the contract has CCD to transfer.
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let amount_to_send = Amount::from_ccd(123);
            let expected_balance = initial_balance + amount_to_send;
            let input_param = (
                ACC_1,
                amount_to_send,
                (expected_balance, Amount::zero(), Amount::zero()),
            );

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Updating valid contract should work");

            assert_eq!(
                chain.persistence_account_balance(ACC_0),
                Some(
                    initial_balance
                        - res_deploy.transaction_fee
                        - res_init.transaction_fee
                        - res_update.transaction_fee
                        - amount_to_send
                )
            );
            assert_eq!(
                chain.persistence_account_balance(ACC_1),
                Some(initial_balance + amount_to_send)
            );
            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Interrupted { .. },
                ChainEvent::Transferred { .. },
                ChainEvent::Resumed { .. },
                ChainEvent::Updated { .. }
            ]));
        }

        #[test]
        fn balance_test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));
            chain.create_account(ACC_1, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/queries-account-balance.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            // TODO: Implement serial for four-tuples in contracts-common. Nesting tuples to
            // get around it here.
            // The contract will query the balance of ACC_1 and assert that the three
            // balances match this input.
            let input_param = (ACC_1, (initial_balance, Amount::zero(), Amount::zero()));

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert_eq!(
                chain.persistence_account_balance(ACC_0),
                Some(
                    initial_balance
                        - res_deploy.transaction_fee
                        - res_init.transaction_fee
                        - res_update.transaction_fee
                )
            );
            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }

        /// Queries the balance of a missing account and asserts that it returns
        /// the correct error.
        #[test]
        fn missing_account_test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!(
                        "{}/queries-account-balance-missing-account.wasm",
                        WASM_TEST_FOLDER
                    ),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            // The account to query, which doesn't exist in this test case.
            let input_param = ACC_1;

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert_eq!(
                chain.persistence_account_balance(ACC_0),
                Some(
                    initial_balance
                        - res_deploy.transaction_fee
                        - res_init.transaction_fee
                        - res_update.transaction_fee
                )
            );
            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }
    }

    mod query_contract_balance {
        use super::*;

        /// Test querying the balance of another contract, which exists. Asserts
        /// that the balance is as expected.
        #[test]
        fn test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let init_amount = Amount::from_ccd(123);

            let res_deploy = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/queries-contract-balance.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_init_other = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    init_amount, // Set up another contract with `init_amount` balance
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            // check that the other contract has `self_balance == init_amount`.
            let input_param = (res_init_other.contract_address, init_amount);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }

        /// Test querying the balance of the contract instance itself. This
        /// should include the amount sent to it in the update transaction.
        #[test]
        fn query_self_test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let init_amount = Amount::from_ccd(123);
            let update_amount = Amount::from_ccd(456);

            let res_deploy = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/queries-contract-balance.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    init_amount,
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            // check that the other contract has `self_balance == init_amount`.
            let input_param = (res_init.contract_address, init_amount + update_amount);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
                    update_amount,
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }

        /// Test querying the balance after a transfer of CCD.
        #[test]
        fn query_self_after_transfer_test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let init_amount = Amount::from_ccd(123);
            let update_amount = Amount::from_ccd(456);
            let transfer_amount = Amount::from_ccd(78);

            let res_deploy = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!(
                        "{}/queries-contract-balance-transfer.wasm",
                        WASM_TEST_FOLDER
                    ),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    init_amount,
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let input_param = (
                ACC_0,
                transfer_amount,
                (
                    res_init.contract_address,
                    init_amount + update_amount - transfer_amount,
                ),
            );

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
                    update_amount,
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Interrupted { .. },
                ChainEvent::Transferred { .. },
                ChainEvent::Resumed { .. },
                ChainEvent::Updated { .. }
            ]));
        }

        /// Test querying the balance of a contract that doesn't exist.
        #[test]
        fn missing_contract_test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!(
                        "{}/queries-contract-balance-missing-contract.wasm",
                        WASM_TEST_FOLDER
                    ),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            // Non-existent contract address.
            let input_param = ContractAddress::new(123, 456);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }
    }

    mod query_exchange_rates {

        use super::*;

        /// Test querying the exchange rates.
        #[test]
        fn test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/queries-exchange-rates.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            // Non-existent contract address.
            let input_param = (chain.euro_per_energy, chain.micro_ccd_per_euro);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("query"),
                    OwnedParameter::new(&input_param),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }
    }

    mod contract_upgrade {

        use super::*;

        /// Test a basic upgrade, ensuring that the new module is in place by
        /// checking the available entrypoints.
        #[test]
        fn test() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            // Deploy the two modules `upgrading_0`, `upgrading_1`
            let res_deploy_0 = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/upgrading_0.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_deploy_1 = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/upgrading_1.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            // Initialize `upgrading_0`.
            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy_0.module_reference,
                    ContractName::new_unchecked("init_a"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            // Upgrade the contract to the `upgrading_1` module by calling the `bump`
            // entrypoint.
            let res_update_upgrade = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("bump"),
                    OwnedParameter::new(&res_deploy_1.module_reference),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            // Call the `newfun` entrypoint which only exists in `upgrading_1`.
            let res_update_new = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("newfun"),
                    OwnedParameter::new(&res_deploy_1.module_reference),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating the `newfun` from the `upgrading_1` module should work");

            assert!(matches!(res_update_upgrade.chain_events[..], [
                ChainEvent::Interrupted { .. },
                ChainEvent::Upgraded { from, to, .. },
                ChainEvent::Resumed { .. },
                ChainEvent::Updated { .. },
            ] if from == res_deploy_0.module_reference && to == res_deploy_1.module_reference));
            assert!(matches!(res_update_new.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }

        /// The contract in this test, triggers an upgrade and then in the same
        /// invocation, calls a function in the upgraded module.
        /// Checking the new module is being used.
        #[test]
        fn test_self_invoke() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy_0 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-self-invoke0.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");
            let res_deploy_1 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-self-invoke1.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy_0.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    OwnedParameter::new(&res_deploy_1.module_reference),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                // Invoking `contract.name`
                ChainEvent::Interrupted { .. },
                ChainEvent::Updated { .. },
                ChainEvent::Resumed { .. },
                // Making the upgrade
                ChainEvent::Interrupted { .. },
                ChainEvent::Upgraded { .. },
                ChainEvent::Resumed { .. },
                // Invoking contract.name again
                ChainEvent::Interrupted { .. },
                ChainEvent::Updated { .. },
                ChainEvent::Resumed { .. },
                // The successful update
                ChainEvent::Updated { .. },
            ]));
        }

        /// Test upgrading to a module that doesn't exist (it uses module
        /// `[0u8;32]` inside the contract). The contract checks whether
        /// the expected error is returned.
        #[test]
        fn test_missing_module() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-missing-module.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Interrupted { .. },
                // No upgrade event, as it is supposed to fail.
                ChainEvent::Resumed { success, .. },
                ChainEvent::Updated { .. },
            ] if success == false));
        }

        /// Test upgrading to a module where there isn't a matching contract
        /// name. The contract checks whether the expected error is
        /// returned.
        #[test]
        fn test_missing_contract() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy_0 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-missing-contract0.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_deploy_1 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-missing-contract1.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy_0.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    OwnedParameter::new(&res_deploy_1.module_reference),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                ChainEvent::Interrupted { .. },
                // No upgrade event, as it is supposed to fail.
                ChainEvent::Resumed { success, .. },
                ChainEvent::Updated { .. },
            ] if success == false));
        }

        /// Test upgrading twice in the same transaction. The effect of the
        /// second upgrade should be in effect at the end.
        #[test]
        fn test_twice_in_one_transaction() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy_0 = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/upgrading-twice0.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_deploy_1 = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/upgrading-twice1.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_deploy_2 = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/upgrading-twice2.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy_0.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let input_param = (res_deploy_1.module_reference, res_deploy_2.module_reference);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    OwnedParameter::new(&input_param),
                    Amount::zero(),
                    Energy::from(100000),
                )
                .expect("Updating valid contract should work");

            assert!(matches!(res_update.chain_events[..], [
                // Invoke the contract itself to check the name entrypoint return value.
                ChainEvent::Interrupted { .. },
                ChainEvent::Updated { .. },
                ChainEvent::Resumed { .. },
                // Upgrade from module 0 to 1
                ChainEvent::Interrupted { .. },
                ChainEvent::Upgraded { from: first_from, to: first_to, .. },
                ChainEvent::Resumed { .. },
                // Invoke the contract itself to check the name again.
                ChainEvent::Interrupted { .. },
                ChainEvent::Updated { .. },
                ChainEvent::Resumed { .. },
                // Upgrade again
                ChainEvent::Interrupted { .. },
                ChainEvent::Upgraded { from: second_from, to: second_to, .. },
                ChainEvent::Resumed { .. },
                // Invoke itself again to check name a final time.
                ChainEvent::Interrupted { .. },
                ChainEvent::Updated { .. },
                ChainEvent::Resumed { .. },
                // Final update event
                ChainEvent::Updated { .. },
            ] if first_from == res_deploy_0.module_reference
                && first_to == res_deploy_1.module_reference
                && second_from == res_deploy_1.module_reference
                && second_to == res_deploy_2.module_reference));
        }

        /// Test upgrading to a module where there isn't a matching contract
        /// name. The contract checks whether the expected error is
        /// returned.
        #[test]
        fn test_chained_contract() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-chained0.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let number_of_upgrades: u32 = 82; // TODO: Stack will overflow if larger than 82.
            let input_param = (number_of_upgrades, res_deploy.module_reference);

            let res_update = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    OwnedParameter::new(&input_param),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect("Updating valid contract should work");

            // Per upgrade: 3 events for invoking itself + 3 events for the upgrade.
            // Ends with 4 extra events: 3 events for an upgrade and 1 event for succesful
            // update.
            assert_eq!(
                res_update.chain_events.len() as u32,
                6 * number_of_upgrades + 4
            )
        }

        /// Tests whether a contract which triggers a succesful upgrade,
        /// but rejects the transaction from another cause, rollbacks the
        /// upgrade as well.
        #[test]
        fn test_reject() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy_0 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-reject0.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_deploy_1 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-reject1.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy_0.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update_upgrade = chain.contract_update(
                ACC_0,
                Address::Account(ACC_0),
                res_init.contract_address,
                EntrypointName::new_unchecked("upgrade"),
                OwnedParameter::new(&res_deploy_1.module_reference),
                Amount::zero(),
                Energy::from(1000000),
            );

            let res_update_new_feature = chain.contract_update(
                ACC_0,
                Address::Account(ACC_0),
                res_init.contract_address,
                EntrypointName::new_unchecked("new_feature"),
                OwnedParameter::empty(),
                Amount::zero(),
                Energy::from(1000000),
            );

            // Check the return value manually returned by the contract.
            match res_update_upgrade {
                Err(ContractUpdateError::ExecutionError { failure_kind, .. }) => match failure_kind
                {
                    InvokeFailure::ContractReject { code, .. } if code == -1 => (),
                    _ => panic!("Expected ContractReject with code == -1"),
                },
                _ => panic!("Expected Err(ContractUpdateError::ExecutionError)"),
            }

            // Assert that the new_feature entrypoint doesn't exist since the upgrade
            // failed.
            assert!(matches!(
                res_update_new_feature,
                Err(ContractUpdateError::ExecutionError {
                    failure_kind:    InvokeFailure::NonExistentEntrypoint,
                    energy_used:     _,
                    transaction_fee: _,
                })
            ));
        }

        /// Tests calling an entrypoint introduced by an upgrade of the module
        /// can be called and whether an entrypoint removed by an upgrade fail
        /// with the appropriate reject reason.
        #[test]
        fn test_changing_entrypoint() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(1000000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy_0 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-changing-entrypoints0.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_deploy_1 = chain
                .module_deploy_wasm_v1(
                    ACC_0,
                    format!("{}/upgrading-changing-entrypoints1.wasm", WASM_TEST_FOLDER),
                )
                .expect("Deploying valid module should work");

            let res_init = chain
                .contract_init(
                    ACC_0,
                    res_deploy_0.module_reference,
                    ContractName::new_unchecked("init_contract"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_update_old_feature_0 = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("old_feature"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect("Updating old_feature on old module should work.");

            let res_update_new_feature_0 = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("new_feature"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect_err("Updating new_feature on old module should _not_ work");

            let res_update_upgrade = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("upgrade"),
                    OwnedParameter::new(&res_deploy_1.module_reference),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect("Upgrading contract should work.");

            let res_update_old_feature_1 = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("old_feature"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect_err("Updating old_feature on _new_ module should _not_ work.");

            let res_update_new_feature_1 = chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init.contract_address,
                    EntrypointName::new_unchecked("new_feature"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(1000000),
                )
                .expect("Updating new_feature on _new_ module should work");

            assert!(matches!(res_update_old_feature_0.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
            assert!(matches!(
                res_update_new_feature_0,
                ContractUpdateError::ExecutionError {
                    failure_kind:    InvokeFailure::NonExistentEntrypoint,
                    energy_used:     _,
                    transaction_fee: _,
                }
            ));
            assert!(matches!(res_update_upgrade.chain_events[..], [
                ChainEvent::Interrupted { .. },
                ChainEvent::Upgraded { .. },
                ChainEvent::Resumed { .. },
                ChainEvent::Updated { .. },
            ]));
            assert!(matches!(
                res_update_old_feature_1,
                ContractUpdateError::ExecutionError {
                    failure_kind:    InvokeFailure::NonExistentEntrypoint,
                    energy_used:     _,
                    transaction_fee: _,
                }
            ));
            assert!(matches!(res_update_new_feature_1.chain_events[..], [
                ChainEvent::Updated { .. }
            ]));
        }
    }

    /// Tests related to checkpoints and rollbacks of the contract state.
    mod checkpointing {
        use super::*;

        /// This test has the following call pattern:
        /// A
        ///  -->  B
        ///         --> A
        ///         <--
        ///       B(trap)
        /// A <--
        /// The state at A should be left unchanged by the changes of the
        /// 'inner' invocation on contract A. A correctly perceives B's
        /// trapping signal. Only V1 contracts are being used.
        #[test]
        fn test_case_1() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(10000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/checkpointing.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_init_a = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_a"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_init_b = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_b"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let forward_parameter = (
                res_init_a.contract_address,
                0u16, // length of empty parameter
                (EntrypointName::new_unchecked("a_modify"), Amount::zero()),
            );
            let forward_parameter_len = to_bytes(&forward_parameter).len();
            let parameter = (
                (
                    res_init_b.contract_address,
                    forward_parameter_len as u16,
                    forward_parameter,
                ),
                EntrypointName::new_unchecked("b_forward_crash"),
                Amount::zero(),
            );

            chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init_a.contract_address,
                    EntrypointName::new_unchecked("a_modify_proxy"),
                    OwnedParameter::new(&parameter),
                    // We supply one microCCD as we expect a trap
                    // (see contract for details).
                    Amount::from_micro_ccd(1),
                    Energy::from(10000),
                )
                .expect("Updating contract should succeed");
        }

        /// This test has the following call pattern:
        /// A
        ///   -->  B
        ///          --> A (no modification, just lookup entry)
        ///          <--
        ///        B
        /// A <--
        ///
        /// The state at A should be left unchanged.
        /// The iterator initialized at the outer A should point to the same
        /// entry as before the call. That is, the iterator should not
        /// be affected by the inner iterator. Only V1 contracts are
        /// being used.
        #[test]
        fn test_case_2() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(10000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/checkpointing.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_init_a = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_a"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_init_b = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_b"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let forward_parameter = (
                res_init_a.contract_address,
                0u16, // length of empty parameter
                (EntrypointName::new_unchecked("a_no_modify"), Amount::zero()),
            );
            let forward_parameter_len = to_bytes(&forward_parameter).len();
            let parameter = (
                (
                    res_init_b.contract_address,
                    forward_parameter_len as u16,
                    forward_parameter,
                ),
                EntrypointName::new_unchecked("b_forward"),
                Amount::zero(),
            );

            chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init_a.contract_address,
                    EntrypointName::new_unchecked("a_modify_proxy"),
                    OwnedParameter::new(&parameter),
                    // We supply zero microCCD as we're instructing the contract to not expect
                    // state modifications. Also, the contract does not expect
                    // errors, i.e., a trap signal from underlying invocations.
                    // The 'inner' call to contract A does not modify the state.
                    // See the contract for details.
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Updating contract should succeed");
        }

        /// This test has the following call pattern:
        /// A
        ///   -->  Transfer
        /// A <--
        ///
        /// The state at A should be left unchanged.
        /// The iterator initialized at A should after the call point to the
        /// same entry as before the call. Only V1 contracts are being
        /// used.
        #[test]
        fn test_case_3() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(10000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));
            chain.create_account(ACC_1, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/checkpointing.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_init_a = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_a"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_b"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init_a.contract_address,
                    EntrypointName::new_unchecked("a_modify_proxy"),
                    OwnedParameter::new(&ACC_1),
                    // We supply three micro CCDs as we're instructing the contract to carry out a
                    // transfer instead of a call. See the contract for
                    // details.
                    Amount::from_micro_ccd(3),
                    Energy::from(10000),
                )
                .expect("Updating contract should succeed");
        }

        /// This test has the following call pattern:
        /// A
        ///   -->  B
        ///          --> A modify
        ///          <--
        ///        B
        /// A <--
        ///
        /// The state at A should have changed according to the 'inner'
        /// invocation on contract A. Only V1 contracts are being used.
        #[test]
        fn test_case_4() {
            let mut chain = Chain::new();
            let initial_balance = Amount::from_ccd(10000);
            chain.create_account(ACC_0, AccountInfo::new(initial_balance));

            let res_deploy = chain
                .module_deploy_wasm_v1(ACC_0, format!("{}/checkpointing.wasm", WASM_TEST_FOLDER))
                .expect("Deploying valid module should work");

            let res_init_a = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_a"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let res_init_b = chain
                .contract_init(
                    ACC_0,
                    res_deploy.module_reference,
                    ContractName::new_unchecked("init_b"),
                    OwnedParameter::empty(),
                    Amount::zero(),
                    Energy::from(10000),
                )
                .expect("Initializing valid contract should work");

            let forward_parameter = (
                res_init_a.contract_address,
                0u16, // length of empty parameter
                (EntrypointName::new_unchecked("a_modify"), Amount::zero()),
            );
            let forward_parameter_len = to_bytes(&forward_parameter).len();
            let parameter = (
                (
                    res_init_b.contract_address,
                    forward_parameter_len as u16,
                    forward_parameter,
                ),
                EntrypointName::new_unchecked("b_forward"),
                Amount::zero(),
            );

            chain
                .contract_update(
                    ACC_0,
                    Address::Account(ACC_0),
                    res_init_a.contract_address,
                    EntrypointName::new_unchecked("a_modify_proxy"),
                    OwnedParameter::new(&parameter),
                    // We supply four CCDs as we're instructing the contract to expect state
                    // modifications being made from the 'inner' contract A
                    // call to be in effect when returned to the caller (a.a_modify_proxy).
                    // See the contract for details.
                    Amount::from_micro_ccd(4),
                    Energy::from(10000),
                )
                .expect("Updating contract should succeed");
        }
    }

    mod amount_delta {
        use super::*;

        #[test]
        fn test() {
            let mut x = AmountDelta::new();
            assert_eq!(x, AmountDelta::Positive(Amount::zero()));

            let one = Amount::from_ccd(1);
            let two = Amount::from_ccd(2);
            let three = Amount::from_ccd(3);
            let five = Amount::from_ccd(5);

            x = x.subtract_amount(one); // -1 CCD
            x = x.subtract_amount(one); // -2 CCD
            assert_eq!(x, AmountDelta::Negative(two));
            x = x.add_amount(five); // +3 CCD
            assert_eq!(x, AmountDelta::Positive(three));
            x = x.subtract_amount(five); // -2 CCD
            assert_eq!(x, AmountDelta::Negative(two));
            x = x.add_amount(two); // 0

            x = x.add_amount(Amount::from_micro_ccd(1)); // 1 mCCD
            assert_eq!(x, AmountDelta::Positive(Amount::from_micro_ccd(1)));
            x = x.subtract_amount(Amount::from_micro_ccd(2)); // -1 mCCD
            assert_eq!(x, AmountDelta::Negative(Amount::from_micro_ccd(1)));
        }
    }
}
