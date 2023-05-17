//! This module contains tests related to the chain queries that are available
//! for smart contracts.
//!
//! Namely queries for:
//!  - the balance of a contract,
//!  - the balances of an account,
//!  - the exhange rates.
use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../concordium-base/smart-contracts/testdata/contracts/v1";
const ACC_0: AccountAddress = AccountAddress([0; 32]);
const ACC_1: AccountAddress = AccountAddress([1; 32]);

mod query_account_balance {
    use super::*;

    /// Queries the balance of another account and asserts that it is as
    /// expected.
    #[test]
    fn test() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(1000000);
        chain.create_account(Account::new(ACC_0, initial_balance));
        chain.create_account(Account::new(ACC_1, initial_balance));

        let res_deploy = chain
            .module_deploy_v1(
                Signer::with_one_key(),
                ACC_0,
                module_load_v1_raw(format!("{}/queries-account-balance.wasm", WASM_TEST_FOLDER))
                    .expect("module should exist"),
            )
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                Signer::with_one_key(),
                ACC_0,
                Energy::from(10000),
                InitContractPayload {
                    mod_ref:   res_deploy.module_reference,
                    init_name: OwnedContractName::new_unchecked("init_contract".into()),
                    param:     OwnedParameter::empty(),
                    amount:    Amount::zero(),
                },
            )
            .expect("Initializing valid contract should work");

        // The contract will query the balance of ACC_1 and assert that the three
        // balances match this input.
        let input_param = (ACC_1, initial_balance, Amount::zero(), Amount::zero());

        let res_update = chain
            .contract_update(
                Signer::with_one_key(),
                ACC_0,
                Address::Account(ACC_0),
                Energy::from(100000),
                UpdateContractPayload {
                    address:      res_init.contract_address,
                    receive_name: OwnedReceiveName::new_unchecked("contract.query".into()),
                    message:      OwnedParameter::from_serial(&input_param)
                        .expect("Parameter has valid size"),
                    amount:       Amount::zero(),
                },
            )
            .expect("Updating valid contract should work");

        assert_eq!(
            chain.account_balance_available(ACC_0),
            Some(
                initial_balance
                    - res_deploy.transaction_fee
                    - res_init.transaction_fee
                    - res_update.transaction_fee
            )
        );
        assert!(matches!(
            res_update.effective_trace_elements_cloned()[..],
            [ContractTraceElement::Updated { .. }]
        ));
    }

    /// Queries the balance of the invoker account, which will have have the
    /// expected balance of:
    /// prior_balance - amount_sent - amount_to_cover_reserved_NRG.
    #[test]
    fn invoker_test() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(1000000);
        chain.create_account(Account::new(ACC_0, initial_balance));
        chain.create_account(Account::new(ACC_1, initial_balance));

        let res_deploy = chain
            .module_deploy_v1(
                Signer::with_one_key(),
                ACC_0,
                module_load_v1_raw(format!("{}/queries-account-balance.wasm", WASM_TEST_FOLDER))
                    .expect("module should exist"),
            )
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                Signer::with_one_key(),
                ACC_0,
                Energy::from(10000),
                InitContractPayload {
                    mod_ref:   res_deploy.module_reference,
                    init_name: OwnedContractName::new_unchecked("init_contract".into()),
                    param:     OwnedParameter::empty(),
                    amount:    Amount::zero(),
                },
            )
            .expect("Initializing valid contract should work");

        let update_amount = Amount::from_ccd(123);
        let energy_limit = Energy::from(100000);
        let invoker_reserved_amount = update_amount + chain.calculate_energy_cost(energy_limit);

        // The contract will query the balance of ACC_1, which is also the invoker, and
        // assert that the three balances match this input.
        let expected_balance = initial_balance - invoker_reserved_amount;
        let input_param = (ACC_1, expected_balance, Amount::zero(), Amount::zero());

        let res_update = chain
            .contract_update(
                Signer::with_one_key(),
                ACC_1,
                Address::Account(ACC_1),
                energy_limit,
                UpdateContractPayload {
                    address:      res_init.contract_address,
                    receive_name: OwnedReceiveName::new_unchecked("contract.query".into()),
                    message:      OwnedParameter::from_serial(&input_param)
                        .expect("Parameter has valid size"),
                    amount:       update_amount,
                },
            )
            .expect("Updating valid contract should work");

        assert_eq!(
            chain.account_balance_available(ACC_0),
            Some(initial_balance - res_deploy.transaction_fee - res_init.transaction_fee)
        );
        assert_eq!(
            chain.account_balance_available(ACC_1),
            // Differs from `expected_balance` as it only includes the actual amount charged
            // for the NRG use. Not the reserved amount.
            Some(initial_balance - res_update.transaction_fee - update_amount)
        );
        assert!(matches!(
            res_update.effective_trace_elements_cloned()[..],
            [ContractTraceElement::Updated { .. }]
        ));
    }

    /// Makes a transfer to an account, then queries its balance and asserts
    /// that it is as expected.
    #[test]
    fn transfer_test() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(1000000);
        chain.create_account(Account::new(ACC_0, initial_balance));
        chain.create_account(Account::new(ACC_1, initial_balance));

        let res_deploy = chain
            .module_deploy_v1(
                Signer::with_one_key(),
                ACC_0,
                module_load_v1_raw(format!(
                    "{}/queries-account-balance-transfer.wasm",
                    WASM_TEST_FOLDER
                ))
                .expect("module should exist"),
            )
            .expect("Deploying valid module should work");

        let amount_to_send = Amount::from_ccd(123);

        let res_init = chain
            .contract_init(
                Signer::with_one_key(),
                ACC_0,
                Energy::from(10000),
                InitContractPayload {
                    mod_ref:   res_deploy.module_reference,
                    init_name: OwnedContractName::new_unchecked("init_contract".into()),
                    param:     OwnedParameter::empty(),
                    amount:    amount_to_send, // Make sure the contract has CCD to transfer.
                },
            )
            .expect("Initializing valid contract should work");

        let amount_to_send = Amount::from_ccd(123);
        let expected_balance = initial_balance + amount_to_send;
        let input_param = (
            ACC_1,
            amount_to_send,
            expected_balance,
            Amount::zero(),
            Amount::zero(),
        );

        let res_update = chain
            .contract_update(
                Signer::with_one_key(),
                ACC_0,
                Address::Account(ACC_0),
                Energy::from(10000),
                UpdateContractPayload {
                    address:      res_init.contract_address,
                    receive_name: OwnedReceiveName::new_unchecked("contract.query".into()),
                    message:      OwnedParameter::from_serial(&input_param)
                        .expect("Parameter has valid size"),
                    amount:       Amount::zero(),
                },
            )
            .expect("Updating valid contract should work");

        assert_eq!(
            chain.account_balance_available(ACC_0),
            Some(
                initial_balance
                    - res_deploy.transaction_fee
                    - res_init.transaction_fee
                    - res_update.transaction_fee
                    - amount_to_send
            )
        );
        assert_eq!(
            chain.account_balance_available(ACC_1),
            Some(initial_balance + amount_to_send)
        );
        assert!(matches!(
            res_update.effective_trace_elements_cloned()[..],
            [
                ContractTraceElement::Interrupted { .. },
                ContractTraceElement::Transferred { .. },
                ContractTraceElement::Resumed { .. },
                ContractTraceElement::Updated { .. }
            ]
        ));
    }

    #[test]
    fn balance_test() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(1000000);
        chain.create_account(Account::new(ACC_0, initial_balance));
        chain.create_account(Account::new(ACC_1, initial_balance));

        let res_deploy = chain
            .module_deploy_v1(
                Signer::with_one_key(),
                ACC_0,
                module_load_v1_raw(format!("{}/queries-account-balance.wasm", WASM_TEST_FOLDER))
                    .expect("module should exist"),
            )
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                Signer::with_one_key(),
                ACC_0,
                Energy::from(10000),
                InitContractPayload {
                    mod_ref:   res_deploy.module_reference,
                    init_name: OwnedContractName::new_unchecked("init_contract".into()),
                    param:     OwnedParameter::empty(),
                    amount:    Amount::zero(),
                },
            )
            .expect("Initializing valid contract should work");

        // The contract will query the balance of ACC_1 and assert that the three
        // balances match this input.
        let input_param = (ACC_1, initial_balance, Amount::zero(), Amount::zero());

        let res_update = chain
            .contract_update(
                Signer::with_one_key(),
                ACC_0,
                Address::Account(ACC_0),
                Energy::from(100000),
                UpdateContractPayload {
                    address:      res_init.contract_address,
                    receive_name: OwnedReceiveName::new_unchecked("contract.query".into()),
                    message:      OwnedParameter::from_serial(&input_param)
                        .expect("Parameter has valid size"),
                    amount:       Amount::zero(),
                },
            )
            .expect("Updating valid contract should work");

        assert_eq!(
            chain.account_balance_available(ACC_0),
            Some(
                initial_balance
                    - res_deploy.transaction_fee
                    - res_init.transaction_fee
                    - res_update.transaction_fee
            )
        );
        assert!(matches!(
            res_update.effective_trace_elements_cloned()[..],
            [ContractTraceElement::Updated { .. }]
        ));
    }

    /// Queries the balance of a missing account and asserts that it returns
    /// the correct error.
    #[test]
    fn missing_account_test() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(1000000);
        chain.create_account(Account::new(ACC_0, initial_balance));

        let res_deploy = chain
            .module_deploy_v1(
                Signer::with_one_key(),
                ACC_0,
                module_load_v1_raw(format!(
                    "{}/queries-account-balance-missing-account.wasm",
                    WASM_TEST_FOLDER
                ))
                .expect("module should exist"),
            )
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                Signer::with_one_key(),
                ACC_0,
                Energy::from(10000),
                InitContractPayload {
                    mod_ref:   res_deploy.module_reference,
                    init_name: OwnedContractName::new_unchecked("init_contract".into()),
                    param:     OwnedParameter::empty(),
                    amount:    Amount::zero(),
                },
            )
            .expect("Initializing valid contract should work");

        // The account to query, which doesn't exist in this test case.
        let input_param = ACC_1;

        let res_update = chain
            .contract_update(
                Signer::with_one_key(),
                ACC_0,
                Address::Account(ACC_0),
                Energy::from(100000),
                UpdateContractPayload {
                    address:      res_init.contract_address,
                    receive_name: OwnedReceiveName::new_unchecked("contract.query".into()),
                    message:      OwnedParameter::from_serial(&input_param)
                        .expect("Parameter has valid size"),
                    amount:       Amount::zero(),
                },
            )
            .expect("Updating valid contract should work");

        assert_eq!(
            chain.account_balance_available(ACC_0),
            Some(
                initial_balance
                    - res_deploy.transaction_fee
                    - res_init.transaction_fee
                    - res_update.transaction_fee
            )
        );
        assert!(matches!(
            res_update.effective_trace_elements_cloned()[..],
            [ContractTraceElement::Updated { .. }]
        ));
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
        chain.create_account(Account::new(ACC_0, initial_balance));

        let init_amount = Amount::from_ccd(123);

        let res_deploy = chain
            .module_deploy_v1(
                Signer::with_one_key(),
                ACC_0,
                module_load_v1_raw(format!(
                    "{}/queries-contract-balance.wasm",
                    WASM_TEST_FOLDER
                ))
                .expect("module should exist"),
            )
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                Signer::with_one_key(),
                ACC_0,
                Energy::from(10000),
                InitContractPayload {
                    mod_ref:   res_deploy.module_reference,
                    init_name: OwnedContractName::new_unchecked("init_contract".into()),
                    param:     OwnedParameter::empty(),
                    amount:    Amount::zero(),
                },
            )
            .expect("Initializing valid contract should work");

        let res_init_other = chain
            .contract_init(
                Signer::with_one_key(),
                ACC_0,
                Energy::from(10000),
                InitContractPayload {
                    mod_ref:   res_deploy.module_reference,
                    init_name: OwnedContractName::new_unchecked("init_contract".into()),
                    param:     OwnedParameter::empty(),
                    amount:    init_amount, // Set up another contract with `init_amount` balance
                },
            )
            .expect("Initializing valid contract should work");

        // check that the other contract has `self_balance == init_amount`.
        let input_param = (res_init_other.contract_address, init_amount);

        let res_update = chain
            .contract_update(
                Signer::with_one_key(),
                ACC_0,
                Address::Account(ACC_0),
                Energy::from(100000),
                UpdateContractPayload {
                    address:      res_init.contract_address,
                    receive_name: OwnedReceiveName::new_unchecked("contract.query".into()),
                    message:      OwnedParameter::from_serial(&input_param)
                        .expect("Parameter has valid size"),
                    amount:       Amount::zero(),
                },
            )
            .expect("Updating valid contract should work");

        assert!(matches!(
            res_update.effective_trace_elements_cloned()[..],
            [ContractTraceElement::Updated { .. }]
        ));
    }

    /// Test querying the balance of the contract instance itself. This
    /// should include the amount sent to it in the update transaction.
    #[test]
    fn query_self_test() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(1000000);
        chain.create_account(Account::new(ACC_0, initial_balance));

        let init_amount = Amount::from_ccd(123);
        let update_amount = Amount::from_ccd(456);

        let res_deploy = chain
            .module_deploy_v1(
                Signer::with_one_key(),
                ACC_0,
                module_load_v1_raw(format!(
                    "{}/queries-contract-balance.wasm",
                    WASM_TEST_FOLDER
                ))
                .expect("module should exist"),
            )
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                Signer::with_one_key(),
                ACC_0,
                Energy::from(10000),
                InitContractPayload {
                    mod_ref:   res_deploy.module_reference,
                    init_name: OwnedContractName::new_unchecked("init_contract".into()),
                    param:     OwnedParameter::empty(),
                    amount:    init_amount,
                },
            )
            .expect("Initializing valid contract should work");

        // check that the other contract has `self_balance == init_amount`.
        let input_param = (res_init.contract_address, init_amount + update_amount);

        let res_update = chain
            .contract_update(
                Signer::with_one_key(),
                ACC_0,
                Address::Account(ACC_0),
                Energy::from(100000),
                UpdateContractPayload {
                    address:      res_init.contract_address,
                    receive_name: OwnedReceiveName::new_unchecked("contract.query".into()),
                    message:      OwnedParameter::from_serial(&input_param)
                        .expect("Parameter has valid size"),
                    amount:       update_amount,
                },
            )
            .expect("Updating valid contract should work");

        assert!(matches!(
            res_update.effective_trace_elements_cloned()[..],
            [ContractTraceElement::Updated { .. }]
        ));
    }

    /// Test querying the balance after a transfer of CCD.
    #[test]
    fn query_self_after_transfer_test() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(1000000);
        chain.create_account(Account::new(ACC_0, initial_balance));

        let init_amount = Amount::from_ccd(123);
        let update_amount = Amount::from_ccd(456);
        let transfer_amount = Amount::from_ccd(78);

        let res_deploy = chain
            .module_deploy_v1(
                Signer::with_one_key(),
                ACC_0,
                module_load_v1_raw(format!(
                    "{}/queries-contract-balance-transfer.wasm",
                    WASM_TEST_FOLDER
                ))
                .expect("module should exist"),
            )
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                Signer::with_one_key(),
                ACC_0,
                Energy::from(10000),
                InitContractPayload {
                    mod_ref:   res_deploy.module_reference,
                    init_name: OwnedContractName::new_unchecked("init_contract".into()),
                    param:     OwnedParameter::empty(),
                    amount:    init_amount,
                },
            )
            .expect("Initializing valid contract should work");

        let input_param = (
            ACC_0,
            transfer_amount,
            res_init.contract_address,
            init_amount + update_amount - transfer_amount,
        );

        let res_update = chain
            .contract_update(
                Signer::with_one_key(),
                ACC_0,
                Address::Account(ACC_0),
                Energy::from(100000),
                UpdateContractPayload {
                    address:      res_init.contract_address,
                    receive_name: OwnedReceiveName::new_unchecked("contract.query".into()),
                    message:      OwnedParameter::from_serial(&input_param)
                        .expect("Parameter has valid size"),
                    amount:       update_amount,
                },
            )
            .expect("Updating valid contract should work");

        assert!(matches!(
            res_update.effective_trace_elements_cloned()[..],
            [
                ContractTraceElement::Interrupted { .. },
                ContractTraceElement::Transferred { .. },
                ContractTraceElement::Resumed { .. },
                ContractTraceElement::Updated { .. }
            ]
        ));
    }

    /// Test querying the balance of a contract that doesn't exist.
    #[test]
    fn missing_contract_test() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(1000000);
        chain.create_account(Account::new(ACC_0, initial_balance));

        let res_deploy = chain
            .module_deploy_v1(
                Signer::with_one_key(),
                ACC_0,
                module_load_v1_raw(format!(
                    "{}/queries-contract-balance-missing-contract.wasm",
                    WASM_TEST_FOLDER
                ))
                .expect("module should exist"),
            )
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                Signer::with_one_key(),
                ACC_0,
                Energy::from(10000),
                InitContractPayload {
                    mod_ref:   res_deploy.module_reference,
                    init_name: OwnedContractName::new_unchecked("init_contract".into()),
                    param:     OwnedParameter::empty(),
                    amount:    Amount::zero(),
                },
            )
            .expect("Initializing valid contract should work");

        // Non-existent contract address.
        let input_param = ContractAddress::new(123, 456);

        let res_update = chain
            .contract_update(
                Signer::with_one_key(),
                ACC_0,
                Address::Account(ACC_0),
                Energy::from(100000),
                UpdateContractPayload {
                    address:      res_init.contract_address,
                    receive_name: OwnedReceiveName::new_unchecked("contract.query".into()),
                    message:      OwnedParameter::from_serial(&input_param)
                        .expect("Parameter has valid size"),
                    amount:       Amount::zero(),
                },
            )
            .expect("Updating valid contract should work");

        assert!(matches!(
            res_update.effective_trace_elements_cloned()[..],
            [ContractTraceElement::Updated { .. }]
        ));
    }
}

mod query_exchange_rates {

    use super::*;

    /// Test querying the exchange rates.
    #[test]
    fn test() {
        let mut chain = Chain::new();
        let initial_balance = Amount::from_ccd(1000000);
        chain.create_account(Account::new(ACC_0, initial_balance));

        let res_deploy = chain
            .module_deploy_v1(
                Signer::with_one_key(),
                ACC_0,
                module_load_v1_raw(format!("{}/queries-exchange-rates.wasm", WASM_TEST_FOLDER))
                    .expect("module should exist"),
            )
            .expect("Deploying valid module should work");

        let res_init = chain
            .contract_init(
                Signer::with_one_key(),
                ACC_0,
                Energy::from(10000),
                InitContractPayload {
                    mod_ref:   res_deploy.module_reference,
                    init_name: OwnedContractName::new_unchecked("init_contract".into()),
                    param:     OwnedParameter::empty(),
                    amount:    Amount::zero(),
                },
            )
            .expect("Initializing valid contract should work");

        // Non-existent contract address.
        let input_param = (chain.euro_per_energy(), chain.micro_ccd_per_euro());

        let res_update = chain
            .contract_update(
                Signer::with_one_key(),
                ACC_0,
                Address::Account(ACC_0),
                Energy::from(100000),
                UpdateContractPayload {
                    address:      res_init.contract_address,
                    receive_name: OwnedReceiveName::new_unchecked("contract.query".into()),
                    message:      OwnedParameter::from_serial(&input_param)
                        .expect("Parameter has valid size"),
                    amount:       Amount::zero(),
                },
            )
            .expect("Updating valid contract should work");

        assert!(matches!(
            res_update.effective_trace_elements_cloned()[..],
            [ContractTraceElement::Updated { .. }]
        ));
    }
}
