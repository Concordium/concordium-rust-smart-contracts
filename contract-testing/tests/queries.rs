//! This module contains tests related to the chain queries that are available
//! for smart contracts.
//!
//! Namely queries for:
//!  - the balance of a contract,
//!  - the balances of an account,
//!  - the exhange rates.
use concordium_smart_contract_testing::*;

const WASM_TEST_FOLDER: &str = "../../concordium-node/concordium-consensus/testdata/contracts/v1";
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
        chain.create_account(ACC_0, Account::new(initial_balance));
        chain.create_account(ACC_1, Account::new(initial_balance));

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
            chain.account_balance(ACC_0),
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
        chain.create_account(ACC_0, Account::new(initial_balance));
        chain.create_account(ACC_1, Account::new(initial_balance));

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
            chain.account_balance(ACC_0),
            Some(initial_balance - res_deploy.transaction_fee - res_init.transaction_fee)
        );
        assert_eq!(
            chain.account_balance(ACC_1),
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
        chain.create_account(ACC_0, Account::new(initial_balance));
        chain.create_account(ACC_1, Account::new(initial_balance));

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
            chain.account_balance(ACC_0),
            Some(
                initial_balance
                    - res_deploy.transaction_fee
                    - res_init.transaction_fee
                    - res_update.transaction_fee
                    - amount_to_send
            )
        );
        assert_eq!(
            chain.account_balance(ACC_1),
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
        chain.create_account(ACC_0, Account::new(initial_balance));
        chain.create_account(ACC_1, Account::new(initial_balance));

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
            chain.account_balance(ACC_0),
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
        chain.create_account(ACC_0, Account::new(initial_balance));

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
            chain.account_balance(ACC_0),
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
        chain.create_account(ACC_0, Account::new(initial_balance));

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
        chain.create_account(ACC_0, Account::new(initial_balance));

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
        chain.create_account(ACC_0, Account::new(initial_balance));

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
        chain.create_account(ACC_0, Account::new(initial_balance));

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
        chain.create_account(ACC_0, Account::new(initial_balance));

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
