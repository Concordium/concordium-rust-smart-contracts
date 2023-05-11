use concordium_smart_contract_testing::*;
use concordium_std::Deserial;
use smart_contract_upgrade::UpgradeParams;

const ACC_ADDR_OWNER: AccountAddress = AccountAddress([0u8; 32]);
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(1000);

#[derive(Deserial, Debug, PartialEq, Eq)]
pub struct State {
    admin:     AccountAddress,
    old_state: String,
    new_state: String,
}

fn setup_chain_and_contract() -> (Chain, ContractInitSuccess) {
    let mut chain = Chain::new();

    chain.create_account(Account::new(ACC_ADDR_OWNER, ACC_INITIAL_BALANCE));

    // Deploy 'contract_version1' module (built with [Cargo Concordium](https://developer.concordium.software/en/mainnet/smart-contracts/guides/setup-tools.html#cargo-concordium)).
    let deployment = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_ADDR_OWNER,
            module_load_v1("./smart_contract_upgrade.wasm.v1")
                .expect("`Contract version1` module should be loaded"),
        )
        .expect("`Contract version1` deployment should always succeed");

    let initialization = chain
        .contract_init(
            Signer::with_one_key(),
            ACC_ADDR_OWNER,
            Energy::from(10000),
            InitContractPayload {
                amount:    Amount::zero(),
                mod_ref:   deployment.module_reference,
                init_name: OwnedContractName::new_unchecked(
                    "init_smart_contract_upgrade".to_string(),
                ),
                param:     OwnedParameter::empty(),
            },
        )
        .expect("Initialization of `Contract version1` should always succeed");

    (chain, initialization)
}

#[test]
fn test_init() {
    let (chain, initialization) = setup_chain_and_contract();
    assert_eq!(
        chain.contract_balance(initialization.contract_address),
        Some(Amount::zero()),
        "Contract should have no funds"
    );
}

#[test]
fn test_upgrade_without_migration_function() {
    let (mut chain, initialization) = setup_chain_and_contract();

    // Deploy 'contract_version2' module (built with [Cargo Concordium](https://developer.concordium.software/en/mainnet/smart-contracts/guides/setup-tools.html#cargo-concordium)).
    let deployment = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_ADDR_OWNER,
            module_load_v1("../contract-version2/smart_contract_upgrade.wasm.v1")
                .expect("`Contract version2` module should be loaded"),
        )
        .expect("`Contract version2` deployment should always succeed");

    let input_parameter = UpgradeParams {
        module:  deployment.module_reference,
        migrate: None,
    };

    // Upgrade `contract_version1` to `contract_version2`.
    let update = chain.contract_update(
        Signer::with_one_key(), // Used for specifying the number of signatures.
        ACC_ADDR_OWNER,         // Invoker account.
        Address::Account(ACC_ADDR_OWNER), // Sender (can also be a contract).
        Energy::from(10000),    // Maximum energy allowed for the update.
        UpdateContractPayload {
            address: initialization.contract_address, // The contract to update.
            receive_name: OwnedReceiveName::new_unchecked("smart_contract_upgrade.upgrade".into()), // The receive function to call.
            message: OwnedParameter::from_serial(&input_parameter)
                .expect("`UpgradeParams` should be a valid inut parameter"), // The parameter sent to the contract.
            amount: Amount::from_ccd(0), // Sending the contract 0 CCD.
        },
    );

    assert_eq!(
        update.expect("Upgrade should succeed").state_changed,
        false,
        "State should not be changed because no `migration` function was called"
    );

    let invoke = chain
        .contract_invoke(
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_upgrade.view".to_string(),
                ),
                message:      OwnedParameter::empty(),
            },
        )
        .expect("Invoking `view` should always succeed");

    let state: State =
        from_bytes(&invoke.return_value).expect("View should always return a valid result");

    assert_eq!(state, State {
        admin:     ACC_ADDR_OWNER,
        old_state: "This state should NOT be migrated as part of the smart contract upgrade."
            .to_string(),
        new_state: "This state should be migrated as part of the smart contract upgrade."
            .to_string(),
    });
}

#[test]
fn test_upgrade_with_migration_function() {
    let (mut chain, initialization) = setup_chain_and_contract();

    // Deploy 'contract_version2' module (built with [Cargo Concordium](https://developer.concordium.software/en/mainnet/smart-contracts/guides/setup-tools.html#cargo-concordium)).
    let deployment = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ACC_ADDR_OWNER,
            module_load_v1("../contract-version2/smart_contract_upgrade.wasm.v1")
                .expect("UpgradeParams should be a valid inut parameter"),
        )
        .expect("`Contract version2` deployment should always succeed");

    let input_parameter = UpgradeParams {
        module:  deployment.module_reference,
        migrate: Some((
            OwnedEntrypointName::new("migration".to_string())
                .expect("`migration` should be a valid name"),
            OwnedParameter::empty(),
        )),
    };

    // Upgrade `contract_version1` to `contract_version2`.
    let update = chain.contract_update(
        Signer::with_one_key(), // Used for specifying the number of signatures.
        ACC_ADDR_OWNER,         // Invoker account.
        Address::Account(ACC_ADDR_OWNER), // Sender (can also be a contract).
        Energy::from(10000),    // Maximum energy allowed for the update.
        UpdateContractPayload {
            address: initialization.contract_address, // The contract to update.
            receive_name: OwnedReceiveName::new_unchecked("smart_contract_upgrade.upgrade".into()), // The receive function to call.
            message: OwnedParameter::from_serial(&input_parameter)
                .expect("`UpgradeParams` should be a valid inut parameter"), // The parameter sent to the contract.
            amount: Amount::from_ccd(0), // Sending the contract 0 CCD.
        },
    );

    assert_eq!(
        update.expect("Upgrade should succeed").state_changed,
        true,
        "State should be changed due to the `migration` function"
    );

    let invoke = chain
        .contract_invoke(
            ACC_ADDR_OWNER,
            Address::Account(ACC_ADDR_OWNER),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      initialization.contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_upgrade.view".to_string(),
                ),
                message:      OwnedParameter::empty(),
            },
        )
        .expect("Invoking `view` should always succeed");

    let state: State =
        from_bytes(&invoke.return_value).expect("View should always return a valid result");

    assert_eq!(state, State {
        admin:     ACC_ADDR_OWNER,
        old_state: "This state should be migrated as part of the smart contract upgrade."
            .to_string(),
        new_state: "This is the new state.".to_string(),
    });
}
