//! This file contains the tests for the icecream contract.
use concordium_smart_contract_testing::*;
use icecream::*;

/// The icecream buyer.
const ACC_0: AccountAddress = AccountAddress([0; 32]);
/// The icecream vendor.
const ACC_1: AccountAddress = AccountAddress([1; 32]);
const SIGNER: Signer = Signer::with_one_key();
const ICECREAM_PRICE: Amount = Amount::from_ccd(1000);
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

/// Test that the icecream contract transfers the correct amount of money to the
/// vendor if the weather is sunny.
#[test]
fn test_sunny_day() {
    let (mut chain, module_reference) = initialize_chain();

    // Initialize the weather contract with sunny weather.
    let weather = Weather::Sunny;
    let weather_address = initialize_weather(&mut chain, module_reference, &weather);

    // Initialize the icecream contract with the weather contract address.
    let icecream_address = initialize_icecream(&mut chain, module_reference, weather_address);

    // Buy the icecream.
    let update = chain
        .contract_update(
            SIGNER,
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       ICECREAM_PRICE,
                address:      icecream_address,
                receive_name: OwnedReceiveName::new_unchecked("icecream.buy_icecream".to_string()),
                message:      OwnedParameter::from_serial(&ACC_1)
                    .expect("Serialize account address."),
            },
        )
        .expect("Call icecream contract");

    // Check that the icecream vendor received the correct amount of money.
    assert_eq!(chain.account_balance_available(ACC_1), Some(ACC_INITIAL_BALANCE + ICECREAM_PRICE));
    // Assert that the transfer to ACC_1 occured via the method on `update`.
    assert_eq!(update.account_transfers().collect::<Vec<_>>()[..], [(
        icecream_address,
        ICECREAM_PRICE,
        ACC_1
    )]);
}

/// Test that the icecream contract transfers the correct amount of money back
/// to the sender on rainy days.
#[test]
fn test_rainy_days() {
    let (mut chain, module_reference) = initialize_chain();

    // Initialize the weather contract with rainy weather.
    let weather = Weather::Rainy;
    let weather_address = initialize_weather(&mut chain, module_reference, &weather);

    // Initialize the icecream contract with the weather contract address.
    let icecream_address = initialize_icecream(&mut chain, module_reference, weather_address);

    // Buy the icecream.
    let update = chain
        .contract_update(
            SIGNER,
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       ICECREAM_PRICE,
                address:      icecream_address,
                receive_name: OwnedReceiveName::new_unchecked("icecream.buy_icecream".to_string()),
                message:      OwnedParameter::from_serial(&ACC_1).expect("Serialize address"),
            },
        )
        .expect("Call icecream contract");

    // Check that the icecream vendor still has the original balance.
    assert_eq!(chain.account_balance_available(ACC_1), Some(ACC_INITIAL_BALANCE));
    // Check that the money were returned to the sender, ACC_0.
    assert_eq!(update.account_transfers().collect::<Vec<_>>()[..], [(
        icecream_address,
        ICECREAM_PRICE,
        ACC_0
    )]);
}

/// Test that `buy_icecream` returns the error `ContractInvokeError` if the
/// weather contract doesn't return a valid weather, because the contract hasn't
/// been initialized.
#[test]
fn test_missing_weather() {
    let (mut chain, module_reference) = initialize_chain();

    // Initialize the icecream contract with an unused address for the weather
    // contract.
    let icecream_address =
        initialize_icecream(&mut chain, module_reference, ContractAddress::new(0, 0));

    // Buy the icecream.
    let update = chain
        .contract_update(
            SIGNER,
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       ICECREAM_PRICE,
                address:      icecream_address,
                receive_name: OwnedReceiveName::new_unchecked("icecream.buy_icecream".to_string()),
                message:      OwnedParameter::from_serial(&ACC_1).expect("Serialize address"),
            },
        )
        .expect_err("Call icecream contract");

    // Deserialize the return value from `update` and check that it is the expected
    // error.
    let rv: ContractError = update.parse_return_value()
        .expect("Deserialize return value");
    assert_eq!(rv, ContractError::ContractInvokeError);
}

/// Test that `buy_icecream` returns the error `TrasnferError` if the icecream
/// vendor doesn't exist.
#[test]
fn test_missing_icecream_vendor() {
    let (mut chain, module_reference) = initialize_chain();

    let non_existing_account = AccountAddress([2; 32]);

    // Initialize the weather contract with sunny weather.
    let weather = Weather::Sunny;
    let weather_address = initialize_weather(&mut chain, module_reference, &weather);

    // Initialize the icecream contract with the weather contract address.
    let icecream_address = initialize_icecream(&mut chain, module_reference, weather_address);

    // Buy the icecream.
    let update = chain
        .contract_update(
            SIGNER,
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       ICECREAM_PRICE,
                address:      icecream_address,
                receive_name: OwnedReceiveName::new_unchecked("icecream.buy_icecream".to_string()),
                message:      OwnedParameter::from_serial(&non_existing_account)
                    .expect("Serialize address"),
            },
        )
        .expect_err("Call icecream contract");

    // Deserialize the return value from `update` and check that it is the expected
    // error.
    let rv: ContractError = update.parse_return_value()
        .expect("Deserialize return value");
    assert_eq!(rv, ContractError::TransferError);
}

// ** HELPERS **

/// Initialize the weather contract with the given weather.
fn initialize_weather(
    chain: &mut Chain,
    module_reference: ModuleReference,
    weather: &Weather,
) -> ContractAddress {
    chain
        .contract_init(SIGNER, ACC_0, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   module_reference,
            init_name: OwnedContractName::new_unchecked("init_weather".to_string()),
            param:     OwnedParameter::from_serial(weather).expect("Serialize weather"),
        })
        .expect("Initialize weather")
        .contract_address
}

/// Initialize the icecream contract with the given weather contract address.
fn initialize_icecream(
    chain: &mut Chain,
    module_reference: ModuleReference,
    weather_address: ContractAddress,
) -> ContractAddress {
    chain
        .contract_init(SIGNER, ACC_0, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   module_reference,
            init_name: OwnedContractName::new_unchecked("init_icecream".to_string()),
            param:     OwnedParameter::from_serial(&weather_address)
                .expect("Serialize weather address"),
        })
        .expect("Initialize icecream")
        .contract_address
}

/// Initialize the chain, create two accounts (ACC_0, ACC_1) and deploy the
/// module.
fn initialize_chain() -> (Chain, ModuleReference) {
    let mut chain = Chain::new();

    // Create two accounts on the chain.
    chain.create_account(Account::new(ACC_0, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(ACC_1, ACC_INITIAL_BALANCE));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, ACC_0, module).expect("Deploy valid module");

    (chain, deployment.module_reference)
}
