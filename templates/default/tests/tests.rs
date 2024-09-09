use concordium_smart_contract_testing::*;
use {{crate_name}}::*;

/// A test account.
const ALICE: AccountAddress = AccountAddress([0u8; 32]);
const ALICE_ADDR: Address = Address::Account(ALICE);

/// The initial balance of the ALICE test account.
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10_000);

/// A [`Signer`] with one set of keys, used for signing transactions.
const SIGNER: Signer = Signer::with_one_key();

/// Test that invoking the `receive` endpoint with the `false` parameter
/// succeeds in updating the contract.
#[test]
fn test_throw_no_error() {
    let (mut chain, init) = initialize();

    // Update the contract via the `receive` entrypoint with the parameter `false`.
    chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            address:      init.contract_address,
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("{{crate_name}}.receive".to_string()),
            message:      OwnedParameter::from_serial(&false)
                .expect("Parameter within size bounds"),
        })
        .expect("Update succeeds with `false` as input.");
}

/// Test that invoking the `receive` endpoint with the `true` parameter
/// results in the `CustomError` being thrown.
#[test]
fn test_throw_error() {
    let (mut chain, init) = initialize();

    // Update the contract via the `receive` entrypoint with the parameter `true`.
    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            address:      init.contract_address,
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("{{crate_name}}.receive".to_string()),
            message:      OwnedParameter::from_serial(&true).expect("Parameter within size bounds"),
        })
        .expect_err("Update fails with `true` as input.");

    // Check that the contract returned `CustomError`.
    let error: Error = update.parse_return_value().expect("Deserialize `Error`");
    assert_eq!(error, Error::CustomError);
}

/// Helper method for initializing the contract.
///
/// Does the following:
///  - Creates the [`Chain`]
///  - Creates one account, `Alice` with `10_000` CCD as the initial balance.
///  - Initializes the contract.
///  - Returns the [`Chain`] and the [`ContractInitSuccess`]
fn initialize() -> (Chain, ContractInitSuccess) {
    // Initialize the test chain.
    let mut chain = Chain::new();

    // Create the test account.
    chain.create_account(Account::new(ALICE, ACC_INITIAL_BALANCE));

    // Load the module.
    let module = module_load_v1("./concordium-out/module.wasm.v1").expect("Module exists at path");
    // Deploy the module.
    let deployment = chain.module_deploy_v1(SIGNER, ALICE, module).expect("Deploy valid module");

    let parameter = CustomInputParameter { num: 0 };

    // Initialize the contract.
    let init = chain
        .contract_init(
            SIGNER,
            ALICE,
            Energy::from(10_000),
            InitContractPayload {
                amount: Amount::zero(),
                mod_ref: deployment.module_reference,
                init_name: OwnedContractName::new_unchecked("init_{{crate_name}}".to_string()),
                param: OwnedParameter::from_serial(&parameter).expect("Parameter is valid."),
            },
        )
        .expect("Initializing contract");

    (chain, init)
}
