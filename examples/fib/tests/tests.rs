use concordium_smart_contract_testing::*;
use concordium_std_derive::*;

const ACC_0: AccountAddress =
    account_address!("2wkBET2rRgE8pahuaczxKbmv7ciehqsne57F9gtzf1PVdr2VP3");
const SIGNER: Signer = Signer::with_one_key();

/// Compute the n-th fibonacci number.
fn fib(n: u64) -> u64 {
    let mut n1 = 1;
    let mut n2 = 1;
    for _ in 2..=n {
        let t = n1;
        n1 = n2;
        n2 += t;
    }
    n2
}

/// Test that calling the `receive` entrypoint produces the correct fib value in
/// the state.
#[test]
fn test() {
    // Create the test chain.
    let mut chain = Chain::new();

    // Create two accounts on the chain.
    chain.create_account(Account::new(ACC_0, Amount::from_ccd(1000)));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, ACC_0, module).expect("Deploy valid module");

    // Initialize the contract.
    let initialization = chain
        .contract_init(SIGNER, ACC_0, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_fib".to_string()),
            param:     OwnedParameter::empty(),
        })
        .expect("Init should succeed");
    let contract_address = initialization.contract_address;

    // Call the `receive` entrypoint with `7` as input.
    let update = chain
        .contract_update(
            SIGNER,
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(50000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("fib.receive".to_string()),
                message:      OwnedParameter::from_serial(&7u64)
                    .expect("Parameter has valid size."),
            },
        )
        .expect("Calling receive");

    let rv: u64 = update.parse_return_value().expect("Return value");
    assert_eq!(rv, fib(7));

    // Check that the result is persisted by invoking the `view` entrypoint.
    let update = chain
        .contract_invoke(
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(50000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("fib.view".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect("Calling receive");

    let rv: u64 = update.parse_return_value().expect("Return value");
    assert_eq!(rv, fib(7));
}
