//! Tests for the recorder example contract.
use concordium_smart_contract_testing::*;
use concordium_std_derive::*;

const ACC_0: AccountAddress =
    account_address!("2xBpaHottqhwFZURMZW4uZduQvpxNDSy46iXMYs9kceNGaPpZX");
const ACC_1: AccountAddress =
    account_address!("2xdTv8awN1BjgYEw8W1BVXVtiEwG2b29U8KoZQqJrDuEqddseE");
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(1000);
const SIGNER: Signer = Signer::with_one_key();

#[test]
fn tests() {
    // Create the test chain.
    let mut chain = Chain::new();

    // Create two accounts on the chain.
    chain.create_account(Account::new(ACC_0, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(ACC_1, ACC_INITIAL_BALANCE));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, ACC_0, module).expect("Deploy valid module");

    // Initialize the contract.
    let initialization = chain
        .contract_init(SIGNER, ACC_0, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_recorder".to_string()),
            param:     OwnedParameter::empty(),
        })
        .expect("Init should succeed");
    let contract_address = initialization.contract_address;

    // Record two addresses.
    chain
        .contract_update(
            SIGNER,
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(5000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("recorder.record".to_string()),
                message:      OwnedParameter::from_serial(&ACC_0)
                    .expect("Serialize account address."),
            },
        )
        .expect("Recording `ACC_0`");
    chain
        .contract_update(
            SIGNER,
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(5000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("recorder.record".to_string()),
                message:      OwnedParameter::from_serial(&ACC_1)
                    .expect("Serialize account address."),
            },
        )
        .expect("Recording `ACC_1`");

    // Check that both addresses are returned by the 'list' view function.
    let view_list_1 = chain
        .contract_invoke(
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(5000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("recorder.list".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect("Viewing list with two elements");
    let returned_list_1: Vec<AccountAddress> =
        view_list_1.parse_return_value().expect("Decoding return value");
    assert_eq!(returned_list_1[..], [ACC_0, ACC_1]);

    // Make the transfers to all accounts.
    let update_transfer = chain
        .contract_update(
            SIGNER,
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(5000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("recorder.transfer".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect("Recording`ACC_1`");

    // Check that the contract returns `2` for the number of transfers made.
    let transfers_made: u64 = update_transfer.parse_return_value().expect("Decoding return value.");
    assert_eq!(transfers_made, 2);
    assert_eq!(update_transfer.account_transfers().collect::<Vec<_>>()[..], [
        (contract_address, Amount::zero(), ACC_0),
        (contract_address, Amount::zero(), ACC_1)
    ]);

    // Check that the 'list' view function now returns an empty list.
    let view_list_2 = chain
        .contract_invoke(
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(5000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("recorder.list".to_string()),
                message:      OwnedParameter::empty(),
            },
        )
        .expect("Viewing list with two elements");
    let returned_list_2: Vec<AccountAddress> =
        view_list_2.parse_return_value().expect("Decoding return value");
    assert!(returned_list_2.is_empty());
}
