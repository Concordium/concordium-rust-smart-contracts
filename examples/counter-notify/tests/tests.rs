use concordium_smart_contract_testing::*;
use concordium_std_derive::account_address;

const ACC_0: AccountAddress =
    account_address!("2wkBET2rRgE8pahuaczxKbmv7ciehqsne57F9gtzf1PVdr2VP3");
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(1000);
const SIGNER: Signer = Signer::with_one_key();

/// Test that the reentrancy attack occurs and is caught by the `counter-notify`
/// contract.
#[test]
fn tests() {
    // Create the test chain.
    let mut chain = Chain::new();

    // Create one account on the chain.
    chain.create_account(Account::new(ACC_0, ACC_INITIAL_BALANCE));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, ACC_0, module).expect("Deploy valid module");

    // Initialize the contract.
    let init_counter = chain
        .contract_init(SIGNER, ACC_0, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_counter-notify".to_string()),
            param:     OwnedParameter::empty(),
        })
        .expect("Init of counter-notify contract should succeed");
    let init_reentrancy = chain
        .contract_init(SIGNER, ACC_0, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_reentrancy-attacker".to_string()),
            param:     OwnedParameter::empty(),
        })
        .expect("Init of reentrancy-attacker should succeed");

    let update = chain
        .contract_update(
            SIGNER,
            ACC_0,
            Address::Account(ACC_0),
            Energy::from(5000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      init_counter.contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "counter-notify.increment-and-notify".to_string(),
                ),
                message:      OwnedParameter::from_serial(&(
                    init_reentrancy.contract_address,
                    EntrypointName::new_unchecked("call-just-increment"),
                ))
                .expect("Serialize account address."),
            },
        )
        .expect("Updating contract");

    use concordium_smart_contract_testing::ContractTraceElement::*;

    // Check that the correct calls and events occured.
    assert!(matches!(update.effective_trace_elements().collect::<Vec<_>>()[..], [
        Interrupted {
            address: ContractAddress {
                index:    0,
                subindex: 0,
            },
            ..
        },
        Interrupted {
            address: ContractAddress {
                index:    1,
                subindex: 0,
            },
            ..
        },
        Updated {
            data: InstanceUpdatedEvent {
                receive_name: rcv_name_1,
                ..
            },
        },
        Resumed {
            address: ContractAddress {
                index:    1,
                subindex: 0,
            },
            success: true,
        },
        Updated {
            data: InstanceUpdatedEvent {
                receive_name: rcv_name_2,
                ..
            },
        },
        Resumed {
            address: ContractAddress {
                index:    0,
                subindex: 0,
            },
            success: true,
        },
        Updated {
            data: InstanceUpdatedEvent {
                receive_name: rcv_name_3,
                ..
            },
        },
    ] if rcv_name_1 == "counter-notify.just-increment" && rcv_name_2 == "reentrancy-attacker.call-just-increment" && rcv_name_3 == "counter-notify.increment-and-notify"));

    // Check that the contract observed the reentrancy attack.
    let rv: bool = update.parse_return_value().unwrap();
    assert!(rv, "Re-entrancy attack not observed.");
}
