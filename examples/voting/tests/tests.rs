use concordium_smart_contract_testing::*;
use voting_contract::*;

// Constants.
const SIGNER: Signer = Signer::with_one_key();
const ALICE: AccountAddress = account_address!("00000000000000000000000000000000");
const ALICE_ADDR: Address = Address::Account(ALICE);
const BOB: AccountAddress = account_address!("11111111111111111111111111111111");
const BOB_ADDR: Address = Address::Account(BOB);
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(1000);

/// Test that voting after the `end_time` fails.
#[test]
fn test_vote_after_end_time() {
    let (mut chain, contract_address) = init();

    let params = VoteParameter {
        vote_index: 0,
    };

    // Advance time to after the end time.
    chain.tick_block_time(Duration::from_millis(1001)).expect("Won't overflow");

    // Try to vote.
    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.vote".to_string()),
            message:      OwnedParameter::from_serial(&params).expect("Valid vote parameter"),
        })
        .expect_err("Contract updated");

    // Check that the error is correct.
    let rv: VotingError = update.parse_return_value().expect("Deserialize VotingError");
    assert_eq!(rv, VotingError::VotingFinished);
}

/// Test that voting with an voting index that is out of range fails.
#[test]
fn test_vote_out_of_range() {
    let (mut chain, contract_address) = init();

    let params = VoteParameter {
        vote_index: 3, // Valid indexes are: 0, 1, 2.
    };

    // Try to vote.
    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.vote".to_string()),
            message:      OwnedParameter::from_serial(&params).expect("Valid vote parameter"),
        })
        .expect_err("Contract updated");

    // Check that the error is correct.
    let rv: VotingError = update.parse_return_value().expect("Deserialize VotingError");
    assert_eq!(rv, VotingError::InvalidVoteIndex);
}

/// Test that voting and changing your vote works.
///
/// In particular:
///  - Alice votes for option 0.
///  - Alice changes her vote to option 1.
///  - Bob votes for option 0.
///  - Bob again votes for option 0.
#[test]
fn test_voting_and_changing_vote() {
    let (mut chain, contract_address) = init();

    // Alice votes for option 0.
    let update_1 = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.vote".to_string()),
            message:      OwnedParameter::from_serial(&VoteParameter {
                vote_index: 0,
            })
            .expect("Valid vote parameter"),
        })
        .expect("Contract updated");

    // Check the events and votes.
    check_event(&update_1, ALICE, 0);
    assert_eq!(get_votes(&chain, contract_address), [1, 0, 0]);

    // Alice changes her vote to option 1.
    let update_2 = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.vote".to_string()),
            message:      OwnedParameter::from_serial(&VoteParameter {
                vote_index: 1,
            })
            .expect("Valid vote parameter"),
        })
        .expect("Contract updated");
    // Check the events and votes.
    check_event(&update_2, ALICE, 1);
    assert_eq!(get_votes(&chain, contract_address), [0, 1, 0]);

    // Bob votes for option 0.
    let update_3 = chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.vote".to_string()),
            message:      OwnedParameter::from_serial(&VoteParameter {
                vote_index: 0,
            })
            .expect("Valid vote parameter"),
        })
        .expect("Contract updated");
    // Check the events and votes.
    check_event(&update_3, BOB, 0);
    assert_eq!(get_votes(&chain, contract_address), [1, 1, 0]);

    // Bob again votes for option 0.
    let update_4 = chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.vote".to_string()),
            message:      OwnedParameter::from_serial(&VoteParameter {
                vote_index: 0,
            })
            .expect("Valid vote parameter"),
        })
        .expect("Contract updated");
    // Check the events and votes.
    check_event(&update_4, BOB, 0);
    assert_eq!(get_votes(&chain, contract_address), [1, 1, 0]);
}

/// Test that a contract is not allowed to vote.
#[test]
fn test_contract_voter() {
    let (mut chain, contract_address) = init();

    // Try to vote.
    let params = VoteParameter {
        vote_index: 0,
    };
    let update = chain
        .contract_update(
            SIGNER,
            ALICE,
            Address::Contract(contract_address), // The contract itself is the sender.
            Energy::from(10_000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      contract_address,
                receive_name: OwnedReceiveName::new_unchecked("voting.vote".to_string()),
                message:      OwnedParameter::from_serial(&params).expect("Valid vote parameter"),
            },
        )
        .expect_err("Contract updated");

    // Check that the error is correct.
    let rv: VotingError = update.parse_return_value().expect("Deserialize VotingError");
    assert_eq!(rv, VotingError::ContractVoter);
}

// Helpers:

/// Initialize chain and contract.
///
/// Also creates the following accounts:
///  - `ALICE`: Account with 1000 CCD.
///  - `BOB`: Account with 1000 CCD.
///
/// The contract is initialized with the following parameters:
///  - `description`: "Election description"
///  - `options`: ["A", "B", "C"]
///  - `end_time`: 1000 milliseconds after the unix epoch time.
fn init() -> (Chain, ContractAddress) {
    let mut chain = Chain::new();

    // Create accounts.
    chain.create_account(Account::new(ALICE, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(BOB, ACC_INITIAL_BALANCE));

    // Deploy module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, ALICE, module).expect("Deploy valid module");

    // Contract init parameters.
    let params = InitParameter {
        description: "Election description".to_string(),
        options:     vec!["A".to_string(), "B".to_string(), "C".to_string()],
        end_time:    Timestamp::from_timestamp_millis(1000),
    };

    // Initialize contract.
    let init = chain
        .contract_init(SIGNER, ALICE, Energy::from(10_000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_voting".to_string()),
            param:     OwnedParameter::from_serial(&params).expect("Valid init parameter"),
        })
        .expect("Contract initialized");

    (chain, init.contract_address)
}

/// Get the number of votes for each voting option.
fn get_votes(chain: &Chain, contract_address: ContractAddress) -> [u32; 3] {
    let view_0 = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.getNumberOfVotes".to_string()),
            message:      OwnedParameter::from_serial(&VoteParameter {
                vote_index: 0,
            })
            .expect("Valid vote parameter"),
        })
        .expect("View invoked");
    let vote_0: VoteCount = view_0.parse_return_value().expect("Deserialize VoteCount");

    let view_1 = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.getNumberOfVotes".to_string()),
            message:      OwnedParameter::from_serial(&VoteParameter {
                vote_index: 1,
            })
            .expect("Valid vote parameter"),
        })
        .expect("View invoked");
    let vote_1: VoteCount = view_1.parse_return_value().expect("Deserialize VoteCount");

    let view_2 = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.getNumberOfVotes".to_string()),
            message:      OwnedParameter::from_serial(&VoteParameter {
                vote_index: 2,
            })
            .expect("Valid vote parameter"),
        })
        .expect("View invoked");
    let vote_2: VoteCount = view_2.parse_return_value().expect("Deserialize VoteCount");

    [vote_0, vote_1, vote_2]
}

/// Check that the voting event is produced and that it is correct.
fn check_event(update: &ContractInvokeSuccess, voter: AccountAddress, vote_index: VoteIndex) {
    let events: Vec<Event> = update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect();
    assert_eq!(events, [Event::Vote(VoteEvent {
        voter,
        vote_index,
    })]);
}
