use concordium_smart_contract_testing::*;
use concordium_std_derive::*;
use voting_contract::*;

// Constants.
const SIGNER: Signer = Signer::with_one_key();
const ALICE: AccountAddress =
    account_address!("2xBpaHottqhwFZURMZW4uZduQvpxNDSy46iXMYs9kceNGaPpZX");
const ALICE_ADDR: Address = Address::Account(ALICE);
const BOB: AccountAddress = account_address!("2xdTv8awN1BjgYEw8W1BVXVtiEwG2b29U8KoZQqJrDuEqddseE");
const BOB_ADDR: Address = Address::Account(BOB);
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(1000);

/// Test that voting after the `end_time` fails.
#[test]
fn test_vote_after_end_time() {
    let (mut chain, contract_address) = init();

    let params = "A".to_string();

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
fn test_invalid_vote() {
    let (mut chain, contract_address) = init();

    let params = "invalid vote".to_string();

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
    assert_eq!(rv, VotingError::InvalidVote);
}

/// Test that voting and changing your vote works.
///
/// In particular:
///  - Alice votes for A.
///  - Alice changes her vote to B.
///  - Bob votes for A.
///  - Bob again votes for A.
#[test]
fn test_voting_and_changing_vote() {
    let (mut chain, contract_address) = init();

    // Alice votes for A.
    let update_1 = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.vote".to_string()),
            message:      OwnedParameter::from_serial(&"A".to_string())
                .expect("Valid vote parameter"),
        })
        .expect("Contract updated");

    // Check the events and votes.
    check_event(&update_1, ALICE, "A");
    assert_eq!(get_votes(&chain, contract_address), [1, 0, 0]);

    // Alice changes her vote to B.
    let update_2 = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.vote".to_string()),
            message:      OwnedParameter::from_serial(&"B".to_string())
                .expect("Valid vote parameter"),
        })
        .expect("Contract updated");
    // Check the events and votes.
    check_event(&update_2, ALICE, "B");
    assert_eq!(get_votes(&chain, contract_address), [0, 1, 0]);

    // Bob votes for A.
    let update_3 = chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.vote".to_string()),
            message:      OwnedParameter::from_serial(&"A".to_string())
                .expect("Valid vote parameter"),
        })
        .expect("Contract updated");
    // Check the events and votes.
    check_event(&update_3, BOB, "A");
    assert_eq!(get_votes(&chain, contract_address), [1, 1, 0]);

    // Bob again votes for option 0.
    let update_4 = chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.vote".to_string()),
            message:      OwnedParameter::from_serial(&"A".to_string())
                .expect("Valid vote parameter"),
        })
        .expect("Contract updated");
    // Check the events and votes.
    check_event(&update_4, BOB, "A");
    assert_eq!(get_votes(&chain, contract_address), [1, 1, 0]);
}

/// Test that a contract is not allowed to vote.
#[test]
fn test_contract_voter() {
    let (mut chain, contract_address) = init();

    // Try to vote.
    let params = "A".to_string();
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
    let params = ElectionConfig {
        description: "Election description".to_string(),
        options:     vec!["A".to_string(), "B".to_string(), "C".to_string()],
        deadline:    Timestamp::from_timestamp_millis(1000),
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

/// Get the number of votes for each voting option, A, B and C.
fn get_votes(chain: &Chain, contract_address: ContractAddress) -> [u32; 3] {
    let view_a = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.getNumberOfVotes".to_string()),
            message:      OwnedParameter::from_serial(&"A".to_string())
                .expect("Valid vote parameter"),
        })
        .expect("View invoked");
    let vote_a: u32 = view_a.parse_return_value().expect("Deserialize VoteCount");

    let view_b = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.getNumberOfVotes".to_string()),
            message:      OwnedParameter::from_serial(&"B".to_string())
                .expect("Valid vote parameter"),
        })
        .expect("View invoked");
    let vote_b: u32 = view_b.parse_return_value().expect("Deserialize VoteCount");

    let view_c = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked("voting.getNumberOfVotes".to_string()),
            message:      OwnedParameter::from_serial(&"C".to_string())
                .expect("Valid vote parameter"),
        })
        .expect("View invoked");
    let vote_c: u32 = view_c.parse_return_value().expect("Deserialize VoteCount");

    [vote_a, vote_b, vote_c]
}

/// Check that the voting event is produced and that it is correct.
fn check_event(
    update: &ContractInvokeSuccess,
    voter: AccountAddress,
    vote_option: impl Into<String>,
) {
    let events: Vec<VoteEvent> = update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect();
    assert_eq!(events, [VoteEvent {
        voter,
        option: vote_option.into(),
    }]);
}
