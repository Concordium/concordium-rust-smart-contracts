//! A multi token example implementation of the Concordium Token Standard CIS2
//! and the Concordium Sponsored Transaction Standard CIS3.
//!
//! # Description
//! An instance of this smart contract can contain a number of different token
//! types each identified by a token ID. A token type is then globally
//! identified by the contract address together with the token ID.
//!
//! Note: The word 'address' refers to either an account address or a
//! contract address.
//!
//! ## CIS3 standard (sponsored transactions):
//! This contract implements the Concordium Token Standard CIS2. In addition, it
//! implements the CIS3 standard which includes features for sponsored
//! transactions.
//!
//! The use case for CIS3 in this smart contract is for third-party service
//! providers (the owner of this contract) that deal with conventional
//! clients/users that don't want to acquire crypto (such as CCD) from an
//! exchange. The third-party has often traditional fiat channels open
//! (off-chain) with the conventional clients/users and wants to offer to submit
//! transactions on behalf of the user on-chain. The user/client has to sign its
//! intended transaction before communicating it (off-chain) to the third-party
//! service provider (often paying some fees in fiat money). The third-party
//! service provider submits the transaction on behalf of the user and pays the
//! transaction fee to execute the transaction on-chain.
//!
//! As follows from the CIS3 specification, the contract has a `permit`
//! function. It is the sponsored counterpart to the
//! `transfer/updateOperator/mint/burn` function and can be executed by anyone
//! on behalf of an account given a signed message.
//!
//! Concordium supports natively multi-sig accounts. Each account address on
//! Concordium is controlled by one or several credential(s) (real-world
//! identities) and each credential has one or several public-private key
//! pair(s). Both the key and signature structures of an account are represented
//! as two-level maps (e.g. BTreeMap<CredentialIndexU8,
//! BTreeMap<PublicKeyIndexU8, PublicKey>> or BTreeMap<CredentialIndexU8,
//! BTreeMap<SignatureIndexU8, Signature>>). The outer map of
//! `BTreeMap<CredentialIndexU8, BTreeMap<PublicKeyIndexU8, PublicKey>>` has an
//! `AccountThreshold` (number of credentials needed to sign the transaction
//! initiated by that account) and the inner map has a `SignatureThreshold`
//! (number of Signatures needed for a specific credential so that this
//! credential is considered to have signed the transaction initiated by that
//! account). The CIS3 standard supports multi-sig accounts. For basic accounts
//! (that have exactly one credential and exactly one public key for that
//! credential), the signaturesMaps/publicKeyMaps in this contract, will have
//! only one value at key 0 in the inner and outer maps.
//!
//! ## `Transfer` and `updateOperator` functions:
//! As follows from the CIS2 specification, the contract has a `transfer`
//! function for transferring an amount of a specific token type from one
//! address to another address. An address can enable and disable one or more
//! addresses as operators with the `updateOperator` function. An operator of
//! an address is allowed to transfer any tokens owned by this address.
//!
//! ## `Mint` and `burn` functions:
//! In this example, the contract is initialized with no tokens, and tokens can
//! be minted through a `mint` contract function, which can be called by anyone
//! (unprotected function). The `mint` function airdrops the `MINT_AIRDROP`
//! amount of tokens to a specified `owner` address in the input parameter.
//! ATTENTION: You most likely want to add your custom access control mechanism
//! to the `mint` function and `permit` function.
//!
//! A token owner (or any of its operator addresses) can burn some of the token
//! owner's tokens by invoking the `burn` function.
//!
//! ## `onReceivingCIS2` functions:
//! This contract also contains an example of a function to be called when
//! receiving tokens. In which case the contract will forward the tokens to
//! the contract owner.
//! This function is not very useful and is only there to showcase a simple
//! implementation of a token receive hook.
//!
//! ## Grant and Revoke roles:
//! The contract has access control roles. The admin can grant or revoke all
//! other roles. The available roles are ADMIN (can grant/revoke roles),
//! UPGRADER (can upgrade the contract), BLACKLISTER (can blacklist addresses),
//! and PAUSER (can pause the contract).
//!
//! ## Blacklist:
//! This contract includes a blacklist. The account with `BLACKLISTER` role can
//! add/remove addresses to/from that list. Blacklisted addresses can not
//! transfer their tokens, receive new tokens, or burn their tokens.
//!
//! ## Pausing:
//! This contract can be paused by an address with the PAUSER role.
//! `Mint,burn,updateOperator,transfer` entrypoints cannot be called when the
//! contract is paused.
//!
//! ## Native upgradability:
//! This contract can be upgraded. The contract
//! has a function to upgrade the smart contract instance to a new module and
//! call optionally a migration function after the upgrade. To use this example,
//! deploy `contract-version1` and then upgrade the smart contract instance to
//! `contract-version2` by invoking the `upgrade` function with the below JSON
//! inputParameter:
//!
//! ```json
//! {
//!   "migrate": {
//!     "Some": [
//!       [
//!         "migration",
//!         ""
//!       ]
//!     ]
//!   },
//!   "module": "<ModuleReferenceContractVersion2>"
//! }
//! ```
//!
//! This initial contract (`contract-version1`) has no migration function.
//! The next version of the contract (`contract-version2`), could have a
//! migration function added to e.g. change the shape of the smart contract
//! state from `contract-version1` to `contract-version2`.
//! https://github.com/Concordium/concordium-rust-smart-contracts/blob/main/examples/smart-contract-upgrade/contract-version2/src/lib.rs
#![cfg_attr(not(feature = "std"), no_std)]
use concordium_cis2::*;
use concordium_std::{collections::BTreeMap, EntrypointName, *};

/// The standard identifier for the CIS-3 standard.
pub const CIS3_STANDARD_IDENTIFIER: StandardIdentifier<'static> =
    StandardIdentifier::new_unchecked("CIS-3");

/// List of supported standards by this contract address.
const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 3] =
    [CIS0_STANDARD_IDENTIFIER, CIS2_STANDARD_IDENTIFIER, CIS3_STANDARD_IDENTIFIER];

/// List of supported entrypoints by the `permit` function (CIS3 standard).
const SUPPORTS_PERMIT_ENTRYPOINTS: [EntrypointName; 2] =
    [EntrypointName::new_unchecked("updateOperator"), EntrypointName::new_unchecked("transfer")];

/// Event tags.
pub const UPDATE_BLACKLIST_EVENT_TAG: u8 = 0;
pub const GRANT_ROLE_EVENT_TAG: u8 = 1;
pub const REVOKE_ROLE_EVENT_TAG: u8 = 2;
pub const NONCE_EVENT_TAG: u8 = 250;

const TRANSFER_ENTRYPOINT: EntrypointName<'_> = EntrypointName::new_unchecked("transfer");
const UPDATE_OPERATOR_ENTRYPOINT: EntrypointName<'_> =
    EntrypointName::new_unchecked("updateOperator");
const MINT_ENTRYPOINT: EntrypointName<'_> = EntrypointName::new_unchecked("mint");
const BURN_ENTRYPOINT: EntrypointName<'_> = EntrypointName::new_unchecked("burn");

/// Tagged events to be serialized for the event log.
#[derive(Debug, Serial, Deserial, PartialEq, Eq)]
#[concordium(repr(u8))]
pub enum Event {
    /// The event is logged whenever an address is added or removed from the
    /// blacklist.
    #[concordium(tag = 0)]
    UpdateBlacklist(UpdateBlacklistEvent),
    /// The event tracks when a new role is granted to an address.
    #[concordium(tag = 1)]
    GrantRole(GrantRoleEvent),
    /// The event tracks when a role is revoked from an address.
    #[concordium(tag = 2)]
    RevokeRole(RevokeRoleEvent),
    /// Cis3 event.
    /// The event tracks the nonce used by the signer of the `PermitMessage`
    /// whenever the `permit` function is invoked.
    #[concordium(tag = 250)]
    Nonce(NonceEvent),
    /// Cis2 token events.
    #[concordium(forward = cis2_events)]
    Cis2Event(Cis2Event<ContractTokenId, ContractTokenAmount>),
}

/// The NonceEvent is logged when the `permit` function is invoked. The event
/// tracks the nonce used by the signer of the `PermitMessage`.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct NonceEvent {
    /// The nonce that was used in the `PermitMessage`.
    pub nonce:   u64,
    /// Account that signed the `PermitMessage`.
    pub account: AccountAddress,
}

/// The UpdateBlacklistEvent is logged when an address is added to or removed
/// from the blacklist.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct UpdateBlacklistEvent {
    /// The update to the address.
    pub update:  BlacklistUpdate,
    /// The address which is added/removed from the blacklist.
    pub address: Address,
}

/// The GrantRoleEvent is logged when a new role is granted to an address.
#[derive(Serialize, SchemaType, Debug, PartialEq, Eq)]
pub struct GrantRoleEvent {
    /// The address that has been its role granted.
    pub address: Address,
    /// The role that was granted to the above address.
    pub role:    Roles,
}

/// The RevokeRoleEvent is logged when a role is revoked from an address.
#[derive(Serialize, SchemaType, Debug, PartialEq, Eq)]
pub struct RevokeRoleEvent {
    /// Address that has been its role revoked.
    pub address: Address,
    /// The role that was revoked from the above address.
    pub role:    Roles,
}

// Implementing a custom schemaType for the `Event` struct containing all
// CIS2/CIS3 events. This custom implementation flattens the fields to avoid one
// level of nesting. Deriving the schemaType would result in e.g.: {"Nonce":
// [{...fields}] }. In contrast, this custom schemaType implementation results
// in e.g.: {"Nonce": {...fields} }
impl schema::SchemaType for Event {
    fn get_type() -> schema::Type {
        let mut event_map = BTreeMap::new();
        event_map.insert(
            NONCE_EVENT_TAG,
            (
                "Nonce".to_string(),
                schema::Fields::Named(vec![
                    (String::from("nonce"), u64::get_type()),
                    (String::from("account"), AccountAddress::get_type()),
                ]),
            ),
        );
        event_map.insert(
            GRANT_ROLE_EVENT_TAG,
            (
                "GrantRole".to_string(),
                schema::Fields::Named(vec![
                    (String::from("address"), Address::get_type()),
                    (String::from("role"), Roles::get_type()),
                ]),
            ),
        );
        event_map.insert(
            REVOKE_ROLE_EVENT_TAG,
            (
                "RevokeRole".to_string(),
                schema::Fields::Named(vec![
                    (String::from("address"), Address::get_type()),
                    (String::from("role"), Roles::get_type()),
                ]),
            ),
        );
        event_map.insert(
            UPDATE_BLACKLIST_EVENT_TAG,
            (
                "UpdateBlacklist".to_string(),
                schema::Fields::Named(vec![
                    (String::from("update"), BlacklistUpdate::get_type()),
                    (String::from("address"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            TRANSFER_EVENT_TAG,
            (
                "Transfer".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), ContractTokenId::get_type()),
                    (String::from("amount"), ContractTokenAmount::get_type()),
                    (String::from("from"), Address::get_type()),
                    (String::from("to"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            MINT_EVENT_TAG,
            (
                "Mint".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), ContractTokenId::get_type()),
                    (String::from("amount"), ContractTokenAmount::get_type()),
                    (String::from("owner"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            BURN_EVENT_TAG,
            (
                "Burn".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), ContractTokenId::get_type()),
                    (String::from("amount"), ContractTokenAmount::get_type()),
                    (String::from("owner"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            UPDATE_OPERATOR_EVENT_TAG,
            (
                "UpdateOperator".to_string(),
                schema::Fields::Named(vec![
                    (String::from("update"), OperatorUpdate::get_type()),
                    (String::from("owner"), Address::get_type()),
                    (String::from("operator"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            TOKEN_METADATA_EVENT_TAG,
            (
                "TokenMetadata".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), ContractTokenId::get_type()),
                    (String::from("metadata_url"), MetadataUrl::get_type()),
                ]),
            ),
        );
        schema::Type::TaggedEnum(event_map)
    }
}

// Types

/// Contract token ID type.
/// To save bytes we use a small token ID type, but is limited to be represented
/// by a `u8`.
pub type ContractTokenId = TokenIdU8;

/// Contract token amount type.
pub type ContractTokenAmount = TokenAmountU64;

/// The parameter for the contract function `mint` which mints/airdrops a number
/// of tokens to the owner's address.
#[derive(Serialize, SchemaType, Clone)]
pub struct MintParams {
    /// Owner of the newly minted tokens.
    pub to:           Receiver,
    /// The metadata_url of the token.
    pub metadata_url: MetadataUrl,
    /// The token_id to mint/create additional tokens.
    pub token_id:     ContractTokenId,
    /// Additional data that can be sent to the receiving contract.
    pub data:         AdditionalData,
}

/// The parameter for the contract function `burn` which burns a number
/// of tokens from the owner's address.
#[derive(Serialize, SchemaType)]
pub struct BurnParams {
    /// Owner of the tokens.
    pub owner:    Address,
    /// The amount of tokens to burn.
    pub amount:   ContractTokenAmount,
    /// The token_id of the tokens to be burned.
    pub token_id: ContractTokenId,
}

/// The parameter type for the contract function `supportsPermit`.
#[derive(Debug, Serialize, SchemaType)]
pub struct SupportsPermitQueryParams {
    /// The list of supportPermit queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<OwnedEntrypointName>,
}

/// The parameter type for the contract function `setImplementors`.
/// Takes a standard identifier and list of contract addresses providing
/// implementations of this standard.
#[derive(Debug, Serialize, SchemaType)]
struct SetImplementorsParams {
    /// The identifier for the standard.
    id:           StandardIdentifierOwned,
    /// The addresses of the implementors of the standard.
    implementors: Vec<ContractAddress>,
}

/// Part of the parameter type for the contract function `permit`.
/// Specifies the message that is signed.
#[derive(SchemaType, Serialize)]
pub struct PermitMessage {
    /// The contract_address that the signature is intended for.
    pub contract_address: ContractAddress,
    /// A nonce to prevent replay attacks.
    pub nonce:            u64,
    /// A timestamp to make signatures expire.
    pub timestamp:        Timestamp,
    /// The entry_point that the signature is intended for.
    pub entry_point:      OwnedEntrypointName,
    /// The serialized payload that should be forwarded to either the `transfer`
    /// or the `updateOperator` function.
    #[concordium(size_length = 2)]
    pub payload:          Vec<u8>,
}

/// The parameter type for the contract function `permit`.
/// Takes a signature, the signer, and the message that was signed.
#[derive(Serialize, SchemaType)]
pub struct PermitParam {
    /// Signature/s. The CIS3 standard supports multi-sig accounts.
    pub signature: AccountSignatures,
    /// Account that created the above signature.
    pub signer:    AccountAddress,
    /// Message that was signed.
    pub message:   PermitMessage,
}

#[derive(Serialize)]
pub struct PermitParamPartial {
    /// Signature/s. The CIS3 standard supports multi-sig accounts.
    pub signature: AccountSignatures,
    /// Account that created the above signature.
    pub signer:    AccountAddress,
}

/// The parameter type for the contract function `setPaused`.
#[derive(Serialize, SchemaType)]
#[repr(transparent)]
pub struct SetPausedParams {
    /// Specifies if contract is paused.
    pub paused: bool,
}

/// The parameter type for the contract function `upgrade`.
/// Takes the new module and optionally an entrypoint to call in the new module
/// after triggering the upgrade. The upgrade is reverted if the entrypoint
/// fails. This is useful for doing migration in the same transaction triggering
/// the upgrade.
#[derive(Serialize, SchemaType)]
pub struct UpgradeParams {
    /// The new module reference.
    pub module:  ModuleReference,
    /// Optional entrypoint to call in the new module after upgrade.
    pub migrate: Option<(OwnedEntrypointName, OwnedParameter)>,
}

/// The parameter for the contract function `grantRole` which grants a role to
/// an address.
#[derive(Serialize, SchemaType)]
pub struct GrantRoleParams {
    /// The address that has been its role granted.
    pub address: Address,
    /// The role that has been granted to the above address.
    pub role:    Roles,
}

/// The parameter for the contract function `revokeRole` which revokes a role
/// from an address.
#[derive(Serialize, SchemaType)]
pub struct RevokeRoleParams {
    /// The address that has been its role revoked.
    pub address: Address,
    /// The role that has been revoked from the above address.
    pub role:    Roles,
}

/// A struct containing a set of roles granted to an address.
#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
struct AddressRoleState<S> {
    /// Set of roles.
    roles: StateSet<Roles, S>,
}

/// Enum of available roles in this contract.
#[derive(Serialize, PartialEq, Eq, Reject, SchemaType, Clone, Copy, Debug)]
pub enum Roles {
    /// Admin role.
    ADMIN,
    /// Upgrader role.
    UPGRADER,
    /// Blacklister role.
    BLACKLISTER,
    /// Pauser role.
    PAUSER,
    // /// Minter role. (comment in if you want a MINTER role)
    // MINTER,
}

/// The state for each address.
#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
struct AddressState<S = StateApi> {
    /// The amount of tokens owned by this address.
    balances:  StateMap<ContractTokenId, ContractTokenAmount, S>,
    /// The addresses which are currently enabled as operators for this address.
    operators: StateSet<Address, S>,
}

impl AddressState {
    fn empty(state_builder: &mut StateBuilder) -> Self {
        AddressState {
            balances:  state_builder.new_map(),
            operators: state_builder.new_set(),
        }
    }
}

/// The contract state,
///
/// Note: The specification does not specify how to structure the contract state
/// and this could be structured in a more space-efficient way.
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
struct State<S = StateApi> {
    /// The state of addresses.
    state:           StateMap<Address, AddressState<S>, S>,
    /// All of the token IDs.
    tokens:          StateMap<ContractTokenId, MetadataUrl, S>,
    /// A map with contract addresses providing implementations of additional
    /// standards.
    implementors:    StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
    /// A registry to link an account to its next nonce. The nonce is used to
    /// prevent replay attacks of the signed message. The nonce is increased
    /// sequentially every time a signed message (corresponding to the
    /// account) is successfully executed in the `permit` function. This
    /// mapping keeps track of the next nonce that needs to be used by the
    /// account to generate a signature.
    nonces_registry: StateMap<AccountAddress, u64, S>,
    /// Set of addresses that are not allowed to receive new tokens, sent
    /// their tokens, or burn their tokens.
    blacklist:       StateSet<Address, S>,
    /// The amount of tokens airdropped when the mint function is invoked.
    mint_airdrop:    ContractTokenAmount,
    /// Specifies if the contract is paused.
    paused:          bool,
    /// A map containing all roles granted to addresses.
    roles:           StateMap<Address, AddressRoleState<S>, S>,
}

/// The different errors the contract can produce.
#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
pub enum CustomContractError {
    /// Failed parsing the parameter.
    #[from(ParseError)]
    ParseParams, // -1
    /// Failed logging: Log is full.
    LogFull, // -2
    /// Failed logging: Log is malformed.
    LogMalformed, // -3
    /// Invalid contract name.
    InvalidContractName, // -4
    /// Only a smart contract can call this function.
    ContractOnly, // -5
    /// Failed to invoke a contract.
    InvokeContractError, // -6
    /// Failed to verify signature because signer account does not exist on
    /// chain.
    MissingAccount, // -7
    /// Failed to verify signature because data was malformed.
    MalformedData, // -8
    /// Failed signature verification: Invalid signature.
    WrongSignature, // -9
    /// Failed signature verification: A different nonce is expected.
    NonceMismatch, // -10
    /// Failed signature verification: Signature was intended for a different
    /// contract.
    WrongContract, // -11
    /// Failed signature verification: Signature was intended for a different
    /// entry_point.
    WrongEntryPoint, // -12
    /// Failed signature verification: Signature is expired.
    Expired, // -13
    /// Token owner address is blacklisted.
    Blacklisted, // -14
    /// Account address has no canonical address.
    NoCanonicalAddress, // -15
    /// Upgrade failed because the new module does not exist.
    FailedUpgradeMissingModule, // -16
    /// Upgrade failed because the new module does not contain a contract with a
    /// matching name.
    FailedUpgradeMissingContract, // -17
    /// Upgrade failed because the smart contract version of the module is not
    /// supported.
    FailedUpgradeUnsupportedModuleVersion, // -18
    /// Contract is paused.
    Paused, // -19
    /// Failed to revoke role because it was not granted in the first place.
    RoleWasNotGranted, // -20
    /// Failed to grant role because it was granted already in the first place.
    RoleWasAlreadyGranted, // -21
}

pub type ContractError = Cis2Error<CustomContractError>;

pub type ContractResult<A> = Result<A, ContractError>;

/// Mapping errors related to contract upgrades to CustomContractError.
impl From<UpgradeError> for CustomContractError {
    #[inline(always)]
    fn from(ue: UpgradeError) -> Self {
        match ue {
            UpgradeError::MissingModule => Self::FailedUpgradeMissingModule,
            UpgradeError::MissingContract => Self::FailedUpgradeMissingContract,
            UpgradeError::UnsupportedModuleVersion => Self::FailedUpgradeUnsupportedModuleVersion,
        }
    }
}

/// Mapping account signature error to CustomContractError
impl From<CheckAccountSignatureError> for CustomContractError {
    fn from(e: CheckAccountSignatureError) -> Self {
        match e {
            CheckAccountSignatureError::MissingAccount => Self::MissingAccount,
            CheckAccountSignatureError::MalformedData => Self::MalformedData,
        }
    }
}

/// Mapping the logging errors to CustomContractError.
impl From<LogError> for CustomContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

/// Mapping errors related to contract invocations to CustomContractError.
impl<T> From<CallContractError<T>> for CustomContractError {
    fn from(_cce: CallContractError<T>) -> Self { Self::InvokeContractError }
}

/// Mapping CustomContractError to ContractError
impl From<CustomContractError> for ContractError {
    fn from(c: CustomContractError) -> Self { Cis2Error::Custom(c) }
}

impl State {
    /// Construct a state with no tokens
    fn empty(state_builder: &mut StateBuilder, mint_airdrop: ContractTokenAmount) -> Self {
        State {
            state: state_builder.new_map(),
            tokens: state_builder.new_map(),
            implementors: state_builder.new_map(),
            nonces_registry: state_builder.new_map(),
            mint_airdrop,
            blacklist: state_builder.new_set(),
            paused: false,
            roles: state_builder.new_map(),
        }
    }

    /// Mints an amount of tokens with a given address as the owner.
    /// The metadataURL for the given token_id is added to the state only
    /// if the token_id is being minted or created for the first time.
    /// Otherwise, the metadataURL provided in the input parameter is ignored.
    fn mint(
        &mut self,
        token_id: &ContractTokenId,
        metadata_url: &MetadataUrl,
        owner: &Address,
        mint_airdrop: ContractTokenAmount,
        state_builder: &mut StateBuilder,
    ) -> MetadataUrl {
        let token_metadata = self.tokens.get(token_id).map(|x| x.to_owned());
        if token_metadata.is_none() {
            let _ = self.tokens.insert(*token_id, metadata_url.to_owned());
        }

        let mut owner_state =
            self.state.entry(*owner).or_insert_with(|| AddressState::empty(state_builder));
        let mut owner_balance = owner_state.balances.entry(*token_id).or_insert(0.into());
        *owner_balance += mint_airdrop;

        if let Some(token_metadata) = token_metadata {
            token_metadata
        } else {
            metadata_url.clone()
        }
    }

    /// Burns an amount of tokens from a given owner address.
    fn burn(
        &mut self,
        token_id: &ContractTokenId,
        amount: ContractTokenAmount,
        owner: &Address,
    ) -> ContractResult<()> {
        ensure!(self.contains_token(token_id), ContractError::InvalidTokenId);

        let mut owner_state =
            self.state.entry(*owner).occupied_or(ContractError::InsufficientFunds)?;

        let mut owner_balance = owner_state.balances.entry(*token_id).or_insert(0.into());
        ensure!(*owner_balance >= amount, ContractError::InsufficientFunds);
        *owner_balance -= amount;

        Ok(())
    }

    /// Check that the token ID currently exists in this contract.
    #[inline(always)]
    fn contains_token(&self, token_id: &ContractTokenId) -> bool {
        self.tokens.get(token_id).map(|x| x.to_owned()).is_some()
    }

    /// Get the current balance of a given token id for a given address.
    /// Results in an error if the token id does not exist in the state.
    fn balance(
        &self,
        token_id: &ContractTokenId,
        address: &Address,
    ) -> ContractResult<ContractTokenAmount> {
        ensure!(self.contains_token(token_id), ContractError::InvalidTokenId);
        let balance = self.state.get(address).map_or(0.into(), |address_state| {
            address_state.balances.get(token_id).map_or(0.into(), |x| *x)
        });
        Ok(balance)
    }

    /// Check if an address is an operator of a given owner address.
    fn is_operator(&self, address: &Address, owner: &Address) -> bool {
        self.state
            .get(owner)
            .map(|address_state| address_state.operators.contains(address))
            .unwrap_or(false)
    }

    /// Update the state with a transfer.
    /// Results in an error if the token id does not exist in the state or if
    /// the from address have insufficient tokens to do the transfer.
    fn transfer(
        &mut self,
        token_id: &ContractTokenId,
        amount: ContractTokenAmount,
        from: &Address,
        to: &Address,
        state_builder: &mut StateBuilder,
    ) -> ContractResult<()> {
        ensure!(self.contains_token(token_id), ContractError::InvalidTokenId);
        // A zero transfer does not modify the state.
        if amount == 0.into() {
            return Ok(());
        }

        // Get the `from` state and balance, if not present it will fail since the
        // balance is interpreted as 0 and the transfer amount must be more than
        // 0 at this point.
        {
            let mut from_address_state =
                self.state.entry(*from).occupied_or(ContractError::InsufficientFunds)?;
            let mut from_balance = from_address_state
                .balances
                .entry(*token_id)
                .occupied_or(ContractError::InsufficientFunds)?;
            ensure!(*from_balance >= amount, ContractError::InsufficientFunds);
            *from_balance -= amount;
        }

        let mut to_address_state =
            self.state.entry(*to).or_insert_with(|| AddressState::empty(state_builder));
        let mut to_address_balance = to_address_state.balances.entry(*token_id).or_insert(0.into());
        *to_address_balance += amount;

        Ok(())
    }

    /// Update the state adding a new operator for a given address.
    /// Succeeds even if the `operator` is already an operator for the
    /// `address`.
    fn add_operator(
        &mut self,
        owner: &Address,
        operator: &Address,
        state_builder: &mut StateBuilder,
    ) {
        let mut owner_state =
            self.state.entry(*owner).or_insert_with(|| AddressState::empty(state_builder));
        owner_state.operators.insert(*operator);
    }

    /// Update the state removing an operator for a given address.
    /// Succeeds even if the `operator` is not an operator for the `address`.
    fn remove_operator(&mut self, owner: &Address, operator: &Address) {
        self.state.entry(*owner).and_modify(|address_state| {
            address_state.operators.remove(operator);
        });
    }

    /// Update the state adding a new address to the blacklist.
    /// Succeeds even if the `address` is already in the blacklist.
    fn add_blacklist(&mut self, address: Address) { self.blacklist.insert(address); }

    /// Update the state removing an address from the blacklist.
    /// Succeeds even if the `address` is not in the list.
    fn remove_blacklist(&mut self, address: &Address) { self.blacklist.remove(address); }

    /// Check if state contains any implementors for a given standard.
    fn have_implementors(&self, std_id: &StandardIdentifierOwned) -> SupportResult {
        if let Some(addresses) = self.implementors.get(std_id) {
            SupportResult::SupportBy(addresses.to_vec())
        } else {
            SupportResult::NoSupport
        }
    }

    /// Set implementors for a given standard.
    fn set_implementors(
        &mut self,
        std_id: StandardIdentifierOwned,
        implementors: Vec<ContractAddress>,
    ) {
        let _ = self.implementors.insert(std_id, implementors);
    }

    /// Grant role to an address.
    fn grant_role(&mut self, account: &Address, role: Roles, state_builder: &mut StateBuilder) {
        self.roles.entry(*account).or_insert_with(|| AddressRoleState {
            roles: state_builder.new_set(),
        });

        self.roles.entry(*account).and_modify(|entry| {
            entry.roles.insert(role);
        });
    }

    /// Revoke role from an address.
    fn revoke_role(&mut self, account: &Address, role: Roles) {
        self.roles.entry(*account).and_modify(|entry| {
            entry.roles.remove(&role);
        });
    }

    /// Check if an address has an role.
    fn has_role(&self, account: &Address, role: Roles) -> bool {
        match self.roles.get(account) {
            None => false,
            Some(roles) => roles.roles.contains(&role),
        }
    }
}

/// Convert the address into its canonical account address (in case it is an
/// account address). Account addresses on Concordium have account aliases. We
/// call the alias 0 for every account the canonical account address.
/// https://developer.concordium.software/en/mainnet/net/references/transactions.html#account-aliases
fn get_canonical_address(address: Address) -> ContractResult<Address> {
    let canonical_address = match address {
        Address::Account(account) => {
            Address::Account(account.get_alias(0).ok_or(CustomContractError::NoCanonicalAddress)?)
        }
        Address::Contract(contract) => Address::Contract(contract),
    };
    Ok(canonical_address)
}

// Contract functions

/// Initialize contract instance with no token types.
#[init(contract = "cis2_multi", parameter = "ContractTokenAmount", event = "Event", enable_logger)]
fn contract_init(
    ctx: &InitContext,
    state_builder: &mut StateBuilder,
    logger: &mut impl HasLogger,
) -> InitResult<State> {
    // Parse the parameter.
    let mint_airdrop: ContractTokenAmount = ctx.parameter_cursor().get()?;

    // Construct the initial contract state.
    let mut state = State::empty(state_builder, mint_airdrop);

    // Get the instantiater of this contract instance.
    let invoker = Address::Account(ctx.init_origin());

    // Grant ADMIN role.
    state.grant_role(&invoker, Roles::ADMIN, state_builder);
    logger.log(&Event::GrantRole(GrantRoleEvent {
        address: invoker,
        role:    Roles::ADMIN,
    }))?;

    Ok(state)
}

#[derive(Serialize, SchemaType, PartialEq, Eq, Debug)]
pub struct ViewAddressState {
    pub balances:  Vec<(ContractTokenId, ContractTokenAmount)>,
    pub operators: Vec<Address>,
}

#[derive(Serialize, SchemaType, PartialEq, Eq)]
pub struct ViewState {
    pub state:           Vec<(Address, ViewAddressState)>,
    pub tokens:          Vec<ContractTokenId>,
    pub nonces_registry: Vec<(AccountAddress, u64)>,
    pub blacklist:       Vec<Address>,
    pub roles:           Vec<(Address, Vec<Roles>)>,
    pub mint_airdrop:    ContractTokenAmount,
    pub paused:          bool,
    pub implementors:    Vec<(StandardIdentifierOwned, Vec<ContractAddress>)>,
}

/// View function for testing. This reports on the entire state of the contract
/// for testing purposes.
#[receive(contract = "cis2_multi", name = "view", return_value = "ViewState")]
fn contract_view(_ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<ViewState> {
    let state = host.state();

    let contract_state = state
        .state
        .iter()
        .map(|(key, value)| {
            let mut balances = Vec::new();
            let mut operators = Vec::new();
            for (token_id, amount) in value.balances.iter() {
                balances.push((*token_id, *amount));
            }
            for operator in value.operators.iter() {
                operators.push(*operator);
            }
            (*key, ViewAddressState {
                balances,
                operators,
            })
        })
        .collect();

    let tokens = state.tokens.iter().map(|a| *a.0).collect();
    let nonces_registry = state.nonces_registry.iter().map(|(a, b)| (*a, *b)).collect();
    let blacklist = state.blacklist.iter().map(|a| *a).collect();
    let roles: Vec<(Address, Vec<Roles>)> = state
        .roles
        .iter()
        .map(|(key, value)| {
            let mut roles_vec = Vec::new();
            for role in value.roles.iter() {
                roles_vec.push(*role);
            }
            (*key, roles_vec)
        })
        .collect();

    let implementors: Vec<(StandardIdentifierOwned, Vec<ContractAddress>)> = state
        .implementors
        .iter()
        .map(|(key, value)| {
            let mut implementors = Vec::new();
            for test in value.iter() {
                implementors.push(*test);
            }

            ((*key).clone(), implementors)
        })
        .collect();

    Ok(ViewState {
        state: contract_state,
        tokens,
        nonces_registry,
        blacklist,
        roles,
        implementors,
        mint_airdrop: host.state().mint_airdrop,
        paused: host.state().paused,
    })
}

/// Internal `mint/permit` helper function. Invokes the `mint`
/// function of the state. Logs a `Mint` event.
/// The function assumes that the mint is authorized.
fn mint(
    params: &MintParams,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    let to_address = params.to.address();

    let is_blacklisted = host.state().blacklist.contains(&get_canonical_address(to_address)?);

    // Check token owner is not blacklisted.
    ensure!(!is_blacklisted, CustomContractError::Blacklisted.into());

    // Check that contract is not paused.
    ensure!(!host.state().paused, CustomContractError::Paused.into());

    let (state, builder) = host.state_and_builder();

    // Mint the token in the state.
    let token_metadata = state.mint(
        &params.token_id,
        &params.metadata_url,
        &to_address,
        state.mint_airdrop,
        builder,
    );

    // Event for minted token.
    logger.log(&Cis2Event::Mint(MintEvent {
        token_id: params.token_id,
        amount:   state.mint_airdrop,
        owner:    to_address,
    }))?;

    // Metadata URL for the token.
    logger.log(&Cis2Event::TokenMetadata::<_, ContractTokenAmount>(TokenMetadataEvent {
        token_id:     params.token_id,
        metadata_url: token_metadata,
    }))?;

    Ok(())
}

/// Mint/Airdrops the fixed amount of `MINT_AIRDROP` of new tokens to the
/// `owner` address. ATTENTION: Can be called by anyone. You should add your
/// custom access control to this function and the permit function.
///
/// Logs a `Mint` and a `TokenMetadata` event for each token.
/// The metadata_url in the input parameter of the token is ignored except for
/// the first time a token_id is minted.
///
/// It rejects if:
/// - Fails to parse parameter.
/// - The token receiver is blacklisted.
/// - The contract is paused.
/// - Fails to log Mint event.
/// - Fails to log TokenMetadata event.
#[receive(
    contract = "cis2_multi",
    name = "mint",
    parameter = "MintParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_mint(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let params: MintParams = ctx.parameter_cursor().get()?;

    // // Get the sender who invoked this contract function. (comment in if you want
    // // only the MINTER role to mint tokens)
    // let sender = ctx.sender();

    // // Check that only the MINTER is authorized to mint an address. (comment in
    // // if you want only the MINTER role to mint tokens)
    // ensure!(host.state().has_role(&sender, Roles::MINTER),
    // ContractError::Unauthorized);

    mint(&params, host, logger)?;

    // If the receiver is a contract: invoke the receive hook function.
    if let Receiver::Contract(address, function) = params.to {
        let parameter = OnReceivingCis2Params {
            token_id: params.token_id,
            amount:   host.state.mint_airdrop,
            from:     Address::from(address),
            data:     params.data,
        };
        host.invoke_contract(&address, &parameter, function.as_entrypoint_name(), Amount::zero())?;
    }

    Ok(())
}

/// Internal `burn/permit` helper function. Invokes the `burn`
/// function of the state. Logs a `Burn` event.
/// The function assumes that the burn is authorized.
fn burn(
    params: BurnParams,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Check that contract is not paused.
    ensure!(!host.state().paused, CustomContractError::Paused.into());

    let is_blacklisted = host.state().blacklist.contains(&get_canonical_address(params.owner)?);

    // Check token owner is not blacklisted.
    ensure!(!is_blacklisted, CustomContractError::Blacklisted.into());

    // Burn the token in the state.
    host.state_mut().burn(&params.token_id, params.amount, &params.owner)?;

    // Event for burned tokens.
    logger.log(&Cis2Event::Burn(BurnEvent {
        token_id: params.token_id,
        amount:   params.amount,
        owner:    params.owner,
    }))?;

    Ok(())
}

/// Burns an amount of tokens from the
/// `owner` address.
///
/// Logs a `Burn` event for each token.
///
/// It rejects if:
/// - Fails to parse parameter.
/// - The sender is not the token owner or an operator of the token owner.
/// - The owner is blacklisted.
/// - The contract is paused.
/// - The token owner owns an insufficient token amount to burn from.
/// - Fails to log Burn event.
#[receive(
    contract = "cis2_multi",
    name = "burn",
    parameter = "BurnParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_burn(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let params: BurnParams = ctx.parameter_cursor().get()?;

    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    // Authenticate the sender for the token burns.
    ensure!(
        params.owner == sender || host.state().is_operator(&sender, &params.owner),
        ContractError::Unauthorized
    );

    burn(params, host, logger)?;

    Ok(())
}

type TransferParameter = TransferParams<ContractTokenId, ContractTokenAmount>;

/// Internal `transfer/permit` helper function. Invokes the `transfer`
/// function of the state. Logs a `Transfer` event and invokes a receive hook
/// function. The function assumes that the transfer is authorized.
fn transfer(
    transfer: concordium_cis2::Transfer<ContractTokenId, ContractTokenAmount>,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    let to_address = transfer.to.address();

    // Check token receiver is not blacklisted.
    ensure!(
        !host.state().blacklist.contains(&get_canonical_address(to_address)?),
        CustomContractError::Blacklisted.into()
    );

    // Check token owner is not blacklisted.
    ensure!(
        !host.state().blacklist.contains(&get_canonical_address(transfer.from)?),
        CustomContractError::Blacklisted.into()
    );

    // Check that contract is not paused.
    ensure!(!host.state().paused, CustomContractError::Paused.into());

    let (state, builder) = host.state_and_builder();

    // Update the contract state
    state.transfer(&transfer.token_id, transfer.amount, &transfer.from, &to_address, builder)?;

    // Log transfer event
    logger.log(&Cis2Event::Transfer(TransferEvent {
        token_id: transfer.token_id,
        amount:   transfer.amount,
        from:     transfer.from,
        to:       to_address,
    }))?;

    // If the receiver is a contract: invoke the receive hook function.
    if let Receiver::Contract(address, function) = transfer.to {
        let parameter = OnReceivingCis2Params {
            token_id: transfer.token_id,
            amount:   transfer.amount,
            from:     transfer.from,
            data:     transfer.data,
        };
        host.invoke_contract(&address, &parameter, function.as_entrypoint_name(), Amount::zero())?;
    }

    Ok(())
}

/// Execute a list of token transfers, in the order of the list.
///
/// Logs a `Transfer` event and invokes a receive hook function for every
/// transfer in the list.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Either the from or to addresses are blacklisted.
/// - The contract is paused.
/// - Any of the transfers fail to be executed, which could be if:
///     - The `token_id` does not exist.
///     - The sender is not the owner of the token, or an operator for this
///       specific `token_id` and `from` address.
///     - The token is not owned by the `from`.
/// - Fails to log event.
/// - Any of the receive hook function calls rejects.
#[receive(
    contract = "cis2_multi",
    name = "transfer",
    parameter = "TransferParameter",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_transfer(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let TransferParams(transfers): TransferParameter = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    for transfer_entry in transfers {
        // Authenticate the sender for this transfer
        ensure!(
            transfer_entry.from == sender
                || host.state().is_operator(&sender, &transfer_entry.from),
            ContractError::Unauthorized
        );

        transfer(transfer_entry, host, logger)?;
    }
    Ok(())
}

/// Helper function that can be invoked at the front-end to serialize the
/// `PermitMessage` before signing it in the wallet.
#[receive(contract = "cis2_multi", name = "serializationHelper", parameter = "PermitMessage")]
fn contract_serialization_helper(_ctx: &ReceiveContext, _host: &Host<State>) -> ContractResult<()> {
    Ok(())
}

/// Helper function to calculate the `message_hash`.
#[receive(
    contract = "cis2_multi",
    name = "viewMessageHash",
    parameter = "PermitParam",
    return_value = "[u8;32]",
    error = "ContractError",
    crypto_primitives,
    mutable
)]
fn contract_view_message_hash(
    ctx: &ReceiveContext,
    _host: &mut Host<State>,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<[u8; 32]> {
    // Parse the parameter.
    let mut cursor = ctx.parameter_cursor();
    // The input parameter is `PermitParam` but we only read the initial part of it
    // with `PermitParamPartial`. I.e. we read the `signature` and the
    // `signer`, but not the `message` here.
    let param: PermitParamPartial = cursor.get()?;

    // The input parameter is `PermitParam` but we have only read the initial part
    // of it with `PermitParamPartial` so far. We read in the `message` now.
    // `(cursor.size() - cursor.cursor_position()` is the length of the message in
    // bytes.
    let mut message_bytes = vec![0; (cursor.size() - cursor.cursor_position()) as usize];

    cursor.read_exact(&mut message_bytes)?;

    // The message signed in the Concordium browser wallet is prepended with the
    // `account` address and 8 zero bytes. Accounts in the Concordium browser wallet
    // can either sign a regular transaction (in that case the prepend is
    // `account` address and the nonce of the account which is by design >= 1)
    // or sign a message (in that case the prepend is `account` address and 8 zero
    // bytes). Hence, the 8 zero bytes ensure that the user does not accidentally
    // sign a transaction. The account nonce is of type u64 (8 bytes).
    let mut msg_prepend = [0; 32 + 8];
    // Prepend the `account` address of the signer.
    msg_prepend[0..32].copy_from_slice(param.signer.as_ref());
    // Prepend 8 zero bytes.
    msg_prepend[32..40].copy_from_slice(&[0u8; 8]);
    // Calculate the message hash.
    let message_hash =
        crypto_primitives.hash_sha2_256(&[&msg_prepend[0..40], &message_bytes].concat()).0;

    Ok(message_hash)
}

/// Verify an ed25519 signature and allow the transfer of tokens or update of an
/// operator.
///
/// In case of a `transfer` action:
/// Logs a `Transfer` event and invokes a receive hook function for the
/// transfer.
///
/// In case of a `updateOperator` action:
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - A different nonce is expected.
/// - The signature was intended for a different contract.
/// - The signature was intended for a different `entry_point`.
/// - The signature is expired.
/// - The signature can not be validated.
/// - Fails to log event.
/// - In case of a `transfer` action: it fails to be executed, which could be
///   if:
///     - The `token_id` does not exist.
///     - The token is not owned by the `from` address.
///     - The receive hook function call rejects.
#[receive(
    contract = "cis2_multi",
    name = "permit",
    parameter = "PermitParam",
    error = "ContractError",
    crypto_primitives,
    mutable,
    enable_logger
)]
fn contract_permit(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> ContractResult<()> {
    // Parse the parameter.
    let param: PermitParam = ctx.parameter_cursor().get()?;

    // Update the nonce.
    let mut entry = host.state_mut().nonces_registry.entry(param.signer).or_insert_with(|| 0);

    // Get the current nonce.
    let nonce = *entry;
    // Bump nonce.
    *entry += 1;
    drop(entry);

    let message = param.message;

    // Check the nonce to prevent replay attacks.
    ensure_eq!(message.nonce, nonce, CustomContractError::NonceMismatch.into());

    // Check that the signature was intended for this contract.
    ensure_eq!(
        message.contract_address,
        ctx.self_address(),
        CustomContractError::WrongContract.into()
    );

    // Check signature is not expired.
    ensure!(message.timestamp > ctx.metadata().slot_time(), CustomContractError::Expired.into());

    let message_hash = contract_view_message_hash(ctx, host, crypto_primitives)?;

    // Check signature.
    let valid_signature =
        host.check_account_signature(param.signer, &param.signature, &message_hash)?;
    ensure!(valid_signature, CustomContractError::WrongSignature.into());

    match message.entry_point.as_entrypoint_name() {
        TRANSFER_ENTRYPOINT => {
            // Transfer the tokens.
            let TransferParams(transfers): TransferParameter = from_bytes(&message.payload)?;

            for transfer_entry in transfers {
                // Authenticate the signer for this transfer
                ensure!(
                    transfer_entry.from.matches_account(&param.signer)
                        || host
                            .state()
                            .is_operator(&Address::from(param.signer), &transfer_entry.from),
                    ContractError::Unauthorized
                );

                transfer(transfer_entry, host, logger)?
            }
        }
        UPDATE_OPERATOR_ENTRYPOINT => {
            // Update the operator.
            let UpdateOperatorParams(updates): UpdateOperatorParams = from_bytes(&message.payload)?;

            let (state, builder) = host.state_and_builder();

            for update in updates {
                update_operator(
                    update.update,
                    concordium_std::Address::Account(param.signer),
                    update.operator,
                    state,
                    builder,
                    logger,
                )?;
            }
        }
        MINT_ENTRYPOINT => {
            // Mint tokens.
            // ATTENTION: Can be called by anyone. You should add your
            // custom access control here.
            let params: MintParams = from_bytes(&message.payload)?;

            // // Check that only the MINTER can authorize to mint. (comment in if you want
            // // only the MINTER role having the authorization to mint)
            // ensure!(
            //     host.state().has_role(&Address::from(param.signer), Roles::MINTER),
            //     ContractError::Unauthorized
            // );

            mint(&params, host, logger)?;
        }
        BURN_ENTRYPOINT => {
            // Burn tokens.
            let params: BurnParams = from_bytes(&message.payload)?;

            // Authenticate the sender for the token burns.
            ensure!(
                params.owner.matches_account(&param.signer)
                    || host.state().is_operator(&Address::from(param.signer), &params.owner),
                ContractError::Unauthorized
            );

            burn(params, host, logger)?;
        }
        _ => {
            bail!(CustomContractError::WrongEntryPoint.into())
        }
    }

    // Log the nonce event.
    logger.log(&Event::Nonce(NonceEvent {
        nonce,
        account: param.signer,
    }))?;

    Ok(())
}

/// Internal `updateOperator/permit` helper function. Invokes the
/// `add_operator/remove_operator` function of the state.
/// Logs a `UpdateOperator` event. The function assumes that the sender is
/// authorized to do the `updateOperator` action.
fn update_operator(
    update: OperatorUpdate,
    sender: Address,
    operator: Address,
    state: &mut State,
    builder: &mut StateBuilder,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Check that contract is not paused.
    ensure!(!state.paused, CustomContractError::Paused.into());

    // Update the operator in the state.
    match update {
        OperatorUpdate::Add => state.add_operator(&sender, &operator, builder),
        OperatorUpdate::Remove => state.remove_operator(&sender, &operator),
    }

    // Log the appropriate event
    logger.log(&Cis2Event::<ContractTokenId, ContractTokenAmount>::UpdateOperator(
        UpdateOperatorEvent {
            owner: sender,
            operator,
            update,
        },
    ))?;

    Ok(())
}

/// Enable or disable addresses as operators of the sender address.
/// Logs an `UpdateOperator` event.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Fails to log event.
#[receive(
    contract = "cis2_multi",
    name = "updateOperator",
    parameter = "UpdateOperatorParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_update_operator(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let UpdateOperatorParams(params) = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();
    let (state, builder) = host.state_and_builder();
    for param in params {
        update_operator(param.update, sender, param.operator, state, builder, logger)?;
    }
    Ok(())
}

/// Parameter type for the CIS-2 function `balanceOf` specialized to the subset
/// of TokenIDs used by this contract.
pub type ContractBalanceOfQueryParams = BalanceOfQueryParams<ContractTokenId>;

/// Response type for the CIS-2 function `balanceOf` specialized to the subset
/// of TokenAmounts used by this contract.
pub type ContractBalanceOfQueryResponse = BalanceOfQueryResponse<ContractTokenAmount>;

/// Get the balance of given token IDs and addresses.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "cis2_multi",
    name = "balanceOf",
    parameter = "ContractBalanceOfQueryParams",
    return_value = "ContractBalanceOfQueryResponse",
    error = "ContractError"
)]
fn contract_balance_of(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<ContractBalanceOfQueryResponse> {
    // Parse the parameter.
    let params: ContractBalanceOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for balance.
        let amount = host.state().balance(&query.token_id, &query.address)?;
        response.push(amount);
    }
    let result = ContractBalanceOfQueryResponse::from(response);
    Ok(result)
}

/// Takes a list of queries. Each query is an owner address and some address to
/// check as an operator of the owner address.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_multi",
    name = "operatorOf",
    parameter = "OperatorOfQueryParams",
    return_value = "OperatorOfQueryResponse",
    error = "ContractError"
)]
fn contract_operator_of(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<OperatorOfQueryResponse> {
    // Parse the parameter.
    let params: OperatorOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for address being an operator of owner.
        let is_operator = host.state().is_operator(&query.address, &query.owner);
        response.push(is_operator);
    }
    let result = OperatorOfQueryResponse::from(response);
    Ok(result)
}

/// The parameter type for the contract functions `isBlacklisted`.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct VecOfAddresses {
    /// List of queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<Address>,
}

/// Takes a list of queries. Each query contains an address which is checked if
/// that address is blacklisted.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_multi",
    name = "isBlacklisted",
    parameter = "VecOfAddresses",
    return_value = "Vec<bool>",
    error = "ContractError"
)]
fn contract_is_blacklisted(ctx: &ReceiveContext, host: &Host<State>) -> ContractResult<Vec<bool>> {
    // Parse the parameter.
    let params: VecOfAddresses = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for address in params.queries {
        // Query the state if address is blacklisted.
        let is_blacklisted = host.state().blacklist.contains(&get_canonical_address(address)?);
        response.push(is_blacklisted);
    }
    Ok(response)
}

/// Response type for the function `publicKeyOf`.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct PublicKeyOfQueryResponse(
    #[concordium(size_length = 2)] pub Vec<Option<AccountPublicKeys>>,
);

impl From<Vec<Option<AccountPublicKeys>>> for PublicKeyOfQueryResponse {
    fn from(results: concordium_std::Vec<Option<AccountPublicKeys>>) -> Self {
        PublicKeyOfQueryResponse(results)
    }
}

/// The parameter type for the contract functions `publicKeyOf/noneOf`. A query
/// for the public key/nonce of a given account.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct VecOfAccountAddresses {
    /// List of queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<AccountAddress>,
}

/// Get the public keys of accounts. `None` is returned if the account does not
/// exist on chain.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_multi",
    name = "publicKeyOf",
    parameter = "VecOfAccountAddresses",
    return_value = "PublicKeyOfQueryResponse",
    error = "ContractError"
)]
fn contract_public_key_of(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<PublicKeyOfQueryResponse> {
    // Parse the parameter.
    let params: VecOfAccountAddresses = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response: Vec<Option<AccountPublicKeys>> = Vec::with_capacity(params.queries.len());
    for account in params.queries {
        // Query the public_key.
        let public_keys = host.account_public_keys(account).ok();

        response.push(public_keys);
    }
    let result = PublicKeyOfQueryResponse::from(response);
    Ok(result)
}

/// Response type for the function `nonceOf`.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct NonceOfQueryResponse(#[concordium(size_length = 2)] pub Vec<u64>);

impl From<Vec<u64>> for NonceOfQueryResponse {
    fn from(results: concordium_std::Vec<u64>) -> Self { NonceOfQueryResponse(results) }
}

/// Get the nonces of accounts.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_multi",
    name = "nonceOf",
    parameter = "VecOfAccountAddresses",
    return_value = "NonceOfQueryResponse",
    error = "ContractError"
)]
fn contract_nonce_of(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<NonceOfQueryResponse> {
    // Parse the parameter.
    let params: VecOfAccountAddresses = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response: Vec<u64> = Vec::with_capacity(params.queries.len());
    for account in params.queries {
        // Query the next nonce.
        let nonce = host.state().nonces_registry.get(&account).map(|nonce| *nonce).unwrap_or(0);

        response.push(nonce);
    }
    Ok(NonceOfQueryResponse::from(response))
}

/// Parameter type for the CIS-2 function `tokenMetadata` specialized to the
/// subset of TokenIDs used by this contract.
type ContractTokenMetadataQueryParams = TokenMetadataQueryParams<ContractTokenId>;

/// Get the token metadata URLs and checksums given a list of token IDs.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Any of the queried `token_id` does not exist.
#[receive(
    contract = "cis2_multi",
    name = "tokenMetadata",
    parameter = "ContractTokenMetadataQueryParams",
    return_value = "TokenMetadataQueryResponse",
    error = "ContractError"
)]
fn contract_token_metadata(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<TokenMetadataQueryResponse> {
    // Parse the parameter.
    let params: ContractTokenMetadataQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for token_id in params.queries {
        let metadata_url = match host.state().tokens.get(&token_id) {
            Some(metadata_url) => metadata_url.clone(),
            None => bail!(ContractError::InvalidTokenId),
        };
        response.push(metadata_url);
    }
    let result = TokenMetadataQueryResponse::from(response);
    Ok(result)
}

/// Example of implementing a function for receiving transfers.
/// It is not required to be implemented by the token contract, but is required
/// to implement such a function by any contract which should receive CIS2
/// tokens.
///
/// This contract function is called when a token is transferred to an instance
/// of this contract and should only be called by a contract implementing CIS2.
/// The parameter include a `data` field which can be used to
/// implement some arbitrary functionality. In this example we choose not to use
/// it, and define the function to forward any transfers to the owner of the
/// contract instance.
///
/// Note: The name of this function is not part the CIS2 standard, and a
/// contract can have multiple functions for receiving tokens.
///
/// It rejects if:
/// - Sender is not a contract.
/// - It fails to parse the parameter.
/// - Contract name part of the parameter is invalid.
/// - Calling back `transfer` to sender contract rejects.
#[receive(contract = "cis2_multi", name = "onReceivingCIS2", error = "ContractError")]
fn contract_on_cis2_received(ctx: &ReceiveContext, host: &Host<State>) -> ContractResult<()> {
    // Ensure the sender is a contract.
    let sender = if let Address::Contract(contract) = ctx.sender() {
        contract
    } else {
        bail!(CustomContractError::ContractOnly.into())
    };

    // Parse the parameter.
    let params: OnReceivingCis2Params<ContractTokenId, ContractTokenAmount> =
        ctx.parameter_cursor().get()?;

    // Build the transfer from this contract to the contract owner.
    let transfer = Transfer {
        token_id: params.token_id,
        amount:   params.amount,
        from:     Address::Contract(ctx.self_address()),
        to:       Receiver::from_account(ctx.owner()),
        data:     AdditionalData::empty(),
    };

    let parameter = TransferParams::from(vec![transfer]);

    // Send back a transfer
    host.invoke_contract_read_only(
        &sender,
        &parameter,
        EntrypointName::new_unchecked("transfer"),
        Amount::zero(),
    )?;
    Ok(())
}

/// Get the supported standards or addresses for a implementation given list of
/// standard identifiers.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_multi",
    name = "supports",
    parameter = "SupportsQueryParams",
    return_value = "SupportsQueryResponse",
    error = "ContractError"
)]
fn contract_supports(
    ctx: &ReceiveContext,
    host: &Host<State>,
) -> ContractResult<SupportsQueryResponse> {
    // Parse the parameter.
    let params: SupportsQueryParams = ctx.parameter_cursor().get()?;

    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for std_id in params.queries {
        if SUPPORTS_STANDARDS.contains(&std_id.as_standard_identifier()) {
            response.push(SupportResult::Support);
        } else {
            response.push(host.state().have_implementors(&std_id));
        }
    }
    let result = SupportsQueryResponse::from(response);
    Ok(result)
}

/// Get the entrypoints supported by the `permit` function given a
/// list of entrypoints.
///
/// It rejects if:
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_multi",
    name = "supportsPermit",
    parameter = "SupportsPermitQueryParams",
    return_value = "SupportsQueryResponse",
    error = "ContractError"
)]
fn contract_supports_permit(
    ctx: &ReceiveContext,
    _host: &Host<State>,
) -> ContractResult<SupportsQueryResponse> {
    // Parse the parameter.
    let params: SupportsPermitQueryParams = ctx.parameter_cursor().get()?;

    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for entrypoint in params.queries {
        if SUPPORTS_PERMIT_ENTRYPOINTS.contains(&entrypoint.as_entrypoint_name()) {
            response.push(SupportResult::Support);
        } else {
            response.push(SupportResult::NoSupport);
        }
    }
    let result = SupportsQueryResponse::from(response);
    Ok(result)
}

/// Set the addresses for an implementation given a standard identifier and a
/// list of contract addresses.
///
/// It rejects if:
/// - Sender is not the owner of the contract instance.
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_multi",
    name = "setImplementors",
    parameter = "SetImplementorsParams",
    error = "ContractError",
    mutable
)]
fn contract_set_implementor(ctx: &ReceiveContext, host: &mut Host<State>) -> ContractResult<()> {
    // Authorize the sender.
    ensure!(ctx.sender().matches_account(&ctx.owner()), ContractError::Unauthorized);
    // Parse the parameter.
    let params: SetImplementorsParams = ctx.parameter_cursor().get()?;
    // Update the implementors in the state
    host.state_mut().set_implementors(params.id, params.implementors);
    Ok(())
}

/// The update to an address with respect to the blacklist.
#[derive(Debug, Serialize, Clone, Copy, SchemaType, PartialEq, Eq)]
pub enum BlacklistUpdate {
    /// Remove from blacklist.
    Remove,
    /// Add to blacklist.
    Add,
}

/// A single update of an address with respect to the blacklist.
#[derive(Debug, Serialize, Clone, SchemaType, PartialEq, Eq)]
pub struct UpdateBlacklist {
    /// The update for this address.
    pub update:  BlacklistUpdate,
    /// The address which is either added to or removed from the blacklist.
    pub address: Address,
}

/// The parameter type for the contract function `updateBlacklist`.
#[derive(Debug, Serialize, Clone, SchemaType)]
#[concordium(transparent)]
pub struct UpdateBlacklistParams(#[concordium(size_length = 2)] pub Vec<UpdateBlacklist>);

/// Add addresses or remove addresses from the blacklist.
/// Logs an `UpdateBlacklist` event.
///
/// It rejects if:
/// - Sender is not the BLACKLISTER of the contract instance.
/// - It fails to parse the parameter.
/// - Fails to log event.
#[receive(
    contract = "cis2_multi",
    name = "updateBlacklist",
    parameter = "UpdateBlacklistParams",
    error = "ContractError",
    enable_logger,
    mutable
)]
fn contract_update_blacklist(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    // Check that only the BLACKLISTER is authorized to blacklist an address.
    ensure!(host.state().has_role(&sender, Roles::BLACKLISTER), ContractError::Unauthorized);

    // Parse the parameter.
    let UpdateBlacklistParams(params) = ctx.parameter_cursor().get()?;

    for param in params {
        let canonical_address = get_canonical_address(param.address)?;

        // Add/remove address from the blacklist.
        match param.update {
            BlacklistUpdate::Add => host.state_mut().add_blacklist(canonical_address),
            BlacklistUpdate::Remove => host.state_mut().remove_blacklist(&canonical_address),
        }

        // Log the update blacklist event.
        logger.log(&Event::UpdateBlacklist(UpdateBlacklistEvent {
            address: canonical_address,
            update:  param.update,
        }))?;
    }

    Ok(())
}

/// Upgrade this smart contract instance to a new module and call optionally a
/// migration function after the upgrade.
///
/// It rejects if:
/// - Sender is not the UPGRADER of the contract instance.
/// - It fails to parse the parameter.
/// - If the ugrade fails.
/// - If the migration invoke fails.
///
/// This function is marked as `low_level`. This is **necessary** since the
/// high-level mutable functions store the state of the contract at the end of
/// execution. This conflicts with migration since the shape of the state
/// **might** be changed by the migration function. If the state is then written
/// by this function it would overwrite the state stored by the migration
/// function.
#[receive(
    contract = "cis2_multi",
    name = "upgrade",
    parameter = "UpgradeParams",
    error = "CustomContractError",
    low_level
)]
fn contract_upgrade(ctx: &ReceiveContext, host: &mut LowLevelHost) -> ContractResult<()> {
    // Read the top-level contract state.
    let state: State = host.state().read_root()?;

    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    // Check that only the UPGRADER is authorized to upgrade the contract.
    ensure!(state.has_role(&sender, Roles::UPGRADER), ContractError::Unauthorized);
    // Parse the parameter.
    let params: UpgradeParams = ctx.parameter_cursor().get()?;
    // Trigger the upgrade.
    host.upgrade(params.module)?;
    // Call the migration function if provided.
    if let Some((func, parameters)) = params.migrate {
        host.invoke_contract_raw(
            &ctx.self_address(),
            parameters.as_parameter(),
            func.as_entrypoint_name(),
            Amount::zero(),
        )?;
    }
    Ok(())
}

/// Pause/Unpause this smart contract instance by the PAUSER. The transfer,
/// updateOperator, mint, and burn functions cannot be
/// executed when the contract is paused.
///
/// It rejects if:
/// - Sender is not the PAUSER of the contract instance.
/// - It fails to parse the parameter.
#[receive(
    contract = "cis2_multi",
    name = "setPaused",
    parameter = "SetPausedParams",
    error = "CustomContractError",
    mutable
)]
fn contract_set_paused(ctx: &ReceiveContext, host: &mut Host<State>) -> ContractResult<()> {
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    // Check that only the PAUSER is authorized to pause the contract.
    ensure!(host.state().has_role(&sender, Roles::PAUSER), ContractError::Unauthorized);

    // Parse the parameter.
    let params: SetPausedParams = ctx.parameter_cursor().get()?;

    // Update the paused variable.
    host.state_mut().paused = params.paused;

    Ok(())
}

/// Add role to an address.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Sender is not the ADMIN of the contract instance.
/// - The `address` is already holding the specified role to be granted.
#[receive(
    contract = "cis2_multi",
    name = "grantRole",
    parameter = "GrantRoleParams",
    enable_logger,
    mutable
)]
fn contract_grant_role(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let params: GrantRoleParams = ctx.parameter_cursor().get()?;

    let (state, state_builder) = host.state_and_builder();

    // Get the sender who invoked this contract function.
    let sender = ctx.sender();
    // Check that only the ADMIN is authorized to grant roles.
    ensure!(state.has_role(&sender, Roles::ADMIN), ContractError::Unauthorized);

    // Check that the `address` had previously not hold the specified role.
    ensure!(
        !state.has_role(&params.address, params.role),
        CustomContractError::RoleWasAlreadyGranted.into()
    );

    // Grant role.
    state.grant_role(&params.address, params.role, state_builder);
    logger.log(&Event::GrantRole(GrantRoleEvent {
        address: params.address,
        role:    params.role,
    }))?;
    Ok(())
}

/// Revoke role from an address.
///
/// It rejects if:
/// - It fails to parse the parameter.
/// - Sender is not the ADMIN of the contract instance.
/// - The `address` is not holding the specified role to be revoked.
#[receive(
    contract = "cis2_multi",
    name = "revokeRole",
    parameter = "RevokeRoleParams",
    enable_logger,
    mutable
)]
fn contract_revoke_role(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let params: RevokeRoleParams = ctx.parameter_cursor().get()?;

    let (state, _) = host.state_and_builder();

    // Get the sender who invoked this contract function.
    let sender = ctx.sender();
    // Check that only the ADMIN is authorized to revoke roles.
    ensure!(state.has_role(&sender, Roles::ADMIN), ContractError::Unauthorized);

    // Check that the `address` had previously hold the specified role.
    ensure!(
        state.has_role(&params.address, params.role),
        CustomContractError::RoleWasNotGranted.into()
    );

    // Revoke role.
    state.revoke_role(&params.address, params.role);
    logger.log(&Event::RevokeRole(RevokeRoleEvent {
        address: params.address,
        role:    params.role,
    }))?;
    Ok(())
}
