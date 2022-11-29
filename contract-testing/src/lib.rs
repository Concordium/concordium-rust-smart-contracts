use concordium_base::base::{Energy, ExchangeRate};
use concordium_contracts_common::*;
use sha2::{Digest, Sha256};
use std::{
    collections::{
        btree_map::Entry::{Occupied, Vacant},
        BTreeMap,
    },
    path::{Path, PathBuf},
};
use wasm_chain_integration::v1::ConcordiumAllowedImports;
use wasm_transform::artifact;

pub struct Chain {
    /// The slot time viewable inside the smart contracts.
    /// An error is thrown if this is `None` and the contract tries to
    /// access it.
    slot_time:            Option<SlotTime>,
    /// Energy per microCCD.
    energy_per_micro_ccd: ExchangeRate,
    /// Accounts and info about them.
    accounts:             BTreeMap<AccountAddress, AccountInfo>,
    /// Smart contract modules.
    modules: BTreeMap<
        ModuleReference,
        artifact::Artifact<
            wasm_transform::artifact::ArtifactNamedImport,
            artifact::CompiledFunction,
        >,
    >,
}

impl Chain {
    pub fn new(slot_time: SlotTime, energy_per_micro_ccd: ExchangeRate) -> Self {
        Self {
            slot_time: Some(slot_time),
            energy_per_micro_ccd,
            accounts: BTreeMap::new(),
            modules: BTreeMap::new(),
        }
    }

    pub fn module_deploy<P: AsRef<Path>>(
        &mut self,
        sender: AccountAddress,
        module_path: P,
    ) -> Result<SuccessfulModuleDeployment, DeployModuleError> {
        // Load file
        let module = std::fs::read(module_path)?;

        // Deserialize as wasm module (artifact)
        let artifact = wasm_transform::utils::instantiate_with_metering::<
            wasm_transform::artifact::ArtifactNamedImport,
            _,
        >(
            &ConcordiumAllowedImports {
                support_upgrade: true,
            },
            &module[8..], // skip the 4 version bytes and 4 len bytes
        )
        .map_err(|e| DeployModuleError::InvalidModule(e.to_string()))?;

        // Calculate transaction fee of deployment
        let energy = Energy::from(module.len() as u64 / 10); // From: Concordium/Const/deployModuleCost.hs
        let transaction_fee = self.calculate_energy_cost(energy);

        // Try to subtract cost for account
        match self.accounts.entry(sender) {
            Vacant(_) => return Err(DeployModuleError::AccountDoesNotExist),
            Occupied(mut acc) => {
                let acc = acc.get_mut();
                if acc.balance < transaction_fee {
                    return Err(DeployModuleError::InsufficientFunds);
                }
                acc.balance -= transaction_fee;
            }
        }

        // Save the module
        let module_reference = {
            let mut hasher = Sha256::new();
            hasher.update(module);
            let hash: [u8; 32] = hasher.finalize().into();
            ModuleReference::from(hash)
        };
        self.modules.insert(module_reference, artifact);
        Ok(SuccessfulModuleDeployment {
            module_reference,
            energy,
            transaction_fee,
        })
    }

    pub fn contract_init(
        &mut self,
        _sender: AccountAddress,
        _module: ModuleReference,
        _contract_name: ContractName,
        _parameter: ContractParameter,
        _amount: Amount,
        _energy: Energy,
    ) -> Result<SuccessfulContractInit, FailedContractInteraction> {
        todo!()
    }

    /// Can we get the return value here?
    pub fn contract_update(
        &mut self,
        _sender: AccountAddress,
        _address: ContractAddress,
        _entrypoint: EntrypointName,
        _parameter: ContractParameter,
        _amount: Amount,
        _energy: Energy,
    ) -> Result<SuccessfulContractUpdate, FailedContractInteraction> {
        todo!()
    }

    /// If `None` is provided, address 0 will be used, which will have
    /// sufficient funds.
    pub fn contract_invoke(
        &mut self,
        _sender: Option<AccountAddress>,
        _address: ContractAddress,
        _entrypoint: EntrypointName,
        _parameter: ContractParameter,
        _amount: Amount,
        _energy: Option<Energy>, // Defaults to 100000 if `None`.
    ) -> Result<SuccessfulContractUpdate, FailedContractInteraction> {
        todo!()
    }

    /// Create an account. Will override existing account if already present.
    pub fn create_account(&mut self, account: AccountAddress, account_info: AccountInfo) {
        self.accounts.insert(account, account_info);
    }

    /// Creates a contract address with an index one above the highest
    /// currently used. Next call to `contract_init` will skip this
    /// address.
    pub fn create_contract_address(&mut self) -> ContractAddress { todo!() }

    pub fn set_slot_time(&mut self, slot_time: SlotTime) { self.slot_time = Some(slot_time); }

    pub fn set_energy_per_micro_ccd(&mut self, energy_per_micro_ccd: ExchangeRate) {
        self.energy_per_micro_ccd = energy_per_micro_ccd;
    }

    /// Returns the balance of an account if it exists.
    pub fn account_balance(&self, address: AccountAddress) -> Option<Amount> {
        self.accounts.get(&address).and_then(|ai| Some(ai.balance))
    }

    pub fn calculate_energy_cost(&self, energy: Energy) -> Amount {
        Amount::from_micro_ccd(
            energy.energy * self.energy_per_micro_ccd.numerator()
                / self.energy_per_micro_ccd.denominator(),
        )
    }
}

pub struct AccountInfo {
    /// The account balance. TODO: Do we need the three types of balances?
    pub balance: Amount,
    /// Optional test policies.
    policies:    Option<Policies>,
}

impl AccountInfo {
    pub fn new(balance: Amount) -> Self {
        Self {
            balance,
            policies: None,
        }
    }
}

#[derive(Debug)]
pub struct FailedContractInteraction {
    /// Energy spent.
    pub energy: Energy,
    /// Error returned.
    pub error:  ContractError,
    /// Events emitted before the interaction failed. Events from failed
    /// updates are not stored on the chain, but can be useful for
    /// debugging.
    pub events: Vec<Event>,
}

#[derive(Debug)]
pub struct ContractError(Vec<u8>);

// TODO: Can we get Eq for this when using io::Error?
// TODO: Should this also have the energy used?
#[derive(Debug)]
pub enum DeployModuleError {
    ReadFileError(std::io::Error),
    InvalidModule(String),
    InsufficientFunds,
    AccountDoesNotExist,
}

impl From<std::io::Error> for DeployModuleError {
    fn from(e: std::io::Error) -> Self { DeployModuleError::ReadFileError(e) }
}

impl ContractError {
    pub fn deserial<T: Deserial>(&self) -> Result<T, ParsingError> { todo!() }
}

#[derive(PartialEq, Eq, Debug)]
pub struct Event(String);

#[derive(PartialEq, Eq, Debug)]
pub enum ChainEvent {
    Interrupted {
        address: ContractAddress,
        events:  Vec<Event>,
    },
    Resumed {
        address: ContractAddress,
        success: bool,
    },
    Upgraded {
        address: ContractAddress,
        from:    ModuleReference,
        to:      ModuleReference,
    },
    Updated {
        address:    ContractAddress,
        contract:   OwnedContractName,
        entrypoing: OwnedEntrypointName,
        amount:     Amount,
    },
}

pub struct SuccessfulContractUpdate {
    /// Host events that occured. This includes interrupts, resumes, and
    /// upgrades.
    pub host_events:     Vec<ChainEvent>,
    pub transfers:       Vec<(AccountAddress, Amount)>,
    /// Energy used.
    pub energy:          Energy,
    /// Cost of transaction.
    pub transaction_fee: Amount,
    /// The returned value.
    pub return_value:    ContractReturnValue,
}

#[derive(Debug, PartialEq, Eq)]
pub struct SuccessfulModuleDeployment {
    pub module_reference: ModuleReference,
    pub energy:           Energy,
    /// Cost of transaction.
    pub transaction_fee:  Amount,
}

#[derive(Debug, PartialEq, Eq)]
pub struct SuccessfulContractInit {
    /// The address of the new instance.
    pub contract_address: ContractAddress,
    /// Events produced during initialization.
    pub events:           Vec<Event>,
    /// Energy used.
    pub energy:           Energy,
    /// Cost of transaction.
    pub transaction_fee:  Amount,
}

pub struct Policies;

pub struct ContractReturnValue(Vec<u8>);

#[derive(Debug, PartialEq, Eq)]
pub enum ParsingError {
    /// Thrown by `deserial` on failure.
    ParsingFailed,
}

impl ContractReturnValue {
    pub fn deserial<T: Deserial>(&self) -> Result<T, ParsingError> { todo!() }
}

pub struct ContractParameter(Vec<u8>);

impl ContractParameter {
    pub fn empty() -> Self { Self(Vec::new()) }

    pub fn from_bytes(bytes: Vec<u8>) -> Self { Self(bytes) }

    // TODO: add version with serde json
    pub fn from_typed<T: Serial>(parameter: &T) -> Self { Self(to_bytes(parameter)) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deploying_valid_module_works() {
        let mut chain = Chain::new(
            Timestamp::from_timestamp_millis(0),
            ExchangeRate::new_unchecked(10, 1),
        );
        let acc_0 = AccountAddress([0; 32]);
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(acc_0, AccountInfo::new(initial_balance));

        let res = chain
            .module_deploy(acc_0, "icecream/icecream.wasm.v1")
            .expect("Deploying valid module should work");

        assert_eq!(chain.accounts.len(), 1);
        assert_eq!(chain.modules.len(), 1);
        assert_eq!(
            chain.account_balance(acc_0),
            Some(initial_balance - res.transaction_fee)
        );
    }
}
