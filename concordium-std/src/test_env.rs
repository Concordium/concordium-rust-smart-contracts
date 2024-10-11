use concordium_contracts_common::{Amount, ContractAddress, SlotTime};

use crate::{from_bytes, prims, to_bytes};

struct TestEnv;

impl TestEnv {
    pub fn set_slot_time(self, slot_time: SlotTime) -> Self {
        unsafe { prims::set_slot_time(slot_time.timestamp_millis()) };
        self
    }

    pub fn get_slot_time(self) -> SlotTime {
        unsafe { SlotTime::from_timestamp_millis(prims::get_slot_time()) }
    }

    pub fn set_receive_balance(self, balance: Amount) -> Self {
        unsafe { prims::set_receive_self_balance(balance.micro_ccd) };
        self
    }

    pub fn get_receive_balance(self) -> Amount {
        let raw_balance = unsafe { prims::get_receive_self_balance() };
        Amount::from_micro_ccd(raw_balance)
    }

    pub fn set_receive_self_address(self, address: ContractAddress) -> Self {
        let address_bytes = to_bytes(&address);
        unsafe { prims::set_receive_self_address(address_bytes.as_ptr()) };
        self
    }

    pub fn get_receive_self_address(self) -> ContractAddress {
        let mut out_bytes = [0u8; 16];
        unsafe { prims::get_receive_self_address(out_bytes.as_mut_ptr()) }
        from_bytes(&out_bytes).unwrap()
    }
}

#[cfg(feature = "internal-wasm-test")]
mod wasm_test {
    use concordium_contracts_common::{ContractAddress, Timestamp};

    use super::*;
    use crate::{claim_eq, concordium_test};

    #[concordium_test]
    fn set_get_slot_time() {
        let original = Timestamp::from_timestamp_millis(10);
        let stored = TestEnv.set_slot_time(original).get_slot_time();
        claim_eq!(original, stored)
    }

    #[concordium_test]
    fn set_get_receive_self_balance() {
        let original = Amount::from_micro_ccd(1729);
        let stored = TestEnv.set_receive_balance(original).get_receive_balance();
        claim_eq!(original, stored)
    }

    #[concordium_test]
    fn set_get_receive_self_address() {
        let original = ContractAddress::new(5040, 12);
        let stored = TestEnv.set_receive_self_address(original).get_receive_self_address();
        claim_eq!(original, stored);
    }
}
