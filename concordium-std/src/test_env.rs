use concordium_contracts_common::{Amount, ContractAddress, SlotTime};

use crate::{prims, to_bytes};

struct TestEnv;

impl TestEnv {
    pub fn set_slot_time(self, slot_time: SlotTime) -> Self {
        unsafe { prims::set_slot_time(slot_time.timestamp_millis()) };
        self
    }

    pub fn set_receive_balance(self, balance: Amount) -> Self {
        unsafe { prims::set_receive_self_balance(balance.micro_ccd) };
        self
    }

    pub fn set_receive_self_address(self, address: ContractAddress) -> Self {
        unsafe { prims::set_receive_self_address(to_bytes(&address).as_ptr()) };
        self
    }

    pub fn set_parameter(self, param_index: u32, bytes: &[u8]) -> Self {
        unsafe { prims::set_parameter(param_index, bytes.as_ptr(), bytes.len() as u32) };
        self
    }
}

#[cfg(feature = "internal-wasm-test")]
mod wasm_test {
    use core::num::NonZeroU32;

    use concordium_contracts_common::{ContractAddress, Timestamp};

    use super::*;
    use crate::*;

    // Helper functions to get host data, as a real smart contract would
    fn extern_host() -> ExternHost<()> {
        let state_api = ExternStateApi::open();
        let state_builder = StateBuilder::open(state_api);
        ExternHost {
            state: (),
            state_builder,
        }
    }

    fn extern_chain_meta() -> ExternChainMeta { ExternChainMeta {} }

    fn external_call_response() -> ExternCallResponse {
        ExternCallResponse::new(unsafe { NonZeroU32::new_unchecked(1) })
    }

    fn receive_context() -> ReceiveContext { ExternContext::default() }

    #[concordium_test]
    fn set_get_slot_time() {
        let original = Timestamp::from_timestamp_millis(10);
        TestEnv.set_slot_time(original);
        let stored = extern_chain_meta().block_time();
        claim_eq!(original, stored)
    }

    #[concordium_test]
    fn set_get_receive_self_balance() {
        let original = Amount::from_micro_ccd(1729);
        TestEnv.set_receive_balance(original);
        let stored = extern_host().self_balance();
        claim_eq!(original, stored)
    }

    #[concordium_test]
    fn set_get_receive_self_address() {
        let original = ContractAddress::new(5040, 12);
        TestEnv.set_receive_self_address(original);
        let stored = receive_context().self_address();
        claim_eq!(original, stored);
    }

    #[concordium_test]
    fn set_get_parameter() {
        let param = vec![3u8; 7];

        TestEnv.set_parameter(0, &param);

        let mut buf = vec![0u8; 10];
        let bytes_read = external_call_response().read(&mut stored).unwrap();

        let param_size = unsafe { prims::get_parameter_size(0) };
        let bytes_written = unsafe { prims::get_parameter_section(0, buf.as_mut_ptr(), 5, 2) };

        let expected = vec![0, 0, 3, 3, 3, 3, 3, 0, 0, 0];

        claim_eq!(param_size, 7);
        claim_eq!(bytes_written, 5);
        claim_eq!(buf, expected);
    }
}
