use concordium_contracts_common::{
    AccountAddress, Amount, ContractAddress, Serial, SlotTime,
};

use crate::{prims, to_bytes};

struct TestEnv;

impl TestEnv {
    /// Set the slot time in milliseconds.
    /// The slot time represents the beginning of the smart contract's block.
    pub fn set_slot_time(self, slot_time: SlotTime) -> Self {
        unsafe { prims::set_slot_time(slot_time.timestamp_millis()) };
        self
    }

    /// Sets the current balance of this smart contract
    pub fn set_receive_balance(self, balance: Amount) -> Self {
        unsafe { prims::set_receive_self_balance(balance.micro_ccd) };
        self
    }

    /// Sets the address of this smart contract
    pub fn set_receive_self_address(self, address: ContractAddress) -> Self {
        unsafe { prims::set_receive_self_address(to_bytes(&address).as_ptr()) };
        self
    }

    /// Sets parameter with `param_index` of the smart contract to the given
    /// value.
    pub fn set_parameter(self, param_index: u32, bytes: &[u8]) -> Self {
        unsafe { prims::set_parameter(param_index, bytes.as_ptr(), bytes.len() as u32) };
        self
    }

    /// Gets event number `i` in the smart contract state. Returns None if `i`
    /// is an invalid index.
    pub fn get_event(self, index: u32) -> Option<Vec<u8>> {
        let event_len = unsafe { prims::get_event_size(index) };

        if event_len < 0 {
            return None;
        }

        let mut buf = vec![0; event_len.try_into().unwrap()];
        let bytes_written = unsafe { prims::get_event(index, buf.as_mut_ptr()) };

        if bytes_written < 0 {
            return None;
        } else {
            Some(buf)
        }
    }

    pub fn set_init_origin(self, address: AccountAddress) -> Self {
        unsafe { prims::set_init_origin(address.0.as_ptr()) };
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

    #[concordium_test]
    fn set_get_slot_time() {
        let extern_chain_meta = ExternChainMeta {};
        let original = Timestamp::from_timestamp_millis(10);
        TestEnv.set_slot_time(original);
        let stored = extern_chain_meta.block_time();
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
        let receive_context: ReceiveContext = ExternContext::default();
        let original = ContractAddress::new(5040, 12);
        TestEnv.set_receive_self_address(original);
        let stored = receive_context.self_address();
        claim_eq!(original, stored);
    }

    #[concordium_test]
    fn set_get_parameter() {
        let mut external_call_response =
            ExternCallResponse::new(unsafe { NonZeroU32::new_unchecked(1) });
        let i = 1;
        let param = vec![3u8; 7];
        let mut buf = vec![0u8; 10];

        TestEnv.set_parameter(i, &param);

        // Use the prims call to test length and offset
        let param_size = unsafe { prims::get_parameter_size(i) };
        let bytes_written = unsafe { prims::get_parameter_section(i, buf.as_mut_ptr(), 5, 2) };
        let expected = vec![0, 0, 3, 3, 3, 3, 3, 0, 0, 0];

        claim_eq!(param_size, 7);
        claim_eq!(bytes_written, 5);
        claim_eq!(buf, expected);

        // Use the external call to test the actual function that would be called in
        // most real scenarios
        buf = vec![0u8; 7];
        let bytes_written = external_call_response.read(&mut buf).unwrap();
        let expected = param;

        claim_eq!(buf, expected);
        claim_eq!(bytes_written, 7);
    }

    #[concordium_test]
    fn get_empty_parameter() {
        let i = 1;
        let mut buf = vec![0u8; 10];

        let param_size = unsafe { prims::get_parameter_size(i) };
        let bytes_written = unsafe { prims::get_parameter_section(i, buf.as_mut_ptr(), 0, 0) };

        claim_eq!(param_size, -1);
        claim_eq!(param_size, bytes_written);
    }

    #[concordium_test]
    fn set_get_events() {
        // Testing primitive calls
        let event_prim = vec![1u8, 2, 3, 4];
        let store_status =
            unsafe { prims::log_event(event_prim.as_ptr(), event_prim.len().try_into().unwrap()) };
        let event_size = unsafe { prims::get_event_size(0) };

        claim_eq!(store_status, 1);
        claim_eq!(event_size, event_prim.len().try_into().unwrap());

        let mut buf = vec![0; event_prim.len()];
        let bytes_written = unsafe { prims::get_event(0, buf.as_mut_ptr()) };

        claim_eq!(bytes_written as usize, event_prim.len());
        claim_eq!(buf, event_prim);

        // Use the external call to test the actual function that would be called in
        // most real scenarios
        let mut logger = Logger::default();
        let event1 = "Hello, World!".to_owned();
        let event2 = "How are you today?".to_owned();

        logger.log(&event1).unwrap();
        logger.log(&event2).unwrap();

        let stored1 = TestEnv.get_event(1).unwrap();
        let stored2 = TestEnv.get_event(2).unwrap();

        let mut expected1 = Vec::new();
        let mut expected2 = Vec::new();
        event1.serial(&mut expected1).unwrap();
        event2.serial(&mut expected2).unwrap();

        claim_eq!(stored1, expected1);
        claim_eq!(stored2, expected2);
    }

    #[concordium_test]
    fn get_empty_events() {
        let stored = TestEnv.get_event(0);
        claim_eq!(stored, None);
    }

    #[concordium_test]
    fn set_get_init_origin() {
        let init_context: InitContext = ExternContext::default();
        // 3kBx2h5Y2veb4hZgAJWPrr8RyQESKm5TjzF3ti1QQ4VSYLwK1G
        let address = AccountAddress([
            105, 117, 36, 6, 204, 147, 159, 201, 12, 166, 167, 59, 87, 206, 225, 9, 150, 53, 71,
            249, 66, 0, 109, 33, 145, 68, 146, 79, 132, 133, 251, 13,
        ]);
        TestEnv.set_init_origin(address);

        let stored = init_context.init_origin();
        let expected = address;

        claim_eq!(stored, expected);
    }
}
