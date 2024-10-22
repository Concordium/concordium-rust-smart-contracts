use concordium_contracts_common::{
    AccountAddress, Address, Amount, ContractAddress, EntrypointName, Serial, SlotTime,
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

    /// Sets the current balance of this smart contract.
    pub fn set_receive_balance(self, balance: Amount) -> Self {
        unsafe { prims::set_receive_self_balance(balance.micro_ccd) };
        self
    }

    /// Sets the address of this smart contract.
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

    /// Set the address of the sender.
    pub fn set_init_origin(self, address: AccountAddress) -> Self {
        unsafe { prims::set_init_origin(address.0.as_ptr()) };
        self
    }

    /// Set the invoker of the top-level transaction.
    pub fn set_receive_invoker(self, address: AccountAddress) -> Self {
        unsafe { prims::set_receive_invoker(address.0.as_ptr()) };
        self
    }

    /// Set the immediate sender of the message (either contract or account).
    pub fn set_receive_sender(self, address: Address) -> Self {
        let mut buf = Vec::new();
        address.serial(&mut buf).unwrap();
        unsafe { prims::set_receive_sender(buf.as_ptr()) };
        self
    }

    /// Set the owner of the contract.
    pub fn set_receive_owner(self, address: AccountAddress) -> Self {
        unsafe { prims::set_receive_owner(address.0.as_ptr()) };
        self
    }

    /// Set the receive entrypoint name.
    pub fn set_receive_entrypoint(self, entrypoint: EntrypointName) -> Self {
        let mut buf = Vec::new();
        entrypoint.serial(&mut buf).unwrap();
        unsafe { prims::set_receive_entrypoint(buf.as_ptr()) };
        self
    }
}

#[cfg(feature = "internal-wasm-test")]
mod wasm_test {
    use core::{num::NonZeroU32, str::FromStr};

    use concordium_contracts_common::{ContractAddress, Timestamp};

    use super::*;
    use crate::*;

    // ----- Helper Functions -----
    // Helper functions to get host data, as a real smart contract would

    fn extern_host() -> ExternHost<()> {
        let state_api = ExternStateApi::open();
        let state_builder = StateBuilder::open(state_api);
        ExternHost {
            state: (),
            state_builder,
        }
    }

    fn crypto_primitives() -> CryptoPrimitives { CryptoPrimitives {} }

    fn receive_context() -> ReceiveContext { ExternContext::default() }

    fn init_context() -> InitContext { ExternContext::default() }

    fn account_address() -> AccountAddress {
        // 3kBx2h5Y2veb4hZgAJWPrr8RyQESKm5TjzF3ti1QQ4VSYLwK1G
        AccountAddress([
            105, 117, 36, 6, 204, 147, 159, 201, 12, 166, 167, 59, 87, 206, 225, 9, 150, 53, 71,
            249, 66, 0, 109, 33, 145, 68, 146, 79, 132, 133, 251, 13,
        ])
    }

    // ----- Tests -----

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
        let original = ContractAddress::new(5040, 12);
        TestEnv.set_receive_self_address(original);
        let stored = receive_context().self_address();
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
        let bytes_written = external_call_response.read(&mut buf).unwrap_abort();
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
        // Testing primitive calls for testing offset and length parameters
        let event_prim = vec![1u8, 2, 3, 4];
        let store_status = unsafe {
            prims::log_event(event_prim.as_ptr(), event_prim.len().try_into().unwrap_abort())
        };
        let event_size = unsafe { prims::get_event_size(0) };

        claim_eq!(store_status, 1);
        claim_eq!(event_size, event_prim.len().try_into().unwrap_abort());

        let mut buf = vec![0; event_prim.len()];
        let bytes_written = unsafe { prims::get_event(0, buf.as_mut_ptr()) };

        claim_eq!(bytes_written as usize, event_prim.len());
        claim_eq!(buf, event_prim);

        // Use the external call to test the actual function that would be called in
        // most real scenarios
        let mut logger = Logger::default();
        let event1 = "Hello, World!".to_owned();
        let event2 = "How are you today?".to_owned();

        logger.log(&event1).unwrap_abort();
        logger.log(&event2).unwrap_abort();

        let stored1 = TestEnv.get_event(1).unwrap_abort();
        let stored2 = TestEnv.get_event(2).unwrap_abort();

        let mut expected1 = Vec::new();
        let mut expected2 = Vec::new();
        event1.serial(&mut expected1).unwrap_abort();
        event2.serial(&mut expected2).unwrap_abort();

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
        let address = account_address();
        TestEnv.set_init_origin(address);
        let stored = init_context().init_origin();
        claim_eq!(stored, address);
    }

    #[concordium_test]
    fn set_get_receive_invoker() {
        let address = account_address();
        TestEnv.set_receive_invoker(address);
        let stored = receive_context().invoker();
        claim_eq!(stored, address);
    }

    #[concordium_test]
    fn set_get_receive_sender() {
        let address = Address::Account(account_address());
        TestEnv.set_receive_sender(address);
        let stored = receive_context().sender();
        claim_eq!(stored, address);

        let address = Address::Contract(ContractAddress::new(3, 7));
        TestEnv.set_receive_sender(address);
        let stored = receive_context().sender();
        claim_eq!(stored, address);
    }

    #[concordium_test]
    fn set_get_receive_owner() {
        let address = account_address();
        TestEnv.set_receive_owner(address);
        let stored = receive_context().owner();
        claim_eq!(stored, address);
    }

    #[concordium_test]
    fn set_get_receive_entrypoint() {
        let entrypoint = EntrypointName::new("some_entry_point").unwrap_abort();

        TestEnv.set_receive_entrypoint(entrypoint);

        let size = unsafe { prims::get_receive_entrypoint_size() };
        let stored = receive_context().named_entrypoint();

        claim_eq!(size, entrypoint.size());
        claim_eq!(stored, entrypoint.to_owned());
    }

    #[concordium_test]
    fn verify_ed25519_signature() {
        let _sk_hex = "7eee273f83906eb9a673c0119553b416aa515fc870a730b4e70cdf1a11dc17d3";
        let pk_hex = "d2af46bb1bd8d656c29a62bda2ca66bd26a0f0aea1e0988c7044003e630ff895";
        let sig_hex = "99e3c8b2cf832c3c0f6e8031466fe259b1bf86a4309386418cebb6cd7859d62b3431250e54c9cac7659b36743d1c272514ece30c1ce37d4f422d42f84069c007";
        let msg = b"Hello, this is a test message!";

        // Check valid signature
        let pk = PublicKeyEd25519::from_str(pk_hex).unwrap_abort();
        let sig = SignatureEd25519::from_str(sig_hex).unwrap_abort();
        let is_verified = crypto_primitives().verify_ed25519_signature(pk, sig, msg);
        claim_eq!(is_verified, true);

        // Check invalid signature
        let wrong_sig_hex = "1111111111832c3c0f6e8031466fe259b1bf86a4309386418cebb6cd7859d62b3431250e54c9cac7659b36743d1c272514ece30c1ce37d4f422d42f84069c007";
        let wrong_sig = SignatureEd25519::from_str(wrong_sig_hex).unwrap_abort();
        let is_verified = crypto_primitives().verify_ed25519_signature(pk, wrong_sig, msg);
        claim_eq!(is_verified, false);
    }

    #[concordium_test]
    fn verify_ecdsa_secp256k_signature() {
        let _sk_hex = "49f386482744ea6ea0d92b17c73fbc1729e3c061dd9ddf02e85db8d88b2a157b";
        let pk_hex = "03b8fa66dda8feccbfcf15fcab18d2b124570f4af23b7961bfbd61f8c1967aca12";
        let sig_hex = "a9170fc158e040f68dd59ab6c0415cf0b8a8811f92294696aa13dfdc7671407732cb6de20f39ca1fdb159cef3213d980fb32b82b8851c847e8168e125fd20c1c";
        let msg_hash = [
            11u8, 236, 151, 183, 34, 12, 80, 68, 186, 215, 67, 68, 119, 118, 54, 234, 68, 106, 196,
            109, 214, 155, 169, 75, 236, 168, 229, 227, 168, 60, 84, 140,
        ];

        // Check valid signature
        let pk = PublicKeyEcdsaSecp256k1::from_str(pk_hex).unwrap_abort();
        let sig = SignatureEcdsaSecp256k1::from_str(sig_hex).unwrap_abort();
        let is_verified = crypto_primitives().verify_ecdsa_secp256k1_signature(pk, sig, msg_hash);
        claim_eq!(is_verified, true);

        // Check invalid signature
        let wrong_sig_hex = "111111111111111111111111c0415cf0b8a8811f92294696aa13dfdc7671407732cb6de20f39ca1fdb159cef3213d980fb32b82b8851c847e8168e125fd20c1c";
        let wrong_sig = SignatureEcdsaSecp256k1::from_str(wrong_sig_hex).unwrap_abort();
        let is_verified =
            crypto_primitives().verify_ecdsa_secp256k1_signature(pk, wrong_sig, msg_hash);
        claim_eq!(is_verified, false);
    }
}
