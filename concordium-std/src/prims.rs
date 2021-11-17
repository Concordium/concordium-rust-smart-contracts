//! This internal module provides the primitive interface to the chain.
//! Functions here should be wrapped in safer wrappers when used from contracts.

/// Interface to the chain. These functions are assumed to be instantiated by
/// the scheduler with relevant primitives.
#[cfg_attr(target_arch = "wasm32", link(wasm_import_module = "concordium"))]
extern "C" {
    pub(crate) fn accept() -> u32;
    // Basic action to send tokens to an account.
    pub(crate) fn simple_transfer(addr_bytes: *const u8, amount: u64) -> u32;
    // Send a message to a smart contract.
    pub(crate) fn send(
        addr_index: u64,
        addr_subindex: u64,
        receive_name: *const u8,
        receive_name_len: u32,
        amount: u64,
        parameter: *const u8,
        parameter_len: u32,
    ) -> u32;
    // Combine two actions using normal sequencing. This is using the stack of
    // actions already produced.
    pub(crate) fn combine_and(l: u32, r: u32) -> u32;
    // Combine two actions using or. This is using the stack of actions already
    // produced.
    pub(crate) fn combine_or(l: u32, r: u32) -> u32;
    // Get the size of the parameter to the method (either init or receive).
    pub(crate) fn get_parameter_size() -> u32;
    // Write a section of the parameter to the given location. Return the number
    // of bytes written. The location is assumed to contain enough memory to
    // write the requested length into.
    pub(crate) fn get_parameter_section(param_bytes: *mut u8, length: u32, offset: u32) -> u32;
    // Write a section of the policy to the given location. Return the number
    // of bytes written. The location is assumed to contain enough memory to
    // write the requested length into.
    pub(crate) fn get_policy_section(policy_bytes: *mut u8, length: u32, offset: u32) -> u32;
    // Add a log item. Return values are
    // - -1 if logging failed due to the message being too long
    // - 0 if the log is already full
    // - 1 if data was successfully logged.
    pub(crate) fn log_event(start: *const u8, length: u32) -> i32;

    // -- CURRENT state implementation --

    // returns how many bytes were read.
    pub(crate) fn load_state(start: *mut u8, length: u32, offset: u32) -> u32;
    // returns how many bytes were written
    pub(crate) fn write_state(start: *const u8, length: u32, offset: u32) -> u32;
    // Resize state to the new value (truncate if new size is smaller). Return 0 if
    // this was unsuccesful (new state too big), or 1 if successful.
    pub(crate) fn resize_state(new_size: u32) -> u32; // returns 0 or 1.
                                                      // get current state size in bytes.
    pub(crate) fn state_size() -> u32;

    // -- NEW state implementation --

    /// Get the root directory.
    pub(crate) fn root_map() -> u32;

    /// Constructs a new trie map and returns a map ID.
    pub(crate) fn new_map() -> u32;

    /// Iterator for all of the current trie maps.
    /// TODO: May be needed
    // fn iterate_maps() -> _

    /// Delete a tree map.
    /// TODO: Is needed if we add iterate_maps
    // fn delete_map(map_id: u32) -> _

    /// Lookup an entry. Concretely this will be some internal identifier
    /// given out by the host. Conceptually the return value is *mut Entry.
    /// Empty key means the root.
    pub(crate) fn entry(map_id: u32, key_start: *const u8, key_length: u32) -> u32;

    /// Checks whether the entry is vacant, i.e., a key does not exist in the
    /// map.
    /// 1 => exists
    /// 0 => does not exist
    pub(crate) fn vacant(entry: u32) -> u32;

    /// Populates the entry. Returns whether an existing value was overwritten.
    /// 1 => created new by overwriting existing value
    /// 0 => created new value
    pub(crate) fn create_entry(entry: u32, capacity: u32) -> u32;

    /// Delete the entry. Returns whether the entry existed or not.
    /// 1 => did exists
    /// 0 => did not exist
    pub(crate) fn delete_entry(entry: u32) -> u32;

    /// Returns an iterator for the map.
    pub(crate) fn iterate_map(map_id: u32) -> u32;

    /// Get next element in an iterator.
    /// Returns -1 when the iterator is empty and entry_id:u32 otherwise.
    pub(crate) fn next(iterator: u32) -> i64;

    // Operations on the entry.
    // entry ... entry id returned by iterator or entry
    // start ... where to write in Wasm memory
    // length ... length of the data to read
    // offset ... where to start reading in the entry
    // returns how many bytes were read.
    pub(crate) fn load_entry_state(entry: u32, start: *mut u8, length: u32, offset: u32) -> u32;

    // entry ... entry id returned by iterator or find
    // start ... where to read in Wasm memory
    // length ... length of the data to write
    // offset ... where to start writing in the entry
    // returns how many bytes were written (this might be removed since we might not
    // have a limit on value size)
    pub(crate) fn write_entry_state(entry: u32, start: *const u8, length: u32, offset: u32) -> u32;

    // Resize entry size to the new value (truncate if new size is smaller). Return
    // 0 if this was unsuccesful (new state too big), or 1 if successful.
    pub(crate) fn resize_entry_state(entry: u32, new_size: u32) -> u32; // returns 0 or 1.

    // get current entry size in bytes.
    pub(crate) fn entry_state_size(entry: u32) -> u32;

    // Getter for the init context.
    /// Address of the sender, 32 bytes
    pub(crate) fn get_init_origin(start: *mut u8);

    // Getters for the receive context
    /// Invoker of the top-level transaction, AccountAddress.
    pub(crate) fn get_receive_invoker(start: *mut u8);
    /// Address of the contract itself, ContractAddress.
    pub(crate) fn get_receive_self_address(start: *mut u8);
    /// Self-balance of the contract, returns the amount
    pub(crate) fn get_receive_self_balance() -> u64;
    /// Immediate sender of the message (either contract or account).
    pub(crate) fn get_receive_sender(start: *mut u8);
    /// Owner of the contract, AccountAddress.
    pub(crate) fn get_receive_owner(start: *mut u8);

    // Getters for the chain meta data
    /// Slot time (in milliseconds) from chain meta data
    pub(crate) fn get_slot_time() -> u64;

    #[cfg(all(feature = "wasm-test", target_arch = "wasm32"))]
    /// Reporting back an error, only exists in debug mode
    pub(crate) fn report_error(
        msg_start: *const u8,
        msg_length: u32,
        filename_start: *const u8,
        filename_length: u32,
        line: u32,
        column: u32,
    );
}

// For every external function, we must provide a dummy function.
// This is nescessary to compile to x86_64 during unit tests on Windows and OSX.
#[cfg(not(target_arch = "wasm32"))]
mod host_dummy_functions {
    #[no_mangle]
    pub(crate) extern "C" fn accept() -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn simple_transfer(_addr_bytes: *const u8, _amount: u64) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn send(
        _addr_index: u64,
        _addr_subindex: u64,
        _receive_name: *const u8,
        _receive_name_len: u32,
        _amount: u64,
        _parameter: *const u8,
        _parameter_len: u32,
    ) -> u32 {
        panic!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn combine_and(_l: u32, _r: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn combine_or(_l: u32, _r: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn get_parameter_size() -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn get_parameter_section(
        _param_bytes: *mut u8,
        _length: u32,
        _offset: u32,
    ) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn get_policy_section(
        _policy_bytes: *mut u8,
        _length: u32,
        _offset: u32,
    ) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn log_event(_start: *const u8, _length: u32) {
        unimplemented!("Dummy function! Not to be executed")
    }

    // -- CURRENT state implementation --
    #[no_mangle]
    pub(crate) extern "C" fn load_state(_start: *mut u8, _length: u32, _offset: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn write_state(_start: *const u8, _length: u32, _offset: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn resize_state(_new_size: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn state_size() -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }

    // -- NEW state implementation --

    #[no_mangle]
    pub(crate) fn root_map() -> u32 { unimplemented!("Dummy function! Not to be executed") }
    #[no_mangle]
    pub(crate) fn new_map() -> u32 { unimplemented!("Dummy function! Not to be executed") }
    #[no_mangle]
    pub(crate) fn entry(_map_id: u32, _key_start: *const u8, _key_length: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn vacant(_entry: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn create_entry(_entry: u32, _capacity: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn delete_entry(_entry: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn iterate_map(_map_id: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn next(_iterator: u32) -> i64 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn load_entry_state(
        _entry: i64,
        _start: *mut u8,
        _length: u32,
        _offset: u32,
    ) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn write_entry_state(
        _entry: i64,
        _start: *const u8,
        _length: u32,
        _offset: u32,
    ) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn resize_entry_state(_entry: i64, _new_size: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn entry_state_size(_entry: i64) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }

    #[no_mangle]
    pub(crate) extern "C" fn get_init_origin(_start: *mut u8) {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn get_receive_invoker(_start: *mut u8) {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn get_receive_self_address(_start: *mut u8) {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn get_receive_self_balance() -> u64 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn get_receive_sender(_start: *mut u8) {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn get_receive_owner(_start: *mut u8) {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) extern "C" fn get_slot_time() -> u64 {
        unimplemented!("Dummy function! Not to be executed")
    }
}
