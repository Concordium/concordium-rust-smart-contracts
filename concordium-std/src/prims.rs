//! This internal module provides the primitive interface to the chain.
//! Functions here should be wrapped in safer wrappers when used from contracts.

/// Interface to the chain. These functions are assumed to be instantiated by
/// the scheduler with relevant primitives.
#[cfg_attr(target_arch = "wasm32", link(wasm_import_module = "concordium"))]
extern "C" {
    /// Invoke a host instruction. The arguments are
    ///
    /// - `tag`, which instruction to invoke
    ///   - 0 for transfer to account
    ///   - 1 for call to a contract
    /// - `start`, pointer to the start of the invoke payload
    /// - `length`, length of the payload
    /// - if the last 5 bytes are 0 then the call succeeded. In this case the
    ///   first bit of the response indicates whether our own state has changed
    ///   (1) or not (0) the remaining 23 bits are the index of the return value
    ///   that can be used in a call to `get_parameter_section` and
    ///   `get_parameter_size`.
    /// - otherwise
    ///   - if the fourth byte is 0 the call failed because of a logic error and
    ///     there is a return value. Bits 1..24 of the response are the index of
    ///     the return value. Bits 32..64 are to be interpreted in two's
    ///     complement and will be a negative number indicating the error code.
    ///   - otherwise only the fourth byte is set.
    ///   - if it is 1 then call failed due to transfer of non-existent amount
    ///   - if it is 2 then the account to transfer to did not exist
    ///   - if it is 3 then the contract to invoke did not exist
    ///   - if it is 4 then the entrypoint did not exist
    ///   - if it is 5 then sending a message to V0 contract failed.
    ///   - if it is 6 then invoking a contract failed with a runtime error
    ///   - no other values are possible
    pub(crate) fn invoke(tag: u32, start: *const u8, length: u32) -> u64;
    /// Write to the return value of the contract. The parameters are
    ///
    /// - `start` the pointer to the location in memory where the data resides
    /// - `length` the size of data (in bytes)
    /// - `offset` where in the return value to write the data
    ///
    /// The return value indicates how many bytes were written.
    pub(crate) fn write_output(start: *const u8, length: u32, offset: u32) -> u32;
    /// Get the size of the `i`-th parameter to the call. 0-th parameter is
    /// always the original parameter that the method was invoked with,
    /// invoking a contract adds additional parameters to the stack. Returns
    /// `-1` if the given parameter does not exist.
    pub(crate) fn get_parameter_size(i: u32) -> i32;
    /// Write a section of the `i`-th parameter to the given location. Return
    /// the number of bytes written or `-1` if the parameter does not exist.
    /// The location is assumed to contain enough memory to
    /// write the requested length into.
    pub(crate) fn get_parameter_section(
        i: u32,
        param_bytes: *mut u8,
        length: u32,
        offset: u32,
    ) -> i32;
    /// Write a section of the policy to the given location. Return the number
    /// of bytes written. The location is assumed to contain enough memory to
    /// write the requested length into.
    pub(crate) fn get_policy_section(policy_bytes: *mut u8, length: u32, offset: u32) -> u32;
    /// Add a log item. Return values are
    /// - -1 if logging failed due to the message being too long
    /// - 0 if the log is already full
    /// - 1 if data was successfully logged.
    pub(crate) fn log_event(start: *const u8, length: u32) -> i32;

    /// Create an entry with the given key and return its entry id.
    /// - vacant => Allocates an empty state entry and returns its id.
    /// - Occupied by entry `e` => Allocates an empty state entry and returns
    ///   its entry id `e'`, where `e' != e`. Entry `e` is eventually
    ///   deallocated.
    pub(crate) fn create(key_start: *const u8, key_length: u32) -> u32;

    /// Lookup an entry.
    /// Returns -1 if the entry does not exist.
    /// Otherwise it returns an entry id as a u32.
    pub(crate) fn lookup(key_start: *const u8, key_length: u32) -> i64;

    /// Delete the entry. Returns whether the entry was or not.
    /// 1 => did exists
    /// 0 => did not exist
    pub(crate) fn delete_entry(entry: u32) -> u32;

    /// This might or might not be necessary.
    /// If exact is set then only delete the specifi key, otherwise the entire
    /// subtree. It seems useful to have the ability to delete the entire
    /// tree
    /// 1 => deleted something
    /// 0 => didn't delete anything
    /// TODO: could also say how much was deleted (number of entries).
    pub(crate) fn delete_prefix(key_start: *const u8, key_length: u32, exact: u32) -> u32;

    /// Iteration. Returns an iterator.
    pub(crate) fn iterator(prefix_start: *const u8, prefix_length: u32) -> u32;

    /// Returns the entry with the key that is the successor of the current key
    /// subject to prefix restrictions.
    /// If the iterator is empty, -1 is returned.
    ///
    /// This will be a snapshot. If you mutate, it will mutate the original
    /// tree, but the snapshot and its entries will remain the same.
    /// Getting a new iterator subsequently will get you a snapshot with your
    /// new changes.
    pub(crate) fn next(iterator: u32) -> i64;

    /// Get the length of the entry's key.
    pub(crate) fn get_entry_key_length(entry: u32) -> u32;

    /// Read the entry's key.
    /// entry ... entry id returned by iterator or entry
    /// start ... where to write in Wasm memory
    /// length ... length of the data to read
    /// offset ... where to start reading the entry key
    /// Returns how many bytes were read.
    pub(crate) fn load_entry_key(entry: u32, start: *mut u8, length: u32, offset: u32) -> u32;

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
    fn invoke(_tag: u32, _start: *const u8, _length: u32) -> i64 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    fn write_output(_start: *const u8, _length: u32, _offset: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn get_parameter_size(_i: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn get_parameter_section(
        _i: u32,
        _param_bytes: *mut u8,
        _length: u32,
        _offset: u32,
    ) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn get_policy_section(_policy_bytes: *mut u8, _length: u32, _offset: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn log_event(_start: *const u8, _length: u32) {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn entry(_key_start: *const u8, _key_length: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn lookup(_key_start: *const u8, _key_length: u32) -> i64 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn vacant(_entry: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn create(_entry: u32, _capacity: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn delete_entry(_entry: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn delete_prefix(_prefix_start: *const u8, _prefix_length: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn iterator(_prefix_start: *const u8, _prefix_length: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn next(_iterator: u32) -> i64 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn get_entry_key_length(_entry: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn load_entry_key(
        _entry: u32,
        _start: *const u8,
        _length: u32,
        _offset: u32,
    ) -> u32 {
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
    extern "C" fn get_init_origin(_start: *mut u8) {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn get_receive_invoker(_start: *mut u8) {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn get_receive_self_address(_start: *mut u8) {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn get_receive_self_balance() -> u64 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn get_receive_sender(_start: *mut u8) {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn get_receive_owner(_start: *mut u8) {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn get_slot_time() -> u64 { unimplemented!("Dummy function! Not to be executed") }
}
