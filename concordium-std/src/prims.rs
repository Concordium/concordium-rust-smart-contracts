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

    /// Lookup an entry with the given key. The return value is either
    /// u64::MAX if the entry at the given key does not exist, or else
    /// the first bit of the result is 0, and the remaining bits
    /// are an entry identifier that may be used in subsequent calls.
    pub(crate) fn state_lookup_entry(key_start: *const u8, key_length: u32) -> u64;

    /// Create an empty entry with the given key. The return value is either
    /// u64::MAX if creating the entry failed because of an iterator lock on
    /// the part of the tree, or else the first bit is 0, and the remaining
    /// bits are an entry identifier that maybe used in subsequent calls.
    /// If an entry at that key already exists it is set to the empty entry.
    pub(crate) fn state_create_entry(key_start: *const u8, key_length: u32) -> u64;

    /// Delete the entry. Returns one of
    /// - 0 if the part of the tree this entry was in is locked
    /// - 1 if the entry did not exist
    /// - 2 if the entry was deleted as a result of this call.
    pub(crate) fn state_delete_entry(key_start: *const u8, key_length: u32) -> u32;

    /// Delete a prefix in the tree, that is, delete all parts of the tree that
    /// have the given key as prefix. Returns
    /// - 0 if the tree was locked and thus deletion failed.
    /// - 1 if the tree **was not locked**, but the key points to an empty part
    ///   of the tree
    /// - 2 if a part of the tree was successfully deleted
    pub(crate) fn state_delete_prefix(key_start: *const u8, key_length: u32) -> u32;

    /// Construct an iterator over a part of the tree. This **locks the part of
    /// the tree that has the given prefix**. Locking means that no
    /// deletions or insertions of entries may occur in that subtree.
    /// Returns
    /// - all 1 bits if too many iterators already exist with this key
    /// - all but second bit set to 1 if there is no value in the state with the
    ///   given key
    /// - otherwise the first bit is 0, and the remaining bits are the iterator
    ///   identifier
    /// that may be used in subsequent calls to advance it, or to get its key.
    pub(crate) fn state_iterate_prefix(prefix_start: *const u8, prefix_length: u32) -> u64;

    /// Return the next entry along the iterator, and advance the iterator.
    /// The return value is
    /// - u64::MAX if the iterator does not exist (it was deleted, or the ID is
    ///   invalid)
    /// - all but the second bit set to 1 if no more entries are left, the
    ///   iterator
    /// is exhausted. All further calls will yield the same until the iterator
    /// is deleted.
    /// - otherwise the first bit is 0, and the remaining bits encode an entry
    ///   identifier that can be passed to any of the entry methods.
    pub(crate) fn state_iterator_next(iterator: u64) -> u64;

    /// Delete the iterator, unlocking the subtree. Returns
    /// - u64::MAX if the iterator does not exist.
    /// - 0 if the iterator was already deleted
    /// - 1 if the iterator was successfully deleted as a result of this call.
    pub(crate) fn state_iterator_delete(iterator: u64) -> u32;

    /// Get the length of the key that the iterator is currently pointing at.
    /// Returns
    /// - u32::MAX if the iterator does not exist
    /// - otherwise the length of the key in bytes.
    pub(crate) fn state_iterator_key_size(iterator: u64) -> u32;

    /// Read a section of the key the iterator is currently pointing at. Returns
    /// either
    /// - u32::MAX if the iterator has already been deleted
    /// - the amount of data that was copied. This will never be more than the
    ///   supplied length.
    /// Before the first call to the [state_iterator_next] function this returns
    /// (sections of) the key that was used to create the iterator. After
    /// [state_iterator_next] returns (the encoding of) [None] this method
    /// returns (sections of) the key at the first node returned by the
    /// iterator.
    pub(crate) fn state_iterator_key_read(
        iterator: u64,
        start: *mut u8,
        length: u32,
        offset: u32,
    ) -> u32;

    // Operations on the entry.

    /// Read a part of the entry. The arguments are
    /// entry ... entry id returned by state_iterator_next or state_create_entry
    /// start ... where to write in Wasm memory
    /// length ... length of the data to read
    /// offset ... where to start reading in the entry
    /// The return value is
    /// - u32::MAX if the entry does not exist (has been invalidated, or never
    /// existed). In this case no data is written.
    /// - amount of data that was read. This is never more than length.
    pub(crate) fn state_entry_read(entry: u64, start: *mut u8, length: u32, offset: u32) -> u32;

    /// Write a part of the entry. The arguments are
    /// entry ... entry id returned by state_iterator_next or state_create_entry
    /// start ... where to read from Wasm memory
    /// length ... length of the data to read
    /// offset ... where to start writing in the entry
    /// The return value is
    /// - u32::MAX if the entry does not exist (has been invalidated, or never
    /// existed). In this case no data is written.
    /// - amount of data that was written. This is never more than length.
    pub(crate) fn state_entry_write(entry: u64, start: *const u8, length: u32, offset: u32) -> u32;

    /// Return the current size of the entry in bytes.
    /// The return value is either
    /// - u32::MAX if the entry does not exist (has been invalidated, or never
    /// existed). In this case no data is written.
    /// - or the size of the entry.
    pub(crate) fn state_entry_size(entry: u64) -> u32;

    /// Resize the entry to the given size. Returns
    /// - u32::MAX if the entry has already been invalidated
    /// - 0 if the attempt was unsuccessful because new_size exceeds maximum
    ///   entry size
    /// - 1 if the entry was successfully resized.
    pub(crate) fn state_entry_resize(entry: u64, new_size: u32) -> u32;

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
    fn invoke(_tag: u32, _start: *const u8, _length: u32) -> u64 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    fn write_output(_start: *const u8, _length: u32, _offset: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn get_parameter_size(_i: u32) -> i32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn get_parameter_section(
        _i: u32,
        _param_bytes: *mut u8,
        _length: u32,
        _offset: u32,
    ) -> i32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn get_policy_section(_policy_bytes: *mut u8, _length: u32, _offset: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn log_event(_start: *const u8, _length: u32) -> i32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn state_lookup_entry(_key_start: *const u8, _key_length: u32) -> u64 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn state_create_entry(_key_start: *const u8, _key_length: u32) -> u64 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn state_delete_entry(_entry: u64) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn state_delete_prefix(_key_start: *const u8, _key_length: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn state_iterate_prefix(_prefix_start: *const u8, _prefix_length: u32) -> u64 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn state_iterator_next(_iterator: u64) -> u64 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn state_iterator_delete(_iterator: u64) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn state_iterator_key_size(_iterator: u64) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn state_iterator_key_read(
        _iterator: u64,
        _start: *mut u8,
        _length: u32,
        _offset: u32,
    ) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn state_entry_read(
        _entry: u64,
        _start: *mut u8,
        _length: u32,
        _offset: u32,
    ) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn state_entry_write(
        _entry: u64,
        _start: *const u8,
        _length: u32,
        _offset: u32,
    ) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn state_entry_resize(_entry: u64, _new_size: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    pub(crate) fn state_entry_size(_entry: u64) -> u32 {
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
