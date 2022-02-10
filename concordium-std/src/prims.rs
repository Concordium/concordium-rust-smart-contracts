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
    /// The response is encoded as follows.
    /// - success is encoded as 0
    /// - every failure has all bits of the first 3 bytes set
    /// - in case of failure
    ///   - if the 4th byte is 0 then the remaining 4 bytes encode the rejection
    ///     reason from the contract
    ///   - otherwise only the 4th byte is used, and encodes the enviroment
    ///     failure.
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
    /// returns how many bytes were read.
    pub(crate) fn load_state(start: *mut u8, length: u32, offset: u32) -> u32;
    /// Modify the contract state, and return how many bytes were written
    pub(crate) fn write_state(start: *const u8, length: u32, offset: u32) -> u32;
    /// Resize state to the new value (truncate if new size is smaller). Return
    /// 0 if this was unsuccessful (new state too big), or 1 if successful.
    pub(crate) fn resize_state(new_size: u32) -> u32;
    /// Get the current state size in bytes.
    pub(crate) fn state_size() -> u32;

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
    extern "C" fn load_state(_start: *mut u8, _length: u32, _offset: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn write_state(_start: *const u8, _length: u32, _offset: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn resize_state(_new_size: u32) -> u32 {
        unimplemented!("Dummy function! Not to be executed")
    }
    #[no_mangle]
    extern "C" fn state_size() -> u32 { unimplemented!("Dummy function! Not to be executed") }
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
