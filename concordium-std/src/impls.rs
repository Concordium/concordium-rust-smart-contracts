use crate::{convert, mem, prims::*, traits::*, types::*};
use concordium_contracts_common::*;

use mem::MaybeUninit;

impl convert::From<()> for Reject {
    #[inline(always)]
    fn from(_: ()) -> Self { Reject {} }
}

impl convert::From<ParseError> for Reject {
    #[inline(always)]
    fn from(_: ParseError) -> Self { Reject {} }
}

/// # Contract state trait implementations.
impl Seek for ContractState {
    type Err = ();

    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Err> {
        use core::convert::TryFrom;
        use SeekFrom::*;
        match pos {
            Start(offset) => match u32::try_from(offset) {
                Ok(offset_u32) => {
                    self.current_position = offset_u32;
                    Ok(offset)
                }
                _ => Err(()),
            },
            End(delta) => {
                let end = self.size();
                if delta >= 0 {
                    match u32::try_from(delta)
                        .ok()
                        .and_then(|x| self.current_position.checked_add(x))
                    {
                        Some(offset_u32) => {
                            self.current_position = offset_u32;
                            Ok(u64::from(offset_u32))
                        }
                        _ => Err(()),
                    }
                } else {
                    match delta.checked_abs().and_then(|x| u32::try_from(x).ok()) {
                        Some(before) if before <= end => {
                            let new_pos = end - before;
                            self.current_position = new_pos;
                            Ok(u64::from(new_pos))
                        }
                        _ => Err(()),
                    }
                }
            }
            Current(delta) => {
                let new_offset = if delta >= 0 {
                    u32::try_from(delta).ok().and_then(|x| self.current_position.checked_add(x))
                } else {
                    delta
                        .checked_abs()
                        .and_then(|x| u32::try_from(x).ok())
                        .and_then(|x| self.current_position.checked_sub(x))
                };
                match new_offset {
                    Some(offset) => {
                        self.current_position = offset;
                        Ok(u64::from(offset))
                    }
                    _ => Err(()),
                }
            }
        }
    }
}

impl Read for ContractState {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
        use core::convert::TryInto;
        let len: u32 = {
            match buf.len().try_into() {
                Ok(v) => v,
                _ => return Err(ParseError::default()),
            }
        };
        let num_read = unsafe { load_state(buf.as_mut_ptr(), len, self.current_position) };
        self.current_position += num_read;
        Ok(num_read as usize)
    }

    /// Read a `u32` in little-endian format. This is optimized to not
    /// initialize a dummy value before calling an external function.
    fn read_u64(&mut self) -> ParseResult<u64> {
        let mut bytes: MaybeUninit<[u8; 8]> = MaybeUninit::uninit();
        let num_read =
            unsafe { load_state(bytes.as_mut_ptr() as *mut u8, 8, self.current_position) };
        self.current_position += num_read;
        if num_read == 8 {
            unsafe { Ok(u64::from_le_bytes(bytes.assume_init())) }
        } else {
            Err(ParseError::default())
        }
    }

    /// Read a `u32` in little-endian format. This is optimized to not
    /// initialize a dummy value before calling an external function.
    fn read_u32(&mut self) -> ParseResult<u32> {
        let mut bytes: MaybeUninit<[u8; 4]> = MaybeUninit::uninit();
        let num_read =
            unsafe { load_state(bytes.as_mut_ptr() as *mut u8, 4, self.current_position) };
        self.current_position += num_read;
        if num_read == 4 {
            unsafe { Ok(u32::from_le_bytes(bytes.assume_init())) }
        } else {
            Err(ParseError::default())
        }
    }

    /// Read a `u8` in little-endian format. This is optimized to not
    /// initialize a dummy value before calling an external function.
    fn read_u8(&mut self) -> ParseResult<u8> {
        let mut bytes: MaybeUninit<[u8; 1]> = MaybeUninit::uninit();
        let num_read =
            unsafe { load_state(bytes.as_mut_ptr() as *mut u8, 1, self.current_position) };
        self.current_position += num_read;
        if num_read == 1 {
            unsafe { Ok(bytes.assume_init()[0]) }
        } else {
            Err(ParseError::default())
        }
    }
}

impl Write for ContractState {
    type Err = ();

    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Err> {
        use core::convert::TryInto;
        let len: u32 = {
            match buf.len().try_into() {
                Ok(v) => v,
                _ => return Err(()),
            }
        };
        if self.current_position.checked_add(len).is_none() {
            return Err(());
        }
        let num_bytes = unsafe { write_state(buf.as_ptr(), len, self.current_position) };
        self.current_position += num_bytes; // safe because of check above that len + pos is small enough
        Ok(num_bytes as usize)
    }
}

impl HasContractState<()> for ContractState {
    type ContractStateData = ();

    #[inline(always)]
    fn open(_: Self::ContractStateData) -> Self {
        ContractState {
            current_position: 0,
        }
    }

    fn reserve(&mut self, len: u32) -> bool {
        let cur_size = unsafe { state_size() };
        if cur_size < len {
            let res = unsafe { resize_state(len) };
            res == 1
        } else {
            true
        }
    }

    #[inline(always)]
    fn size(&self) -> u32 { unsafe { state_size() } }

    fn truncate(&mut self, new_size: u32) {
        let cur_size = self.size();
        if cur_size > new_size {
            unsafe { resize_state(new_size) };
        }
        if new_size < self.current_position {
            self.current_position = new_size
        }
    }
}

/// # Trait implementations for Parameter
impl Read for Parameter {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
        use core::convert::TryInto;
        let len: u32 = {
            match buf.len().try_into() {
                Ok(v) => v,
                _ => return Err(ParseError::default()),
            }
        };
        let num_read =
            unsafe { get_parameter_section(buf.as_mut_ptr(), len, self.current_position) };
        self.current_position += num_read;
        Ok(num_read as usize)
    }
}

impl HasParameter for Parameter {
    #[inline(always)]
    fn size(&self) -> u32 { unsafe { get_parameter_size() } }
}

/// # Trait implementations for the chain metadata.
impl HasChainMetadata for ChainMetaExtern {
    #[inline(always)]
    fn slot_time(&self) -> SlotTime { unsafe { get_slot_time() } }

    #[inline(always)]
    fn block_height(&self) -> BlockHeight { unsafe { get_block_height() } }

    #[inline(always)]
    fn finalized_height(&self) -> FinalizedHeight { unsafe { get_finalized_height() } }

    #[inline(always)]
    fn slot_number(&self) -> SlotNumber { unsafe { get_slot_number() } }
}

/// # Trait implementations for the init context
impl HasInitContext<()> for InitContextExtern {
    type InitData = ();
    type MetadataType = ChainMetaExtern;
    type ParamType = Parameter;

    /// Create a new init context by using an external call.
    fn open(_: Self::InitData) -> Self { InitContextExtern {} }

    #[inline(always)]
    fn init_origin(&self) -> AccountAddress {
        let mut bytes: MaybeUninit<[u8; ACCOUNT_ADDRESS_SIZE]> = MaybeUninit::uninit();
        let ptr = bytes.as_mut_ptr();
        let address = unsafe {
            get_init_origin(ptr as *mut u8);
            bytes.assume_init()
        };
        AccountAddress(address)
    }

    #[inline(always)]
    fn parameter_cursor(&self) -> Self::ParamType {
        Parameter {
            current_position: 0,
        }
    }

    #[inline(always)]
    fn metadata(&self) -> &Self::MetadataType { &ChainMetaExtern {} }
}

/// # Trait implementations for the receive context
impl HasReceiveContext<()> for ReceiveContextExtern {
    type MetadataType = ChainMetaExtern;
    type ParamType = Parameter;
    type ReceiveData = ();

    /// Create a new receive context
    fn open(_: Self::ReceiveData) -> Self { ReceiveContextExtern {} }

    #[inline(always)]
    fn invoker(&self) -> AccountAddress {
        let mut bytes: MaybeUninit<[u8; ACCOUNT_ADDRESS_SIZE]> = MaybeUninit::uninit();
        let ptr = bytes.as_mut_ptr();
        let address = unsafe {
            get_receive_invoker(ptr as *mut u8);
            bytes.assume_init()
        };
        AccountAddress(address)
    }

    #[inline(always)]
    fn self_address(&self) -> ContractAddress {
        let mut bytes: MaybeUninit<[u8; 16]> = MaybeUninit::uninit();
        let ptr = bytes.as_mut_ptr();
        let address = unsafe {
            get_receive_self_address(ptr as *mut u8);
            bytes.assume_init()
        };
        match from_bytes(&address) {
            Ok(v) => v,
            Err(_) => crate::trap(),
        }
    }

    #[inline(always)]
    fn self_balance(&self) -> Amount {
        Amount::from_micro_gtu(unsafe { get_receive_self_balance() })
    }

    #[inline(always)]
    fn sender(&self) -> Address {
        let mut bytes: MaybeUninit<[u8; 33]> = MaybeUninit::uninit();
        let ptr = bytes.as_mut_ptr() as *mut u8;
        unsafe {
            get_receive_sender(ptr);
            let tag = *ptr;
            match tag {
                0u8 => {
                    match from_bytes(core::slice::from_raw_parts(ptr.add(1), ACCOUNT_ADDRESS_SIZE))
                    {
                        Ok(v) => Address::Account(v),
                        Err(_) => crate::trap(),
                    }
                }
                1u8 => match from_bytes(core::slice::from_raw_parts(ptr.add(1), 16)) {
                    Ok(v) => Address::Contract(v),
                    Err(_) => crate::trap(),
                },
                _ => crate::trap(), // unreachable!("Host violated precondition."),
            }
        }
    }

    #[inline(always)]
    fn owner(&self) -> AccountAddress {
        let mut bytes: MaybeUninit<[u8; ACCOUNT_ADDRESS_SIZE]> = MaybeUninit::uninit();
        let ptr = bytes.as_mut_ptr();
        let address = unsafe {
            get_receive_owner(ptr as *mut u8);
            bytes.assume_init()
        };
        AccountAddress(address)
    }

    #[inline(always)]
    fn parameter_cursor(&self) -> Self::ParamType {
        Parameter {
            current_position: 0,
        }
    }

    #[inline(always)]
    fn metadata(&self) -> &Self::MetadataType { &ChainMetaExtern {} }
}

/// #Implementations of the logger.

impl HasLogger for Logger {
    #[inline(always)]
    fn init() -> Self {
        Self {
            _private: (),
        }
    }

    #[inline(always)]
    fn log_bytes(&mut self, event: &[u8]) {
        unsafe {
            log_event(event.as_ptr(), event.len() as u32);
        }
    }
}

/// #Implementation of actions.
/// These actions are implemented by direct calls to host functions.
impl HasActions for Action {
    #[inline(always)]
    fn accept() -> Self {
        Action {
            _private: unsafe { accept() },
        }
    }

    #[inline(always)]
    fn simple_transfer(acc: &AccountAddress, amount: Amount) -> Self {
        let res = unsafe { simple_transfer(acc.0.as_ptr(), amount.micro_gtu) };
        Action {
            _private: res,
        }
    }

    #[inline(always)]
    fn send(ca: &ContractAddress, receive_name: &str, amount: Amount, parameter: &[u8]) -> Self {
        let receive_bytes = receive_name.as_bytes();
        let res = unsafe {
            send(
                ca.index,
                ca.subindex,
                receive_bytes.as_ptr(),
                receive_bytes.len() as u32,
                amount.micro_gtu,
                parameter.as_ptr(),
                parameter.len() as u32,
            )
        };
        Action {
            _private: res,
        }
    }

    #[inline(always)]
    fn and_then(self, then: Self) -> Self {
        let res = unsafe { combine_and(self._private, then._private) };
        Action {
            _private: res,
        }
    }

    #[inline(always)]
    fn or_else(self, el: Self) -> Self {
        let res = unsafe { combine_or(self._private, el._private) };
        Action {
            _private: res,
        }
    }
}

/// Allocates a Vec of bytes prepended with its length as a `u32` into memory,
/// and prevents them from being dropped. Returns the pointer.
/// Used to pass bytes from a Wasm module to its host.
#[cfg(feature = "std")]
pub fn put_in_memory(input: &[u8]) -> *mut u8 {
    let bytes_length = input.len() as u32;
    let mut bytes = to_bytes(&bytes_length);
    bytes.extend_from_slice(input);
    let ptr = bytes.as_mut_ptr();
    ::std::mem::forget(bytes);
    ptr
}
