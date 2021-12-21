use crate::{
    collections::{BTreeMap, BTreeSet},
    convert::{self, TryFrom, TryInto},
    hash::Hash,
    mem, num,
    prims::*,
    traits::*,
    types::*,
    vec::Vec,
    String,
};
use concordium_contracts_common::*;
use mem::MaybeUninit;

impl convert::From<()> for Reject {
    #[inline(always)]
    fn from(_: ()) -> Self {
        Reject {
            error_code: unsafe { num::NonZeroI32::new_unchecked(i32::MIN + 1) },
        }
    }
}

impl convert::From<ParseError> for Reject {
    #[inline(always)]
    fn from(_: ParseError) -> Self {
        Reject {
            error_code: unsafe { num::NonZeroI32::new_unchecked(i32::MIN + 2) },
        }
    }
}

/// Full is mapped to i32::MIN+3, Malformed is mapped to i32::MIN+4.
impl From<LogError> for Reject {
    #[inline(always)]
    fn from(le: LogError) -> Self {
        let error_code = match le {
            LogError::Full => unsafe { crate::num::NonZeroI32::new_unchecked(i32::MIN + 3) },
            LogError::Malformed => unsafe { crate::num::NonZeroI32::new_unchecked(i32::MIN + 4) },
        };
        Self {
            error_code,
        }
    }
}

/// MissingInitPrefix is mapped to i32::MIN + 5,
/// TooLong to i32::MIN + 6,
/// ContainsDot to i32::MIN + 9, and
/// InvalidCharacters to i32::MIN + 10.
impl From<NewContractNameError> for Reject {
    fn from(nre: NewContractNameError) -> Self {
        let error_code = match nre {
            NewContractNameError::MissingInitPrefix => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 5)
            },
            NewContractNameError::TooLong => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 6)
            },
            NewContractNameError::ContainsDot => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 9)
            },
            NewContractNameError::InvalidCharacters => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 10)
            },
        };
        Self {
            error_code,
        }
    }
}

/// MissingDotSeparator is mapped to i32::MIN + 7,
/// TooLong to i32::MIN + 8, and
/// InvalidCharacters to i32::MIN + 11.
impl From<NewReceiveNameError> for Reject {
    fn from(nre: NewReceiveNameError) -> Self {
        let error_code = match nre {
            NewReceiveNameError::MissingDotSeparator => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 7)
            },
            NewReceiveNameError::TooLong => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 8)
            },
            NewReceiveNameError::InvalidCharacters => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 11)
            },
        };
        Self {
            error_code,
        }
    }
}

/// The error code is i32::MIN + 12
impl From<NotPayableError> for Reject {
    #[inline(always)]
    fn from(_: NotPayableError) -> Self {
        Self {
            error_code: unsafe { crate::num::NonZeroI32::new_unchecked(i32::MIN + 12) },
        }
    }
}

impl ReturnValue {
    pub fn get_i(&self) -> NonZeroU32 { self.i }
}

impl Write for ReturnValue {
    type Err = ();

    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Err> {
        let len: u32 = {
            match buf.len().try_into() {
                Ok(v) => v,
                _ => return Err(()),
            }
        };
        if self.current_position.checked_add(len).is_none() {
            return Err(());
        }
        let num_bytes = unsafe { write_output(buf.as_ptr(), len, self.current_position) };
        self.current_position += num_bytes; // safe because of check above that len + pos is small enough
        Ok(num_bytes as usize)
    }
}

/// # Contract state trait implementations.
impl Seek for ContractState {
    type Err = ();

    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Err> {
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
impl Read for ExternParameter {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
        let len: u32 = {
            match buf.len().try_into() {
                Ok(v) => v,
                _ => return Err(ParseError::default()),
            }
        };
        let num_read =
            unsafe { get_parameter_section(0, buf.as_mut_ptr(), len, self.current_position) };
        self.current_position += num_read as u32; // parameter 0 always exists, so this is safe.
        Ok(num_read as usize)
    }
}

impl HasParameter for ExternParameter {
    #[inline(always)]
    // parameter 0 always exists so this is correct
    fn size(&self) -> u32 { unsafe { get_parameter_size(0) as u32 } }
}

/// # Trait implementations ReturnValue
impl Read for ReturnValue {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
        let len: u32 = {
            match buf.len().try_into() {
                Ok(v) => v,
                _ => return Err(ParseError::default()),
            }
        };
        let num_read = unsafe {
            get_parameter_section(self.i.into(), buf.as_mut_ptr(), len, self.current_position)
        };
        if num_read >= 0 {
            self.current_position += num_read as u32;
            Ok(num_read as usize)
        } else {
            Err(ParseError::default())
        }
    }
}

/// # Trait implementations for the chain metadata.
impl HasChainMetadata for ChainMetaExtern {
    #[inline(always)]
    fn slot_time(&self) -> SlotTime { Timestamp::from_timestamp_millis(unsafe { get_slot_time() }) }
}

impl HasPolicy for Policy<AttributesCursor> {
    fn identity_provider(&self) -> IdentityProvider { self.identity_provider }

    fn created_at(&self) -> Timestamp { self.created_at }

    fn valid_to(&self) -> Timestamp { self.valid_to }

    fn next_item(&mut self, buf: &mut [u8; 31]) -> Option<(AttributeTag, u8)> {
        if self.items.remaining_items == 0 {
            return None;
        }

        let (tag_value_len, num_read) = unsafe {
            let mut tag_value_len = MaybeUninit::<[u8; 2]>::uninit();
            // Should succeed, otherwise host violated precondition.
            let num_read = get_policy_section(
                tag_value_len.as_mut_ptr() as *mut u8,
                2,
                self.items.current_position,
            );
            (tag_value_len.assume_init(), num_read)
        };
        self.items.current_position += num_read;
        if tag_value_len[1] > 31 {
            // Should not happen because all attributes fit into 31 bytes.
            return None;
        }
        let num_read = unsafe {
            get_policy_section(
                buf.as_mut_ptr(),
                u32::from(tag_value_len[1]),
                self.items.current_position,
            )
        };
        self.items.current_position += num_read;
        self.items.remaining_items -= 1;
        Some((AttributeTag(tag_value_len[0]), tag_value_len[1]))
    }
}

/// An iterator over policies using host functions to supply the data.
/// The main interface to using this type is via the methods of the [Iterator](https://doc.rust-lang.org/std/iter/trait.Iterator.html)
/// and [ExactSizeIterator](https://doc.rust-lang.org/std/iter/trait.ExactSizeIterator.html) traits.
pub struct PoliciesIterator {
    /// Position in the policies binary serialization.
    pos:             u32,
    /// Number of remaining items in the stream.
    remaining_items: u16,
}

impl Iterator for PoliciesIterator {
    type Item = Policy<AttributesCursor>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining_items == 0 {
            return None;
        }
        // 2 for total size of this section, 4 for identity_provider,
        // 8 bytes for created_at, 8 for valid_to, and 2 for
        // the length
        let mut buf: MaybeUninit<[u8; 2 + 4 + 8 + 8 + 2]> = MaybeUninit::uninit();
        let buf = unsafe {
            get_policy_section(buf.as_mut_ptr() as *mut u8, 2 + 4 + 8 + 8 + 2, self.pos);
            buf.assume_init()
        };
        let skip_part: [u8; 2] = buf[0..2].try_into().unwrap_abort();
        let ip_part: [u8; 4] = buf[2..2 + 4].try_into().unwrap_abort();
        let created_at_part: [u8; 8] = buf[2 + 4..2 + 4 + 8].try_into().unwrap_abort();
        let valid_to_part: [u8; 8] = buf[2 + 4 + 8..2 + 4 + 8 + 8].try_into().unwrap_abort();
        let len_part: [u8; 2] = buf[2 + 4 + 8 + 8..2 + 4 + 8 + 8 + 2].try_into().unwrap_abort();
        let identity_provider = IdentityProvider::from_le_bytes(ip_part);
        let created_at = Timestamp::from_timestamp_millis(u64::from_le_bytes(created_at_part));
        let valid_to = Timestamp::from_timestamp_millis(u64::from_le_bytes(valid_to_part));
        let remaining_items = u16::from_le_bytes(len_part);
        let attributes_start = self.pos + 2 + 4 + 8 + 8 + 2;
        self.pos += u32::from(u16::from_le_bytes(skip_part)) + 2;
        self.remaining_items -= 1;
        Some(Policy {
            identity_provider,
            created_at,
            valid_to,
            items: AttributesCursor {
                current_position: attributes_start,
                remaining_items,
            },
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let rem = self.remaining_items as usize;
        (rem, Some(rem))
    }
}

impl ExactSizeIterator for PoliciesIterator {
    #[inline(always)]
    fn len(&self) -> usize { self.remaining_items as usize }
}

impl<T: sealed::ContextType> HasCommonData for ExternContext<T> {
    type MetadataType = ChainMetaExtern;
    type ParamType = ExternParameter;
    type PolicyIteratorType = PoliciesIterator;
    type PolicyType = Policy<AttributesCursor>;

    #[inline(always)]
    fn metadata(&self) -> &Self::MetadataType { &ChainMetaExtern {} }

    fn policies(&self) -> PoliciesIterator {
        let mut buf: MaybeUninit<[u8; 2]> = MaybeUninit::uninit();
        let buf = unsafe {
            get_policy_section(buf.as_mut_ptr() as *mut u8, 2, 0);
            buf.assume_init()
        };
        PoliciesIterator {
            pos:             2, // 2 because we already read 2 bytes.
            remaining_items: u16::from_le_bytes(buf),
        }
    }

    #[inline(always)]
    fn parameter_cursor(&self) -> Self::ParamType {
        ExternParameter {
            current_position: 0,
        }
    }
}

const INVOKE_TRANSFER_TAG: u32 = 0;
const INVOKE_CALL_TAG: u32 = 1;

/// TODO: Make consistent with errors returned by the scheduler.
fn parse_response_code(code: u64) -> InvokeResult<NonZeroU32> {
    if code & !0xffff_ff00_0000_0000 == 0 {
        // this means success
        let rv = (code >> 32) as u32;
        if rv > 0 {
            Ok(unsafe { NonZeroU32::new_unchecked(rv) })
        } else {
            crate::trap() // host precondition violation.
        }
    } else {
        match 0x0000_00ff_0000_0000 & code >> 32 {
            0x00 =>
            // response with logic error and return value.
            {
                let reason = (0x0000_0000_ffff_ffff & code) as u32 as i32;
                if reason == 0 {
                    crate::trap()
                } else {
                    let rv = (code >> 32) as u32;
                    if rv > 0 {
                        Err(InvokeError::LogicReject {
                            reason,
                            return_value: ReturnValue {
                                i:                unsafe { NonZeroU32::new_unchecked(rv) },
                                current_position: 0,
                            },
                        })
                    } else {
                        crate::trap() // host precondition violation.
                    }
                }
            }
            0x01 => Err(InvokeError::AmountTooLarge),
            0x02 => Err(InvokeError::MissingAccount),
            0x03 => Err(InvokeError::MissingContract),
            0x04 => Err(InvokeError::MessageFailed),
            0x05 => Err(InvokeError::Trap),
            _ => Err(InvokeError::Unknown), // FIXME: This should be trap as well.
        }
    }
}

impl HasOperations for ExternOperations {
    fn invoke_transfer(&mut self, receiver: &AccountAddress, amount: Amount) -> InvokeResult<()> {
        let mut bytes: MaybeUninit<[u8; ACCOUNT_ADDRESS_SIZE + 8]> = MaybeUninit::uninit();
        let data = unsafe {
            (bytes.as_mut_ptr() as *mut u8).copy_from_nonoverlapping(
                receiver.as_ref() as *const [u8; ACCOUNT_ADDRESS_SIZE] as *const u8,
                ACCOUNT_ADDRESS_SIZE,
            );
            (bytes.as_mut_ptr() as *mut u8).add(ACCOUNT_ADDRESS_SIZE).copy_from_nonoverlapping(
                &amount.micro_ccd.to_le_bytes() as *const [u8; 8] as *const u8,
                8,
            );
            bytes.assume_init()
        };
        let response = unsafe {
            invoke(INVOKE_TRANSFER_TAG, data.as_ptr(), (ACCOUNT_ADDRESS_SIZE + 8) as u32)
        };
        parse_response_code(response).map(|_| ())
    }

    fn invoke_contract(
        &mut self,
        to: &ContractAddress,
        parameter: Parameter,
        method: EntrypointName,
        amount: Amount,
    ) -> InvokeResult<crate::ReturnValue> {
        let mut data =
            Vec::with_capacity(16 + parameter.0.len() + 2 + method.size() as usize + 2 + 8);
        let mut cursor = Cursor::new(&mut data);
        to.serial(&mut cursor).unwrap_abort();
        parameter.serial(&mut cursor).unwrap_abort();
        method.serial(&mut cursor).unwrap_abort();
        amount.serial(&mut cursor).unwrap_abort();
        let len = data.len();
        let response = unsafe { invoke(INVOKE_CALL_TAG, data.as_ptr(), len as u32) };
        let i = parse_response_code(response)?;
        Ok(ReturnValue {
            i,
            current_position: 0,
        })
    }

    // TODO: Return the correct `i`.
    fn success(&self) -> crate::ReturnValue {
        ReturnValue {
            i:                unsafe { NonZeroU32::new_unchecked(1) },
            current_position: 0,
        }
    }
}

/// # Trait implementations for the init context
impl HasInitContext for ExternContext<crate::types::InitContextExtern> {
    type InitData = ();

    /// Create a new init context by using an external call.
    fn open(_: Self::InitData) -> Self { ExternContext::default() }

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
}

/// # Trait implementations for the receive context
impl HasReceiveContext for ExternContext<crate::types::ReceiveContextExtern> {
    type ReceiveData = ();

    /// Create a new receive context
    fn open(_: Self::ReceiveData) -> Self { ExternContext::default() }

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
        Amount::from_micro_ccd(unsafe { get_receive_self_balance() })
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
}

/// #Implementations of the logger.

impl HasLogger for Logger {
    #[inline(always)]
    fn init() -> Self {
        Self {
            _private: (),
        }
    }

    fn log_raw(&mut self, event: &[u8]) -> Result<(), LogError> {
        let res = unsafe { log_event(event.as_ptr(), event.len() as u32) };
        match res {
            1 => Ok(()),
            0 => Err(LogError::Full),
            _ => Err(LogError::Malformed),
        }
    }
}

/// Allocates a Vec of bytes prepended with its length as a `u32` into memory,
/// and prevents them from being dropped. Returns the pointer.
/// Used to pass bytes from a Wasm module to its host.
#[doc(hidden)]
pub fn put_in_memory(input: &[u8]) -> *mut u8 {
    let bytes_length = input.len() as u32;
    let mut bytes = to_bytes(&bytes_length);
    bytes.extend_from_slice(input);
    let ptr = bytes.as_mut_ptr();
    #[cfg(feature = "std")]
    ::std::mem::forget(bytes);
    #[cfg(not(feature = "std"))]
    core::mem::forget(bytes);
    ptr
}

impl<A, E> UnwrapAbort for Result<A, E> {
    type Unwrap = A;

    #[inline]
    fn unwrap_abort(self) -> Self::Unwrap {
        match self {
            Ok(x) => x,
            Err(_) => crate::trap(),
        }
    }
}

#[cfg(not(feature = "std"))]
use core::fmt;
#[cfg(feature = "std")]
use std::fmt;
use std::num::NonZeroU32;

impl<A, E: fmt::Debug> ExpectReport for Result<A, E> {
    type Unwrap = A;

    fn expect_report(self, msg: &str) -> Self::Unwrap {
        match self {
            Ok(x) => x,
            Err(e) => crate::fail!("{}: {:?}", msg, e),
        }
    }
}

impl<A: fmt::Debug, E> ExpectErrReport for Result<A, E> {
    type Unwrap = E;

    fn expect_err_report(self, msg: &str) -> Self::Unwrap {
        match self {
            Ok(a) => crate::fail!("{}: {:?}", msg, a),
            Err(e) => e,
        }
    }
}

impl<A> UnwrapAbort for Option<A> {
    type Unwrap = A;

    #[inline(always)]
    fn unwrap_abort(self) -> Self::Unwrap { self.unwrap_or_else(|| crate::trap()) }
}

impl<A> ExpectReport for Option<A> {
    type Unwrap = A;

    fn expect_report(self, msg: &str) -> Self::Unwrap {
        match self {
            Some(v) => v,
            None => crate::fail!("{}", msg),
        }
    }
}

impl<A: fmt::Debug> ExpectNoneReport for Option<A> {
    fn expect_none_report(self, msg: &str) {
        if let Some(x) = self {
            crate::fail!("{}: {:?}", msg, x)
        }
    }
}

impl<K: Serial + Ord> SerialCtx for BTreeSet<K> {
    fn serial_ctx<W: Write>(
        &self,
        size_len: schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err> {
        schema::serial_length(self.len(), size_len, out)?;
        serial_set_no_length(self, out)
    }
}

impl<K: Deserial + Ord + Copy> DeserialCtx for BTreeSet<K> {
    fn deserial_ctx<R: Read>(
        size_len: schema::SizeLength,
        ensure_ordered: bool,
        source: &mut R,
    ) -> ParseResult<Self> {
        let len = schema::deserial_length(source, size_len)?;
        if ensure_ordered {
            deserial_set_no_length(source, len)
        } else {
            deserial_set_no_length_no_order_check(source, len)
        }
    }
}

impl<K: Serial + Ord, V: Serial> SerialCtx for BTreeMap<K, V> {
    fn serial_ctx<W: Write>(
        &self,
        size_len: schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err> {
        schema::serial_length(self.len(), size_len, out)?;
        serial_map_no_length(self, out)
    }
}

impl<K: Deserial + Ord + Copy, V: Deserial> DeserialCtx for BTreeMap<K, V> {
    fn deserial_ctx<R: Read>(
        size_len: schema::SizeLength,
        ensure_ordered: bool,
        source: &mut R,
    ) -> ParseResult<Self> {
        let len = schema::deserial_length(source, size_len)?;
        if ensure_ordered {
            deserial_map_no_length(source, len)
        } else {
            deserial_map_no_length_no_order_check(source, len)
        }
    }
}

/// Serialization for HashSet given a size_len.
/// Values are not serialized in any particular order.
impl<K: Serial> SerialCtx for HashSet<K> {
    fn serial_ctx<W: Write>(
        &self,
        size_len: schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err> {
        schema::serial_length(self.len(), size_len, out)?;
        serial_hashset_no_length(self, out)
    }
}

/// Deserialization for HashSet given a size_len.
/// Values are not verified to be in any particular order and setting
/// ensure_ordering have no effect.
impl<K: Deserial + Eq + Hash> DeserialCtx for HashSet<K> {
    fn deserial_ctx<R: Read>(
        size_len: schema::SizeLength,
        _ensure_ordered: bool,
        source: &mut R,
    ) -> ParseResult<Self> {
        let len = schema::deserial_length(source, size_len)?;
        deserial_hashset_no_length(source, len)
    }
}

/// Serialization for HashMap given a size_len.
/// Keys are not serialized in any particular order.
impl<K: Serial, V: Serial> SerialCtx for HashMap<K, V> {
    fn serial_ctx<W: Write>(
        &self,
        size_len: schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err> {
        schema::serial_length(self.len(), size_len, out)?;
        serial_hashmap_no_length(self, out)
    }
}

/// Deserialization for HashMap given a size_len.
/// Keys are not verified to be in any particular order and setting
/// ensure_ordering have no effect.
impl<K: Deserial + Eq + Hash, V: Deserial> DeserialCtx for HashMap<K, V> {
    fn deserial_ctx<R: Read>(
        size_len: schema::SizeLength,
        _ensure_ordered: bool,
        source: &mut R,
    ) -> ParseResult<Self> {
        let len = schema::deserial_length(source, size_len)?;
        deserial_hashmap_no_length(source, len)
    }
}

impl<T: Serial> SerialCtx for &[T] {
    fn serial_ctx<W: Write>(
        &self,
        size_len: schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err> {
        schema::serial_length(self.len(), size_len, out)?;
        serial_vector_no_length(self, out)
    }
}

impl<T: Serial> SerialCtx for Vec<T> {
    fn serial_ctx<W: Write>(
        &self,
        size_len: schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err> {
        self.as_slice().serial_ctx(size_len, out)
    }
}

impl<T: Deserial> DeserialCtx for Vec<T> {
    fn deserial_ctx<R: Read>(
        size_len: schema::SizeLength,
        _ensure_ordered: bool,
        source: &mut R,
    ) -> ParseResult<Self> {
        let len = schema::deserial_length(source, size_len)?;
        deserial_vector_no_length(source, len)
    }
}

impl SerialCtx for &str {
    fn serial_ctx<W: Write>(
        &self,
        size_len: schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err> {
        schema::serial_length(self.len(), size_len, out)?;
        serial_vector_no_length(&self.as_bytes().to_vec(), out)
    }
}

impl SerialCtx for String {
    fn serial_ctx<W: Write>(
        &self,
        size_len: schema::SizeLength,
        out: &mut W,
    ) -> Result<(), W::Err> {
        self.as_str().serial_ctx(size_len, out)
    }
}

impl DeserialCtx for String {
    fn deserial_ctx<R: Read>(
        size_len: schema::SizeLength,
        _ensure_ordered: bool,
        source: &mut R,
    ) -> ParseResult<Self> {
        let len = schema::deserial_length(source, size_len)?;
        let bytes = deserial_vector_no_length(source, len)?;
        let res = String::from_utf8(bytes).map_err(|_| ParseError::default())?;
        Ok(res)
    }
}
