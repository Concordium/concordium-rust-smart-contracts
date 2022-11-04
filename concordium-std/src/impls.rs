use crate::{
    cell::UnsafeCell,
    convert::{self, TryInto},
    fmt,
    marker::PhantomData,
    mem, num,
    num::NonZeroU32,
    prims,
    traits::*,
    types::*,
    vec::Vec,
    String,
};
pub(crate) use concordium_contracts_common::*;
use mem::MaybeUninit;

/// Mapped to i32::MIN + 1.
impl convert::From<()> for Reject {
    #[inline(always)]
    fn from(_: ()) -> Self { unsafe { num::NonZeroI32::new_unchecked(i32::MIN + 1) }.into() }
}

/// Mapped to i32::MIN + 2.
impl convert::From<ParseError> for Reject {
    #[inline(always)]
    fn from(_: ParseError) -> Self {
        unsafe { num::NonZeroI32::new_unchecked(i32::MIN + 2) }.into()
    }
}

/// Full is mapped to i32::MIN + 3,
/// Malformed is mapped to i32::MIN + 4.
impl From<LogError> for Reject {
    #[inline(always)]
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => unsafe { crate::num::NonZeroI32::new_unchecked(i32::MIN + 3) }.into(),
            LogError::Malformed => {
                unsafe { crate::num::NonZeroI32::new_unchecked(i32::MIN + 4) }.into()
            }
        }
    }
}

/// MissingInitPrefix is mapped to i32::MIN + 5,
/// TooLong to i32::MIN + 6,
/// ContainsDot to i32::MIN + 9, and
/// InvalidCharacters to i32::MIN + 10.
impl From<NewContractNameError> for Reject {
    fn from(nre: NewContractNameError) -> Self {
        match nre {
            NewContractNameError::MissingInitPrefix => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 5).into()
            },
            NewContractNameError::TooLong => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 6).into()
            },
            NewContractNameError::ContainsDot => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 9).into()
            },
            NewContractNameError::InvalidCharacters => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 10).into()
            },
        }
    }
}

/// MissingDotSeparator is mapped to i32::MIN + 7,
/// TooLong to i32::MIN + 8, and
/// InvalidCharacters to i32::MIN + 11.
impl From<NewReceiveNameError> for Reject {
    fn from(nre: NewReceiveNameError) -> Self {
        match nre {
            NewReceiveNameError::MissingDotSeparator => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 7).into()
            },
            NewReceiveNameError::TooLong => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 8).into()
            },
            NewReceiveNameError::InvalidCharacters => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 11).into()
            },
        }
    }
}

/// The error code is i32::MIN + 12.
impl From<NotPayableError> for Reject {
    #[inline(always)]
    fn from(_: NotPayableError) -> Self {
        unsafe { crate::num::NonZeroI32::new_unchecked(i32::MIN + 12) }.into()
    }
}

/// AmountTooLarge is i32::MIN + 13,
/// MissingAccount is i32::MIN + 14.
impl From<TransferError> for Reject {
    #[inline(always)]
    fn from(te: TransferError) -> Self {
        match te {
            TransferError::AmountTooLarge => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 13).into()
            },
            TransferError::MissingAccount => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 14).into()
            },
        }
    }
}

/// AmountTooLarge is i32::MIN + 15,
/// MissingAccount is i32::MIN + 16,
/// MissingContract is i32::MIN + 17,
/// MissingEntrypoint is i32::MIN + 18,
/// MessageFailed is i32::MIN + 19,
/// LogicReject is i32::MIN + 20,
/// Trap is i32::MIN + 21.
impl<T> From<CallContractError<T>> for Reject {
    #[inline(always)]
    fn from(cce: CallContractError<T>) -> Self {
        match cce {
            CallContractError::AmountTooLarge => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 15).into()
            },
            CallContractError::MissingAccount => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 16).into()
            },
            CallContractError::MissingContract => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 17).into()
            },
            CallContractError::MissingEntrypoint => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 18).into()
            },
            CallContractError::MessageFailed => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 19).into()
            },
            CallContractError::LogicReject {
                ..
            } => unsafe { crate::num::NonZeroI32::new_unchecked(i32::MIN + 20).into() },
            CallContractError::Trap => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 21).into()
            },
        }
    }
}

/// MissingModule is i32::MIN + 22,
/// MissingContract is i32::MIN + 23,
/// UnsupportedModuleVersion is i32::MIN + 24.
impl From<UpgradeError> for Reject {
    #[inline(always)]
    fn from(te: UpgradeError) -> Self {
        match te {
            UpgradeError::MissingModule => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 22).into()
            },
            UpgradeError::MissingContract => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 23).into()
            },
            UpgradeError::UnsupportedModuleVersion => unsafe {
                crate::num::NonZeroI32::new_unchecked(i32::MIN + 24).into()
            },
        }
    }
}

/// Query account balance error missing account is i32::MIN + 25.
impl From<QueryAccountBalanceError> for Reject {
    #[inline(always)]
    fn from(_: QueryAccountBalanceError) -> Self {
        unsafe { crate::num::NonZeroI32::new_unchecked(i32::MIN + 25).into() }
    }
}

/// Query contract balance error missing contract is i32::MIN + 26.
impl From<QueryContractBalanceError> for Reject {
    #[inline(always)]
    fn from(_: QueryContractBalanceError) -> Self {
        unsafe { crate::num::NonZeroI32::new_unchecked(i32::MIN + 26).into() }
    }
}

/// Return values are intended to be produced by writing to the
/// [ExternReturnValue] buffer, either in a high-level interface via
/// serialization, or in a low-level interface by manually using the [Write]
/// trait's interface.
impl Write for ExternReturnValue {
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
        let num_bytes = unsafe { prims::write_output(buf.as_ptr(), len, self.current_position) };
        self.current_position += num_bytes; // safe because of check above that len + pos is small enough
        Ok(num_bytes as usize)
    }
}

impl ExternReturnValue {
    #[inline(always)]
    /// Create a return value cursor that starts at the beginning.
    /// Note that there is a single return value per contract invocation, so
    /// multiple calls to open will give access to writing the same return
    /// value. Thus this function should only be used once per contract
    /// invocation.
    pub fn open() -> Self {
        Self {
            current_position: 0,
        }
    }
}

impl StateEntry {
    /// Open a new state entry with its `current_position` set to `0`.
    pub(crate) fn open(state_entry_id: StateEntryId, key: Vec<u8>) -> Self {
        Self {
            state_entry_id,
            key,
            current_position: 0,
        }
    }
}

impl HasStateEntry for StateEntry {
    type Error = ();
    type StateEntryData = ();
    type StateEntryKey = ();

    #[inline(always)]
    fn move_to_start(&mut self) { self.current_position = 0; }

    #[inline(always)]
    fn size(&self) -> Result<u32, Self::Error> {
        let res = unsafe { prims::state_entry_size(self.state_entry_id) };
        match res {
            u32::MAX => Err(()),
            _ => Ok(res),
        }
    }

    fn truncate(&mut self, new_size: u32) -> Result<(), Self::Error> {
        let cur_size = self.size()?;
        if cur_size > new_size {
            self.resize(new_size)?;
        }
        Ok(())
    }

    fn get_key(&self) -> &[u8] { &self.key }

    fn resize(&mut self, new_size: u32) -> Result<(), Self::Error> {
        let res = unsafe { prims::state_entry_resize(self.state_entry_id, new_size) };
        match res {
            1 => {
                if self.current_position > new_size {
                    self.current_position = new_size;
                }
                Ok(())
            }
            _ => Err(()),
        }
    }
}

impl Seek for StateEntry {
    type Err = ();

    #[inline]
    // Make sure the inline is OK. This is a relatively big function, but once
    // specialized to one of the branches it should benefit from inlining.
    fn seek(&mut self, pos: SeekFrom) -> Result<u32, Self::Err> {
        use SeekFrom::*;
        let end = self.size()?;
        match pos {
            Start(offset) => {
                if offset <= end {
                    self.current_position = offset;
                    Ok(offset)
                } else {
                    Err(())
                }
            }
            End(delta) => {
                if delta > 0 {
                    Err(()) // cannot seek beyond the end
                } else {
                    // due to two's complement representation of values we do not have to
                    // distinguish on whether we go forward or backwards. Reinterpreting the bits
                    // and adding unsigned values is the same as subtracting the
                    // absolute value.
                    let new_offset = end.wrapping_add(delta as u32);
                    if new_offset <= end {
                        self.current_position = new_offset;
                        Ok(new_offset)
                    } else {
                        Err(())
                    }
                }
            }
            Current(delta) => {
                // due to two's complement representation of values we do not have to
                // distinguish on whether we go forward or backwards.
                let new_offset = self.current_position + delta as u32;
                if new_offset <= end {
                    self.current_position = new_offset;
                    Ok(new_offset)
                } else {
                    Err(())
                }
            }
        }
    }

    #[inline(always)]
    fn cursor_position(&self) -> u32 { self.current_position }
}

impl Read for StateEntry {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
        let len: u32 = buf.len().try_into().map_err(|_| ParseError::default())?;
        let num_read = unsafe {
            prims::state_entry_read(
                self.state_entry_id,
                buf.as_mut_ptr(),
                len,
                self.current_position,
            )
        };
        if num_read == u32::MAX {
            return Err(ParseError::default()); // Entry did not exist.
        }
        self.current_position += num_read;
        Ok(num_read as usize)
    }

    /// Read a `u64` in little-endian format. This is optimized to not
    /// initialize a dummy value before calling an external function.
    fn read_u64(&mut self) -> ParseResult<u64> {
        let mut bytes: MaybeUninit<[u8; 8]> = MaybeUninit::uninit();
        let num_read = unsafe {
            prims::state_entry_read(
                self.state_entry_id,
                bytes.as_mut_ptr() as *mut u8,
                8,
                self.current_position,
            )
        };
        if num_read == u32::MAX {
            return Err(ParseError::default()); // Entry did not exist.
        }
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
        let num_read = unsafe {
            prims::state_entry_read(
                self.state_entry_id,
                bytes.as_mut_ptr() as *mut u8,
                4,
                self.current_position,
            )
        };
        if num_read == u32::MAX {
            return Err(ParseError::default()); // Entry did not exist.
        }
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
        let num_read = unsafe {
            prims::state_entry_read(
                self.state_entry_id,
                bytes.as_mut_ptr() as *mut u8,
                1,
                self.current_position,
            )
        };
        if num_read == u32::MAX {
            return Err(ParseError::default()); // Entry did not exist.
        }
        self.current_position += num_read;
        if num_read == 1 {
            unsafe { Ok(bytes.assume_init()[0]) }
        } else {
            Err(ParseError::default())
        }
    }
}

impl Write for StateEntry {
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
        let num_bytes = unsafe {
            prims::state_entry_write(self.state_entry_id, buf.as_ptr(), len, self.current_position)
        };
        if num_bytes == u32::MAX {
            return Err(()); // Entry did not exist.
        }
        self.current_position += num_bytes; // safe because of check above that len + pos is small enough
        Ok(num_bytes as usize)
    }
}

impl<StateApi: HasStateApi> VacantEntryRaw<StateApi> {
    /// Create a new `VacantEntryRaw`.
    pub(crate) fn new(key: Key, state_api: StateApi) -> Self {
        Self {
            key,
            state_api,
        }
    }

    /// Gets a reference to the key that would be used when inserting a value
    /// through the `VacantEntryRaw`.
    #[inline(always)]
    pub fn key(&self) -> &[u8] { &self.key }

    /// Sets the value of the entry with the [`VacantEntryRaw`’s](Self) key.
    pub fn insert_raw(mut self, value: &[u8]) -> Result<StateApi::EntryType, StateError> {
        let mut entry = self.state_api.create_entry(&self.key)?;
        entry.write_all(value).unwrap_abort(); // Writing to state cannot fail.
        entry.move_to_start(); // Reset cursor.
        Ok(entry)
    }

    /// Sets the value of the entry with the `VacantEntryRaw`’s key.
    /// This differs from
    /// [`insert_raw`](Self::insert_raw) in that it automatically serializes
    /// the provided value. [`insert`](Self::insert) should be preferred
    /// for values that can be directly converted to byte arrays, e.g., any
    /// value that implements [`AsRef<[u8]>`](AsRef).
    pub fn insert<V: Serial>(mut self, value: &V) -> Result<StateApi::EntryType, StateError> {
        let mut entry = self.state_api.create_entry(&self.key)?;
        // Writing to state cannot fail unless the value is too large (more than 2^31
        // bytes). We can't do much about that.
        value.serial(&mut entry).unwrap_abort();
        entry.move_to_start(); // Reset cursor.
        Ok(entry)
    }
}

impl<StateApi: HasStateApi> OccupiedEntryRaw<StateApi> {
    /// Create a new `OccupiedEntryRaw`.
    pub(crate) fn new(state_entry: StateApi::EntryType) -> Self {
        Self {
            state_entry,
        }
    }

    /// Gets a reference to the key that would be used when inserting a value
    /// through the `OccupiedEntryRaw`.
    #[inline(always)]
    pub fn key(&self) -> &[u8] { self.state_entry.get_key() }

    /// Gets a reference to the [`HasStateEntry`] type in the entry.
    #[inline(always)]
    pub fn get_ref(&self) -> &StateApi::EntryType { &self.state_entry }

    /// Converts the entry into its [`HasStateEntry`] type.
    ///
    /// If you need multiple mutable references to the `OccupiedEntryRaw`, see
    /// [`get_mut`][Self::get_mut].
    #[inline(always)]
    pub fn get(self) -> StateApi::EntryType { self.state_entry }

    /// Gets a mutable reference to the [`HasStateEntry`] type in the entry.
    ///
    /// If you need access to a [`HasStateEntry`], which can outlive the
    /// `OccupiedEntryRaw`, see [`get`][Self::get].
    #[inline(always)]
    pub fn get_mut(&mut self) -> &mut StateApi::EntryType { &mut self.state_entry }

    /// Sets the value of the entry with the `OccupiedEntryRaw`'s key.
    pub fn insert_raw(&mut self, value: &[u8]) {
        self.state_entry.move_to_start();
        self.state_entry.write_all(value).unwrap_abort();

        // Truncate any data leftover from previous value.
        self.state_entry.truncate(value.len() as u32).unwrap_abort();
    }

    /// Sets the value of the entry with the [`OccupiedEntryRaw`'s](Self) key.
    /// This differs from [`insert_raw`](Self::insert_raw) in that it
    /// automatically serializes the value. The [`insert`](Self::insert)
    /// should be preferred if the value is already a byte array.
    pub fn insert<V: Serial>(&mut self, value: &V) {
        // Truncate so that no data is leftover from previous value.
        self.state_entry.truncate(0).unwrap_abort();
        self.state_entry.move_to_start();
        value.serial(&mut self.state_entry).unwrap_abort()
    }
}

impl<StateApi: HasStateApi> EntryRaw<StateApi> {
    /// Ensures a value is in the entry by inserting the default if empty, and
    /// returns the [`HasStateEntry`] type for the entry.
    pub fn or_insert_raw(self, default: &[u8]) -> Result<StateApi::EntryType, StateError> {
        match self {
            EntryRaw::Vacant(vac) => vac.insert_raw(default),
            EntryRaw::Occupied(occ) => Ok(occ.get()),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and
    /// returns the [`HasStateEntry`] type. This differs from
    /// [`or_insert_raw`](Self::or_insert_raw) in that it automatically
    /// serializes the provided value. [`or_insert`](Self::or_insert) should
    /// be preferred for values that can be directly converted to byte
    /// arrays, e.g., any value that implements [`AsRef<[u8]>`](AsRef).
    pub fn or_insert<V: Serial>(self, default: &V) -> StateApi::EntryType {
        match self {
            EntryRaw::Vacant(vac) => vac.insert(default).unwrap_abort(),
            EntryRaw::Occupied(occ) => occ.get(),
        }
    }

    /// Returns a reference to this entry's key.
    pub fn key(&self) -> &[u8] {
        match self {
            EntryRaw::Vacant(vac) => vac.key(),
            EntryRaw::Occupied(occ) => occ.key(),
        }
    }
}

impl<'a, K, V, StateApi> VacantEntry<'a, K, V, StateApi>
where
    K: Serial,
    V: Serial,
    StateApi: HasStateApi,
{
    /// Create a new `VacantEntry`.
    pub(crate) fn new(key: K, key_bytes: Vec<u8>, state_api: StateApi) -> Self {
        Self {
            key,
            key_bytes,
            state_api,
            _lifetime_marker: PhantomData,
        }
    }

    /// Get a reference to the `VacantEntry`'s key.
    #[inline(always)]
    pub fn key(&self) -> &K { &self.key }

    /// Take ownership of the key.
    #[inline(always)]
    pub fn into_key(self) -> K { self.key }

    /// Sets the value of the entry with the `VacantEntry`'s key.
    pub fn insert(mut self, value: V) -> OccupiedEntry<'a, K, V, StateApi> {
        // Writing to state cannot fail.
        let mut state_entry = self.state_api.create_entry(&self.key_bytes).unwrap_abort();
        value.serial(&mut state_entry).unwrap_abort();
        state_entry.move_to_start(); // Reset cursor.
        OccupiedEntry {
            key: self.key,
            value,
            modified: false,
            state_entry,
            _lifetime_marker: self._lifetime_marker,
        }
    }
}

impl<'a, K, V, StateApi> OccupiedEntry<'a, K, V, StateApi>
where
    K: Serial,
    V: Serial,
    StateApi: HasStateApi,
{
    /// Create a new `OccupiedEntry`.
    pub(crate) fn new(key: K, value: V, state_entry: StateApi::EntryType) -> Self {
        Self {
            key,
            value,
            modified: false,
            state_entry,
            _lifetime_marker: PhantomData,
        }
    }

    /// Get a reference to the key that is associated with this entry.
    #[inline(always)]
    pub fn key(&self) -> &K { &self.key }

    /// Get an immutable reference to the value contained in this entry.
    #[inline(always)]
    pub fn get_ref(&self) -> &V { &self.value }

    /// Modify the value in the entry, and possibly return
    /// some information.
    #[inline]
    pub fn modify<F, A>(&mut self, f: F) -> A
    where
        // NB: This closure cannot return a reference to V. The reason for this is
        // that the type of the closure is really `for<'b>FnOnce<&'b mut V> -> A`.
        // In particular, the lifetime of the reference the closure gets is not tied directly to the
        // lifetime of `Self`.
        F: FnOnce(&mut V) -> A, {
        let res = f(&mut self.value);
        self.store_value();
        res
    }

    /// Like [`modify`](Self::modify), but allows the closure to signal failure,
    /// aborting the update.
    pub fn try_modify<F, A, E>(&mut self, f: F) -> Result<A, E>
    where
        F: FnOnce(&mut V) -> Result<A, E>, {
        let res = f(&mut self.value)?;
        self.store_value();
        Ok(res)
    }
}

impl<'a, K, V, StateApi> OccupiedEntry<'a, K, V, StateApi>
where
    V: Serial,
    StateApi: HasStateApi,
{
    pub(crate) fn store_value(&mut self) {
        // First truncate it back to 0. This is not ideal in some cases, since
        // it is a needless call.
        // An alternative would be to first write to a temporary buffer,
        // resize the entry to the size of that buffer, and then copy that buffer in.
        // That has the disadvantage of allocating an intermediate buffer.
        self.state_entry.truncate(0).unwrap_abort();
        // If we did not manage to serialize we just abort. This can only happen
        // if (1) one of the serial implementations raises an error, which it should not
        // in normal circumstances or (2) we have run of out of space to write
        // the entry. However the limit to entry size is 2^31 so this
        // will not happen in practice.
        self.value.serial(&mut self.state_entry).unwrap_abort();
    }
}

impl<'a, K, V, StateApi> Entry<'a, K, V, StateApi>
where
    K: Serial,
    V: Serial,
    StateApi: HasStateApi,
{
    /// Return whether the entry is vacant.
    #[inline(always)]
    pub fn is_vacant(&self) -> bool { matches!(self, Entry::Vacant(_)) }

    /// Return whether the entry is occupied.
    #[inline(always)]
    pub fn is_occupied(&self) -> bool { matches!(self, Entry::Occupied(_)) }

    /// If the entry is [`Occupied`](Entry::Occupied) return `Ok`. Otherwise
    /// return the supplied error.
    #[inline]
    pub fn occupied_or<E>(self, e: E) -> Result<OccupiedEntry<'a, K, V, StateApi>, E> {
        match self {
            Entry::Vacant(_) => Err(e),
            Entry::Occupied(oe) => Ok(oe),
        }
    }

    /// If the entry is [`Vacant`](Entry::Vacant) return `Ok`. Otherwise return
    /// the supplied error.
    #[inline]
    pub fn vacant_or<E>(self, e: E) -> Result<VacantEntry<'a, K, V, StateApi>, E> {
        match self {
            Entry::Vacant(vac) => Ok(vac),
            Entry::Occupied(_) => Err(e),
        }
    }

    /// Ensure a value is in the entry by inserting the provided value if the
    /// entry is vacant.
    pub fn or_insert(self, value: V) -> OccupiedEntry<'a, K, V, StateApi> {
        match self {
            Entry::Vacant(vac) => vac.insert(value),
            Entry::Occupied(oe) => oe,
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default
    /// function if empty.
    pub fn or_insert_with<F>(self, default: F) -> OccupiedEntry<'a, K, V, StateApi>
    where
        F: FnOnce() -> V, {
        match self {
            Entry::Vacant(vac) => vac.insert(default()),
            Entry::Occupied(oe) => oe,
        }
    }

    /// If the entry is occupied apply the given function to its contents.
    /// If the function returns an error the contents are not updated.
    /// **If the supplied function returns an error then it should not modify
    /// the given value. If it does so than the map will become
    /// inconsistent.** If the entry is vacant no changes are made.
    pub fn and_try_modify<F, E>(mut self, f: F) -> Result<Entry<'a, K, V, StateApi>, E>
    where
        F: FnOnce(&mut V) -> Result<(), E>, {
        if let Entry::Occupied(ref mut occ) = self {
            occ.try_modify(f)?;
        }
        Ok(self)
    }

    /// If the entry is occupied apply the given function to its contents.
    /// If the entry is vacant no changes are made.
    pub fn and_modify<F>(mut self, f: F) -> Entry<'a, K, V, StateApi>
    where
        F: FnOnce(&mut V), {
        if let Entry::Occupied(ref mut occ) = self {
            occ.modify(f);
        }
        self
    }

    /// Return a reference to this entry's key.
    pub fn key(&self) -> &K {
        match self {
            Entry::Vacant(vac) => vac.key(),
            Entry::Occupied(occ) => occ.key(),
        }
    }
}

impl<'a, K, V, StateApi> Entry<'a, K, V, StateApi>
where
    K: Serial,
    V: Serial + Default,
    StateApi: HasStateApi,
{
    /// Ensures a value is in the entry by inserting the default value if empty.
    pub fn or_default(self) -> OccupiedEntry<'a, K, V, StateApi> {
        self.or_insert_with(Default::default)
    }
}

/// The (i.e., location in the contract state trie) at which the
/// "allocator"/state builder stores "next location". The values stored at this
/// location are 64-bit integers.
const NEXT_ITEM_PREFIX_KEY: [u8; 8] = 0u64.to_le_bytes();
#[cfg(test)]
const GENERIC_MAP_PREFIX: u64 = 1;
/// Initial location to store in [NEXT_ITEM_PREFIX_KEY]. For example, the
/// initial call to "new_state_box" will allocate the box at this location.
pub(crate) const INITIAL_NEXT_ITEM_PREFIX: [u8; 8] = 2u64.to_le_bytes();

impl HasStateApi for ExternStateApi {
    type EntryType = StateEntry;
    type IterType = ExternStateIter;

    fn create_entry(&mut self, key: &[u8]) -> Result<Self::EntryType, StateError> {
        let key_start = key.as_ptr();
        let key_len = key.len() as u32; // Wasm usize == 32bit.
        let entry_id = unsafe { prims::state_create_entry(key_start, key_len) };
        if entry_id == u64::MAX {
            return Err(StateError::SubtreeLocked);
        }
        Ok(StateEntry::open(entry_id, key.to_vec()))
    }

    fn lookup_entry(&self, key: &[u8]) -> Option<Self::EntryType> {
        let key_start = key.as_ptr();
        let key_len = key.len() as u32; // Wasm usize == 32bit.
        let entry_id = unsafe { prims::state_lookup_entry(key_start, key_len) };
        if entry_id == u64::MAX {
            None
        } else {
            Some(StateEntry::open(entry_id, key.to_vec()))
        }
    }

    fn delete_entry(&mut self, entry: Self::EntryType) -> Result<(), StateError> {
        let key = entry.get_key();
        let res = unsafe { prims::state_delete_entry(key.as_ptr(), key.len() as u32) };
        match res {
            0 => Err(StateError::SubtreeLocked),
            1 => Err(StateError::EntryNotFound),
            2 => Ok(()),
            _ => crate::trap(), // cannot happen
        }
    }

    fn delete_prefix(&mut self, prefix: &[u8]) -> Result<bool, StateError> {
        let res = unsafe { prims::state_delete_prefix(prefix.as_ptr(), prefix.len() as u32) };
        match res {
            0 => Err(StateError::SubtreeLocked),
            1 => Ok(false),
            2 => Ok(true),
            _ => crate::trap(), // cannot happen
        }
    }

    fn iterator(&self, prefix: &[u8]) -> Result<Self::IterType, StateError> {
        let prefix_start = prefix.as_ptr();
        let prefix_len = prefix.len() as u32; // Wasm usize == 32bit.
        let iterator_id = unsafe { prims::state_iterate_prefix(prefix_start, prefix_len) };
        match iterator_id {
            OK_NONE => Err(StateError::SubtreeWithPrefixNotFound),
            ERR => Err(StateError::IteratorLimitForPrefixExceeded),
            iterator_id => Ok(ExternStateIter {
                iterator_id,
            }),
        }
    }

    fn delete_iterator(&mut self, iter: Self::IterType) {
        // This call can never fail because the only way to get an `ExternStateIter`
        // is through `StateApi::iterator(..)`. And this call consumes
        // the iterator.
        // These conditions rule out the two types of errors that the prims
        // call can return, iterator not found and iterator already deleted.
        // The iterator can also be deleted with `delete_iterator_by_id`, but that is
        // only called when a [StateMapIter] or [StateSetIter] is dropped (which
        // also drops the [ExternStateIter]). Again ruling out the already
        // deleted error.
        unsafe { prims::state_iterator_delete(iter.iterator_id) };
    }
}

/// Encoding of Ok(None) that is returned by some host functions.
const OK_NONE: u64 = u64::MAX;
/// Encoding of Err that is returned by some host functions.
const ERR: u64 = u64::MAX & !(1u64 << 62);

impl Iterator for ExternStateIter {
    type Item = StateEntry;

    fn next(&mut self) -> Option<Self::Item> {
        let res = unsafe { prims::state_iterator_next(self.iterator_id) };
        match res {
            OK_NONE => None,
            // This next case means that an iterator never existed or was deleted.
            // In both cases, it is not possible to call `next` on such an iterator with the current
            // API. The only way to get an iterator is through
            // [HasStateApi::iterator] and the only way to delete it is through
            // [HasStateApi::delete_iterator].
            ERR => None,
            _ => {
                // This will always return a valid size, because the iterator is guaranteed to
                // exist.
                let key_size = unsafe { prims::state_iterator_key_size(self.iterator_id) };
                let mut key = Vec::with_capacity(key_size as usize);
                // The key will always be read, because the iterator is guaranteed to exist.
                unsafe {
                    let num_read = prims::state_iterator_key_read(
                        self.iterator_id,
                        key.as_mut_ptr(),
                        key_size,
                        0,
                    );
                    key.set_len(num_read as usize);
                };
                Some(StateEntry::open(res, key))
            }
        }
    }
}

impl<K, V, S> StateMap<K, V, S>
where
    S: HasStateApi,
    K: Serialize,
    V: Serial + DeserialWithState<S>,
{
    /// Lookup the value with the given key. Return [None] if there is no value
    /// with the given key.
    pub fn get(&self, key: &K) -> Option<StateRef<V>> {
        let k = self.key_with_map_prefix(key);
        self.state_api.lookup_entry(&k).map(|mut entry| {
            // Unwrapping is safe when using only the high-level API.
            StateRef::new(V::deserial_with_state(&self.state_api, &mut entry).unwrap_abort())
        })
    }

    /// Lookup a mutable reference to the value with the given key. Return
    /// [None] if there is no value with the given key.
    pub fn get_mut(&self, key: &K) -> Option<StateRefMut<V, S>> {
        let k = self.key_with_map_prefix(key);
        let entry = self.state_api.lookup_entry(&k)?;
        Some(StateRefMut::new(entry, self.state_api.clone()))
    }

    /// Inserts the value with the given key. If a value already exists at the
    /// given key it is replaced and the old value is returned.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let key_bytes = self.key_with_map_prefix(&key);
        // Unwrapping is safe because iter() holds a reference to the stateset.
        match self.state_api.entry(key_bytes) {
            EntryRaw::Vacant(vac) => {
                let _ = vac.insert(&value).unwrap_abort();
                None
            }
            EntryRaw::Occupied(mut occ) => {
                // Unwrapping is safe when using only the high-level API.
                let old_value =
                    V::deserial_with_state(&self.state_api, occ.get_mut()).unwrap_abort();
                occ.insert(&value);
                Some(old_value)
            }
        }
    }

    /// Get an entry for the given key.
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V, S> {
        let key_bytes = self.key_with_map_prefix(&key);
        // Unwrapping is safe because iter() holds a reference to the stateset.
        match self.state_api.lookup_entry(&key_bytes) {
            None => Entry::Vacant(VacantEntry::new(key, key_bytes, self.state_api.clone())),
            Some(mut state_entry) => {
                // Unwrapping is safe when using only the high-level API.
                let value =
                    V::deserial_with_state(&self.state_api, &mut state_entry).unwrap_abort();
                Entry::Occupied(OccupiedEntry::new(key, value, state_entry))
            }
        }
    }

    /// Return `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool { self.state_api.lookup_entry(&self.prefix).is_none() }

    /// Clears the map, removing all key-value pairs.
    /// This also includes values pointed at, if `V`, for example, is a
    /// [StateBox]. **If applicable use [`clear_flat`](Self::clear_flat)
    /// instead.**
    pub fn clear(&mut self)
    where
        V: Deletable, {
        // Delete all values pointed at by the statemap. This is necessary if `V` is a
        // StateBox/StateMap.
        for (_, value) in self.iter() {
            value.value.delete()
        }

        // Then delete the map itself.
        // Unwrapping is safe when only using the high-level API.
        self.state_api.delete_prefix(&self.prefix).unwrap_abort();
    }

    /// Clears the map, removing all key-value pairs.
    /// **This should be used over [`clear`](Self::clear) if it is
    /// applicable.** It avoids recursive deletion of values since the
    /// values are required to be _flat_.
    ///
    /// Unfortunately it is not possible to automatically choose between these
    /// implementations. Once Rust gets trait specialization then this might
    /// be possible.
    pub fn clear_flat(&mut self)
    where
        V: Deserial, {
        // Delete only the map itself since the values have no pointers to state.
        // Thus there will be no dangling references.
        // Unwrapping is safe when only using the high-level API.
        self.state_api.delete_prefix(&self.prefix).unwrap_abort();
    }

    /// Remove a key from the map, returning the value at the key if the key was
    /// previously in the map.
    ///
    /// *Caution*: If `V` is a [StateBox], [StateMap], then it is
    /// important to call [`Deletable::delete`] on the value returned when
    /// you're finished with it. Otherwise, it will remain in the contract
    /// state.
    #[must_use]
    pub fn remove_and_get(&mut self, key: &K) -> Option<V> {
        let key_bytes = self.key_with_map_prefix(key);
        // Unwrapping is safe because iter() holds a reference to the stateset.
        let entry_raw = self.state_api.entry(key_bytes);
        match entry_raw {
            EntryRaw::Vacant(_) => None,
            EntryRaw::Occupied(mut occ) => {
                // Unwrapping safe in high-level API.
                let old_value =
                    V::deserial_with_state(&self.state_api, occ.get_mut()).unwrap_abort();
                let _existed = self.state_api.delete_entry(occ.state_entry);
                Some(old_value)
            }
        }
    }

    /// Remove a key from the map.
    /// This also deletes the value in the state.
    pub fn remove(&mut self, key: &K)
    where
        V: Deletable, {
        if let Some(v) = self.remove_and_get(key) {
            v.delete()
        }
    }

    /// Serializes the key and prepends the unique map prefix to it.
    fn key_with_map_prefix(&self, key: &K) -> Vec<u8> {
        let mut key_with_prefix = self.prefix.to_vec();
        key.serial(&mut key_with_prefix).unwrap_abort();
        key_with_prefix
    }
}

impl<'a, K, V, S: HasStateApi> Drop for StateMapIter<'a, K, V, S> {
    fn drop(&mut self) {
        // Delete the iterator to unlock the subtree.
        if let Some(valid) = self.state_iter.take() {
            self.state_api.delete_iterator(valid);
        }
    }
}

impl<K, V, S> StateMap<K, V, S>
where
    S: HasStateApi,
{
    pub(crate) fn open(state_api: S, prefix: [u8; 8]) -> Self {
        Self {
            _marker_key: PhantomData,
            _marker_value: PhantomData,
            prefix,
            state_api,
        }
    }

    /// Get an iterator over the key-value pairs of the map. The iterator
    /// returns values in increasing order of keys, where keys are ordered
    /// lexicographically via their serializations.
    pub fn iter(&self) -> StateMapIter<'_, K, V, S> {
        match self.state_api.iterator(&self.prefix) {
            Ok(state_iter) => StateMapIter {
                state_iter:       Some(state_iter),
                state_api:        self.state_api.clone(),
                _lifetime_marker: PhantomData,
            },
            Err(StateError::SubtreeWithPrefixNotFound) => StateMapIter {
                state_iter:       None,
                state_api:        self.state_api.clone(),
                _lifetime_marker: PhantomData,
            },
            _ => crate::trap(),
        }
    }

    /// Like [iter](Self::iter), but allows modifying the values during
    /// iteration.
    pub fn iter_mut(&mut self) -> StateMapIterMut<'_, K, V, S> {
        match self.state_api.iterator(&self.prefix) {
            Ok(state_iter) => StateMapIterMut {
                state_iter:       Some(state_iter),
                state_api:        self.state_api.clone(),
                _lifetime_marker: PhantomData,
            },
            Err(StateError::SubtreeWithPrefixNotFound) => StateMapIterMut {
                state_iter:       None,
                state_api:        self.state_api.clone(),
                _lifetime_marker: PhantomData,
            },
            _ => crate::trap(),
        }
    }
}

impl<'a, K, V, S: HasStateApi> Iterator for StateMapIter<'a, K, V, S>
where
    K: Deserial + 'a,
    V: DeserialWithState<S> + 'a,
{
    type Item = (StateRef<'a, K>, StateRef<'a, V>);

    fn next(&mut self) -> Option<Self::Item> {
        let mut entry = self.state_iter.as_mut()?.next()?;
        let key = entry.get_key();
        let mut key_cursor = Cursor {
            data:   key,
            offset: 8, // Items in a map always start with the set prefix which is 8 bytes.
        };
        // Unwrapping is safe when only using the high-level API.
        let k = K::deserial(&mut key_cursor).unwrap_abort();
        let v = V::deserial_with_state(&self.state_api, &mut entry).unwrap_abort();
        Some((StateRef::new(k), StateRef::new(v)))
    }
}

impl<'a, K, V: Serial, S: HasStateApi> Iterator for StateMapIterMut<'a, K, V, S>
where
    K: Deserial + 'a,
    V: DeserialWithState<S> + 'a,
    S::EntryType: 'a,
{
    type Item = (StateRef<'a, K>, StateRefMut<'a, V, S>);

    fn next(&mut self) -> Option<Self::Item> {
        let entry = self.state_iter.as_mut()?.next()?;

        let key_bytes = entry.get_key();
        let mut key_cursor = Cursor {
            data:   key_bytes,
            offset: 8, // Items in a map always start with the set prefix which is 8 bytes.
        };
        // Unwrapping is safe when only using the high-level API.
        let k = K::deserial(&mut key_cursor).unwrap_abort();
        // we do not load the value here, only on demand. This allows iteration over
        // keys to be reasonably efficient.
        Some((StateRef::new(k), StateRefMut::new(entry, self.state_api.clone())))
    }
}

impl<'a, S: HasStateApi, V: Serial + DeserialWithState<S>> crate::ops::Deref
    for StateRefMut<'a, V, S>
{
    type Target = V;

    #[inline(always)]
    fn deref(&self) -> &Self::Target { self.get() }
}

impl<'a, S: HasStateApi, V: Serial + DeserialWithState<S>> crate::ops::DerefMut
    for StateRefMut<'a, V, S>
{
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target { self.get_mut() }
}

/// When dropped, the value, `V`, is written to the entry in the contract state.
impl<'a, V: Serial, S: HasStateApi> Drop for StateRefMut<'a, V, S> {
    fn drop(&mut self) {
        if let Some(value) = self.lazy_value.get_mut() {
            let entry = self.entry.get_mut();
            entry.move_to_start();
            value.serial(entry).unwrap_abort()
        }
    }
}

impl<'a, V, S> StateRefMut<'a, V, S>
where
    V: Serial + DeserialWithState<S>,
    S: HasStateApi,
{
    /// Get a shared reference to the value. Note that [StateRefMut](Self) also
    /// implements [Deref](crate::ops::Deref) so this conversion can happen
    /// implicitly.
    pub fn get(&self) -> &V {
        let lv = unsafe { &mut *self.lazy_value.get() };
        if let Some(v) = lv {
            v
        } else {
            lv.insert(self.load_value())
        }
    }

    /// Get a unique reference to the value. Note that [StateRefMut](Self) also
    /// implements [DerefMut](crate::ops::DerefMut) so this conversion can
    /// happen implicitly.
    pub fn get_mut(&mut self) -> &mut V {
        let lv = unsafe { &mut *self.lazy_value.get() };
        if let Some(v) = lv {
            v
        } else {
            lv.insert(self.load_value())
        }
    }

    /// Load the value referenced by the entry from the chain data.
    fn load_value(&self) -> V {
        let entry = unsafe { &mut *self.entry.get() };
        entry.move_to_start();
        V::deserial_with_state(&self.state_api, entry).unwrap_abort()
    }

    /// Set the value. Overwrites the existing one.
    pub fn set(&mut self, new_val: V) {
        let entry = self.entry.get_mut();
        entry.move_to_start();
        new_val.serial(entry).unwrap_abort();
        let _ = self.lazy_value.get_mut().insert(new_val);
    }

    /// Update the existing value with the given function.
    pub fn update<F>(&mut self, f: F)
    where
        F: FnOnce(&mut V), {
        let lv = self.lazy_value.get_mut();
        let entry = self.entry.get_mut();
        let value = if let Some(v) = lv {
            v
        } else {
            entry.move_to_start();
            let value = V::deserial_with_state(&self.state_api, entry).unwrap_abort();
            lv.insert(value)
        };

        // Mutate the value (perhaps only in memory, depends on the type).
        f(value);
        entry.move_to_start();
        value.serial(entry).unwrap_abort()
    }
}

impl<K, V, S> Serial for StateMap<K, V, S> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> { out.write_all(&self.prefix) }
}

impl<T, S> StateSet<T, S>
where
    T: Serialize,
    S: HasStateApi,
{
    /// Adds a value to the set.
    /// If the set did not have this value, `true` is returned. Otherwise,
    /// `false`.
    pub fn insert(&mut self, value: T) -> bool {
        let key_bytes = self.key_with_set_prefix(&value);
        match self.state_api.entry(key_bytes) {
            EntryRaw::Vacant(vac) => {
                let _ = vac.insert_raw(&[]);
                true
            }
            EntryRaw::Occupied(_) => false,
        }
    }

    /// Returns `true` if the set contains no elements.
    pub fn is_empty(&self) -> bool { self.state_api.lookup_entry(&self.prefix).is_none() }

    /// Returns `true` if the set contains a value.
    pub fn contains(&self, value: &T) -> bool {
        let key_bytes = self.key_with_set_prefix(value);
        self.state_api.lookup_entry(&key_bytes).is_some()
    }

    /// Clears the set, removing all values.
    /// This also includes values pointed at, if `V`, for example, is a
    /// [StateBox].
    // Note: This does not use delete() because delete consumes self.
    pub fn clear(&mut self) {
        // Delete all values in the stateset. Since `T` is serializable
        // there is no need to recursively delete the values since
        // serializable values cannot have pointers to other parts of state.
        // Unwrapping is safe when only using the high-level API.
        self.state_api.delete_prefix(&self.prefix).unwrap_abort();
    }

    /// Removes a value from the set. Returns whether the value was present in
    /// the set.
    pub fn remove(&mut self, value: &T) -> bool {
        let key_bytes = self.key_with_set_prefix(value);

        // Unwrapping is safe, because iter() keeps a reference to the stateset.
        match self.state_api.entry(key_bytes) {
            EntryRaw::Vacant(_) => false,
            EntryRaw::Occupied(occ) => {
                // Unwrapping is safe, because iter() keeps a reference to the stateset.
                self.state_api.delete_entry(occ.get()).unwrap_abort();
                true
            }
        }
    }

    fn key_with_set_prefix(&self, key: &T) -> Vec<u8> {
        let mut key_with_prefix = self.prefix.to_vec();
        key.serial(&mut key_with_prefix).unwrap_abort();
        key_with_prefix
    }
}

impl<T, S: HasStateApi> StateSet<T, S> {
    pub(crate) fn open(state_api: S, prefix: [u8; 8]) -> Self {
        Self {
            _marker: PhantomData,
            prefix,
            state_api,
        }
    }

    /// Get an iterator over the elements in the `StateSet`. The iterator
    /// returns elements in increasing order, where elements are ordered
    /// lexicographically via their serializations.
    pub fn iter(&self) -> StateSetIter<T, S> {
        match self.state_api.iterator(&self.prefix) {
            Ok(state_iter) => StateSetIter {
                state_iter:       Some(state_iter),
                state_api:        self.state_api.clone(),
                _marker_lifetime: PhantomData,
            },
            Err(StateError::SubtreeWithPrefixNotFound) => StateSetIter {
                state_iter:       None,
                state_api:        self.state_api.clone(),
                _marker_lifetime: PhantomData,
            },
            _ => crate::trap(),
        }
    }
}

impl<T: Serial, S: HasStateApi> StateBox<T, S> {
    /// Create a new statebox.
    pub(crate) fn new(value: T, state_api: S, entry: S::EntryType) -> Self {
        StateBox {
            state_api,
            inner: UnsafeCell::new(StateBoxInner::Loaded {
                entry,
                modified: true,
                value,
            }),
        }
    }

    /// Return the key under which the value is stored in the contract state
    /// trie.
    pub(crate) fn get_location(&self) -> &[u8] {
        match unsafe { &*self.inner.get() } {
            StateBoxInner::Loaded {
                entry,
                ..
            } => entry.get_key(),
            StateBoxInner::Reference {
                prefix,
            } => &prefix[..],
        }
    }
}

impl<S: HasStateApi, T: Serial + DeserialWithState<S>> crate::ops::Deref for StateBox<T, S> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target { self.get() }
}

impl<S: HasStateApi, T: Serial + DeserialWithState<S>> crate::ops::DerefMut for StateBox<T, S> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target { self.get_mut() }
}

impl<T: Serial, S: HasStateApi> Drop for StateBox<T, S> {
    fn drop(&mut self) {
        if let StateBoxInner::Loaded {
            entry,
            modified,
            value,
        } = self.inner.get_mut()
        {
            if *modified {
                entry.move_to_start();
                value.serial(entry).unwrap_abort();
            }
        }
    }
}

/// Return a reference to the value stored inside the [`StateBoxInner`], as well
/// as a reference to the flag that indicates whether the value has been
/// modified or not.
fn get_with_inner<'a, T: Serial + DeserialWithState<S>, S: HasStateApi>(
    state_api: &S,
    inner: &'a mut StateBoxInner<T, S>,
) -> (&'a mut T, &'a mut bool) {
    let (entry, value) = match inner {
        StateBoxInner::Loaded {
            value,
            modified,
            ..
        } => return (value, modified),
        StateBoxInner::Reference {
            prefix,
        } => {
            let mut entry = state_api.lookup_entry(prefix).unwrap_abort();
            // new entry, positioned at the start.
            let value = T::deserial_with_state(state_api, &mut entry).unwrap_abort();
            (entry, value)
        }
    };
    *inner = StateBoxInner::Loaded {
        entry,
        modified: false,
        value,
    };
    match inner {
        StateBoxInner::Loaded {
            value,
            modified,
            ..
        } => (value, modified),
        StateBoxInner::Reference {
            ..
        } => {
            // We just set it to loaded.
            unsafe { crate::hint::unreachable_unchecked() }
        }
    }
}

impl<T, S> StateBox<T, S>
where
    T: Serial + DeserialWithState<S>,
    S: HasStateApi,
{
    /// Get a reference to the value.
    pub fn get(&self) -> &T {
        let inner = unsafe { &mut *self.inner.get() };
        get_with_inner(&self.state_api, inner).0
    }

    /// Get a mutable reference to the value. If the value is modified in-memory
    /// then it will be stored when the box is dropped.
    pub fn get_mut(&mut self) -> &mut T {
        let inner = self.inner.get_mut();
        let (value, modified) = get_with_inner(&self.state_api, inner);
        *modified = true;
        value
    }

    /// Replace the value with the provided one. The current value is returned.
    /// Note that if the type `T` contains references to state, e.g., is a
    /// [`StateBox`], then it must be [deleted](Deletable::delete) to avoid
    /// space leaks.
    #[must_use]
    pub fn replace(&mut self, new_val: T) -> T {
        let (entry, value) = self.ensure_cached();
        entry.move_to_start();
        new_val.serial(entry).unwrap_abort();
        mem::replace(value, new_val)
    }

    /// Update the existing value with the given function.
    /// The supplied function may return some data, which is then returned by
    /// [`update`](Self::update).
    pub fn update<F, A>(&mut self, f: F) -> A
    where
        F: FnOnce(&mut T) -> A, {
        let (entry, value) = self.ensure_cached();
        // Mutate the value (perhaps only in memory, depends on the type).
        let res = f(value);
        entry.move_to_start();
        value.serial(entry).unwrap_abort();
        res
    }

    /// If the value isn't cached, load the value from the state. Return a
    /// reference to the entry, and the value. Note that **if the value is
    /// modified, the entry should be used to write it.**
    fn ensure_cached(&mut self) -> (&mut S::EntryType, &mut T) {
        let inner = self.inner.get_mut();
        let (entry, modified, value) = match inner {
            StateBoxInner::Loaded {
                entry,
                value,
                ..
            } => return (entry, value),
            StateBoxInner::Reference {
                prefix,
            } => {
                let mut entry = self.state_api.lookup_entry(prefix).unwrap_abort();
                // new entry, positioned at the start.
                let value = T::deserial_with_state(&self.state_api, &mut entry).unwrap_abort();
                (entry, false, value)
            }
        };
        *inner = StateBoxInner::Loaded {
            entry,
            modified,
            value,
        };
        match inner {
            StateBoxInner::Loaded {
                entry,
                value,
                ..
            } => (entry, value),
            StateBoxInner::Reference {
                ..
            } => {
                // We just set it to loaded
                unsafe { crate::hint::unreachable_unchecked() }
            }
        }
    }
}

impl<T: Serial, S: HasStateApi> Serial for StateBox<T, S> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        out.write_all(self.get_location())
    }
}

impl<T, S> Serial for StateSet<T, S> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> { out.write_all(&self.prefix) }
}

/// Unlock the part of the tree locked by the iterator.
impl<'a, T, S: HasStateApi> Drop for StateSetIter<'a, T, S> {
    #[inline]
    fn drop(&mut self) {
        // Delete the iterator to unlock the subtree.
        if let Some(valid) = self.state_iter.take() {
            self.state_api.delete_iterator(valid);
        }
    }
}

impl<'a, T, S: HasStateApi> Iterator for StateSetIter<'a, T, S>
where
    T: DeserialWithState<S>,
{
    type Item = StateRef<'a, T>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let entry = self.state_iter.as_mut()?.next()?;
        let key = entry.get_key();
        let mut key_cursor = Cursor {
            data:   key,
            offset: 8, // Items in a set always start with the set prefix which is 8 bytes.
        };
        // Unwrapping is safe when only using the high-level API.
        let t = T::deserial_with_state(&self.state_api, &mut key_cursor).unwrap_abort();
        Some(StateRef::new(t))
    }
}

// # Trait implementations for Parameter

impl Default for ExternParameter {
    #[inline(always)]
    fn default() -> Self {
        ExternParameter {
            cursor: Cursor::new(ExternParameterDataPlaceholder {}),
        }
    }
}

impl Read for ExternParameter {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
        let len: u32 = {
            match buf.len().try_into() {
                Ok(v) => v,
                _ => return Err(ParseError::default()),
            }
        };
        let num_read = unsafe {
            // parameter 0 always exists, so this is safe.
            prims::get_parameter_section(0, buf.as_mut_ptr(), len, self.cursor.offset as u32)
        };

        self.cursor.offset += num_read as usize;
        Ok(num_read as usize)
    }
}

impl HasSize for ExternParameterDataPlaceholder {
    #[inline(always)]
    // parameter 0 always exists so this is correct
    fn size(&self) -> u32 { unsafe { prims::get_parameter_size(0) as u32 } }
}

impl HasSize for ExternParameter {
    #[inline(always)]
    fn size(&self) -> u32 { self.cursor.data.size() }
}

impl Seek for ExternParameter {
    type Err = ();

    #[inline(always)]
    fn seek(&mut self, pos: SeekFrom) -> Result<u32, Self::Err> { self.cursor.seek(pos) }

    #[inline(always)]
    fn cursor_position(&self) -> u32 { self.cursor.cursor_position() }
}

impl HasParameter for ExternParameter {}

/// The read implementation uses host functions to read chunks of return value
/// on demand.
impl Read for ExternCallResponse {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
        let len: u32 = {
            match buf.len().try_into() {
                Ok(v) => v,
                _ => return Err(ParseError::default()),
            }
        };
        let num_read = unsafe {
            prims::get_parameter_section(
                self.i.into(),
                buf.as_mut_ptr(),
                len,
                self.current_position,
            )
        };
        if num_read >= 0 {
            self.current_position += num_read as u32;
            Ok(num_read as usize)
        } else {
            Err(ParseError::default())
        }
    }
}

impl HasCallResponse for ExternCallResponse {
    // CallResponse can only be constured in this crate. As a result whenever it is
    // constructed it will point to a valid parameter, which means that
    // `get_parameter_size` will always return a non-negative value.
    fn size(&self) -> u32 { unsafe { prims::get_parameter_size(self.i.get()) as u32 } }
}

/// # Trait implementations for the chain metadata.
impl HasChainMetadata for ExternChainMeta {
    #[inline(always)]
    fn slot_time(&self) -> SlotTime {
        Timestamp::from_timestamp_millis(unsafe { prims::get_slot_time() })
    }
}

impl AttributesCursor {
    fn next_item(&mut self, buf: &mut [u8]) -> Option<(AttributeTag, u8)> {
        if self.remaining_items == 0 {
            return None;
        }

        let (tag_value_len, num_read) = unsafe {
            let mut tag_value_len = MaybeUninit::<[u8; 2]>::uninit();
            // Should succeed, otherwise host violated precondition.
            let num_read = prims::get_policy_section(
                tag_value_len.as_mut_ptr() as *mut u8,
                2,
                self.current_position,
            );
            (tag_value_len.assume_init(), num_read)
        };
        self.current_position += num_read;
        if tag_value_len[1] > 31 {
            // Should not happen because all attributes fit into 31 bytes.
            return None;
        }
        let num_read = unsafe {
            prims::get_policy_section(
                buf.as_mut_ptr(),
                u32::from(tag_value_len[1]),
                self.current_position,
            )
        };
        self.current_position += num_read;
        self.remaining_items -= 1;
        Some((AttributeTag(tag_value_len[0]), tag_value_len[1]))
    }
}

impl HasPolicy for Policy<AttributesCursor> {
    type Iterator = PolicyAttributesIter;

    fn identity_provider(&self) -> IdentityProvider { self.identity_provider }

    fn created_at(&self) -> Timestamp { self.created_at }

    fn valid_to(&self) -> Timestamp { self.valid_to }

    #[inline(always)]
    fn next_item(&mut self, buf: &mut [u8; 31]) -> Option<(AttributeTag, u8)> {
        self.items.next_item(buf)
    }

    fn attributes(&self) -> Self::Iterator {
        PolicyAttributesIter {
            cursor: AttributesCursor {
                current_position: 0,
                remaining_items:  self.items.total_items,
                total_items:      self.items.total_items,
            },
        }
    }
}

impl Iterator for PolicyAttributesIter {
    type Item = (AttributeTag, AttributeValue);

    fn next(&mut self) -> Option<Self::Item> {
        let mut inner = [0u8; 32];
        let (tag, len) = self.cursor.next_item(&mut inner[1..])?;
        inner[0] = len;
        Some((tag, unsafe { AttributeValue::new_unchecked(inner) }))
    }
}

impl ExactSizeIterator for PolicyAttributesIter {
    fn len(&self) -> usize { self.cursor.remaining_items as usize }
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
            prims::get_policy_section(buf.as_mut_ptr() as *mut u8, 2 + 4 + 8 + 8 + 2, self.pos);
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
                total_items: remaining_items,
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
    type MetadataType = ExternChainMeta;
    type ParamType = ExternParameter;
    type PolicyIteratorType = PoliciesIterator;
    type PolicyType = Policy<AttributesCursor>;

    #[inline(always)]
    fn metadata(&self) -> &Self::MetadataType { &ExternChainMeta {} }

    fn policies(&self) -> PoliciesIterator {
        let mut buf: MaybeUninit<[u8; 2]> = MaybeUninit::uninit();
        let buf = unsafe {
            prims::get_policy_section(buf.as_mut_ptr() as *mut u8, 2, 0);
            buf.assume_init()
        };
        PoliciesIterator {
            pos:             2, // 2 because we already read 2 bytes.
            remaining_items: u16::from_le_bytes(buf),
        }
    }

    #[inline(always)]
    fn parameter_cursor(&self) -> Self::ParamType { ExternParameter::default() }
}

/// Tag of the transfer operation expected by the host. See [prims::invoke].
const INVOKE_TRANSFER_TAG: u32 = 0;
/// Tag of the call operation expected by the host. See [prims::invoke].
const INVOKE_CALL_TAG: u32 = 1;
/// Tag of the query account balance operation expected by the host. See
/// [prims::invoke].
const INVOKE_QUERY_ACCOUNT_BALANCE_TAG: u32 = 2;
/// Tag of the query contract balance operation expected by the host. See
/// [prims::invoke].
const INVOKE_QUERY_CONTRACT_BALANCE_TAG: u32 = 3;
/// Tag of the query exchange rates operation expected by the host. See
/// [prims::invoke].
const INVOKE_QUERY_EXCHANGE_RATES_TAG: u32 = 4;

/// Check whether the response code from calling `invoke` is encoding a failure
/// and map out the byte used for the error code.
/// A successful response code have the last 5 bytes unset.
#[inline(always)]
fn get_invoke_failure_code(code: u64) -> Option<u8> {
    if code & 0xff_ffff_ffff == 0 {
        None
    } else {
        let error_code = (code & 0xff_0000_0000) >> 32;
        Some(error_code as u8)
    }
}

/// Decode the the response code.
///
/// The response is encoded as follows.
/// - Success if the last 5 bytes are all zero:
///   - the first 3 bytes encodes the return value index, except the first bit,
///     which is used to indicate whether the contract state was modified.
/// - In case of failure the 4th byte is used, and encodes the enviroment
///   failure, where:
///   - 0x01 encodes amount too large.
///   - 0x02 encodes missing account.
fn parse_transfer_response_code(code: u64) -> TransferResult {
    if let Some(error_code) = get_invoke_failure_code(code) {
        match error_code {
            0x01 => Err(TransferError::AmountTooLarge),
            0x02 => Err(TransferError::MissingAccount),
            _ => crate::trap(), // host precondition violation
        }
    } else {
        Ok(())
    }
}

/// Decode the response code from calling upgrade.
///
/// The response is encoded as follows.
/// - Success if the last 5 bytes are all zero:
///   - the first 3 bytes encodes the return value index, except the first bit,
///     which is used to indicate whether the contract state was modified.
/// - In case of failure the 4th byte is used, and encodes the enviroment
///   failure, where:
///   - 0x07 encodes missing module.
///   - 0x08 encodes missing contract.
///   - 0x09 encodes module being an unsupported version.
#[inline(always)]
fn parse_upgrade_response_code(code: u64) -> UpgradeResult {
    if let Some(error_code) = get_invoke_failure_code(code) {
        match error_code {
            0x07 => Err(UpgradeError::MissingModule),
            0x08 => Err(UpgradeError::MissingContract),
            0x09 => Err(UpgradeError::UnsupportedModuleVersion),
            _ => crate::trap(), // host precondition violation
        }
    } else {
        Ok(())
    }
}

/// Decode the the response code.
///
/// The response is encoded as follows.
/// - Success if the last 5 bytes are all zero:
///   - the first 3 bytes encodes the return value index, except the first bit,
///     which is used to indicate whether the contract state was modified.
/// - In case of failure:
///   - if the 4th byte is 0 then the remaining 4 bytes encode the rejection
///     reason from the contract
///   - otherwise only the 4th byte is used, and encodes the enviroment failure.
///     - 0x01 encodes amount too large.
///     - 0x02 encodes missing account.
///     - 0x03 encodes missing contract.
///     - 0x04 encodes missing entrypoint.
///     - 0x05 encodes message failed.
///     - 0x06 encodes trap.
fn parse_call_response_code(code: u64) -> CallContractResult<ExternCallResponse> {
    if let Some(error_code) = get_invoke_failure_code(code) {
        match error_code {
            0x00 =>
            // response with logic error and return value.
            {
                let reason = (0x0000_0000_ffff_ffff & code) as u32 as i32;
                if reason == 0 {
                    crate::trap()
                } else {
                    let rv = (code >> 40) as u32;
                    if rv > 0 {
                        Err(CallContractError::LogicReject {
                            reason,
                            return_value: ExternCallResponse::new(unsafe {
                                NonZeroU32::new_unchecked(rv)
                            }),
                        })
                    } else {
                        unsafe { crate::hint::unreachable_unchecked() } // host precondition violation.
                    }
                }
            }
            0x01 => Err(CallContractError::AmountTooLarge),
            0x02 => Err(CallContractError::MissingAccount),
            0x03 => Err(CallContractError::MissingContract),
            0x04 => Err(CallContractError::MissingEntrypoint),
            0x05 => Err(CallContractError::MessageFailed),
            0x06 => Err(CallContractError::Trap),
            _ => unsafe { crate::hint::unreachable_unchecked() }, // host precondition violation
        }
    } else {
        // Map out the 3 bytes encoding the return value index.
        let rv = (code >> 40) as u32;

        let tag = 0x80_0000u32; // Mask for the first bit.
        if tag & rv != 0 {
            // Check the bit, indicating a contract state change.
            Ok((true, NonZeroU32::new(rv & !tag).map(ExternCallResponse::new)))
        } else {
            Ok((false, NonZeroU32::new(rv).map(ExternCallResponse::new)))
        }
    }
}

/// Decode the account balance response code.
///
/// - Success if the last 5 bytes are all zero:
///   - the first 3 bytes encodes the return value index.
/// - In case of failure the 4th byte is used, and encodes the enviroment
///   failure where:
///    - '0x02' encodes missing account.
fn parse_query_account_balance_response_code(
    code: u64,
) -> Result<ExternCallResponse, QueryAccountBalanceError> {
    if let Some(error_code) = get_invoke_failure_code(code) {
        if error_code == 0x02 {
            Err(QueryAccountBalanceError)
        } else {
            unsafe { crate::hint::unreachable_unchecked() }
        }
    } else {
        // Map out the 3 bytes encoding the return value index.
        let return_value_index = NonZeroU32::new((code >> 40) as u32).unwrap_abort();
        Ok(ExternCallResponse::new(return_value_index))
    }
}

/// Decode the contract balance response code.
///
/// - Success if the last 5 bytes are all zero:
///   - the first 3 bytes encodes the return value index.
/// - In case of failure the 4th byte is used, and encodes the enviroment
///   failure where:
///    - '0x03' encodes missing contract.
fn parse_query_contract_balance_response_code(
    code: u64,
) -> Result<ExternCallResponse, QueryContractBalanceError> {
    if let Some(error_code) = get_invoke_failure_code(code) {
        if error_code == 0x03 {
            Err(QueryContractBalanceError)
        } else {
            unsafe { crate::hint::unreachable_unchecked() }
        }
    } else {
        // Map out the 3 bytes encoding the return value index.
        let return_value_index = NonZeroU32::new((code >> 40) as u32).unwrap_abort();
        Ok(ExternCallResponse::new(return_value_index))
    }
}

/// Decode the exchange rate response code.
///
/// - Success if the last 5 bytes are all zero:
///   - the first 3 bytes encodes the return value index.
/// - In case of failure we throw a runtime error, since this query is not
///   expected to fail.
fn parse_query_exchange_rates_response_code(code: u64) -> ExternCallResponse {
    if get_invoke_failure_code(code).is_some() {
        // Querying the exchange rates should never produce a failure response code.
        unsafe { crate::hint::unreachable_unchecked() }
    } else {
        // Map out the 3 bytes encoding the return value index.
        let return_value_index = NonZeroU32::new((code >> 40) as u32).unwrap_abort();
        ExternCallResponse::new(return_value_index)
    }
}

/// Helper factoring out the common behaviour of invoke_transfer for the two
/// extern hosts below.
fn invoke_transfer_worker(receiver: &AccountAddress, amount: Amount) -> TransferResult {
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
        prims::invoke(INVOKE_TRANSFER_TAG, data.as_ptr(), (ACCOUNT_ADDRESS_SIZE + 8) as u32)
    };
    parse_transfer_response_code(response)
}

/// A helper that constructs the parameter to invoke_contract.
fn invoke_contract_construct_parameter(
    to: &ContractAddress,
    parameter: Parameter,
    method: EntrypointName,
    amount: Amount,
) -> Vec<u8> {
    let mut data = Vec::with_capacity(16 + parameter.0.len() + 2 + method.size() as usize + 2 + 8);
    let mut cursor = Cursor::new(&mut data);
    to.serial(&mut cursor).unwrap_abort();
    parameter.serial(&mut cursor).unwrap_abort();
    method.serial(&mut cursor).unwrap_abort();
    amount.serial(&mut cursor).unwrap_abort();
    data
}

/// Helper factoring out the common behaviour of account_balance for the
/// two extern hosts below.
fn query_account_balance_worker(address: &AccountAddress) -> QueryAccountBalanceResult {
    let response = unsafe {
        prims::invoke(
            INVOKE_QUERY_ACCOUNT_BALANCE_TAG,
            AsRef::<[u8]>::as_ref(&address).as_ptr(),
            32,
        )
    };
    let mut return_value = parse_query_account_balance_response_code(response)?;
    Ok(AccountBalance::deserial(&mut return_value).unwrap_abort())
}

/// Helper factoring out the common behaviour of contract_balance for the
/// two extern hosts below.
fn query_contract_balance_worker(address: &ContractAddress) -> QueryContractBalanceResult {
    let mut data = [0u8; 16];
    data[..8].copy_from_slice(&address.index.to_le_bytes());
    data[8..].copy_from_slice(&address.subindex.to_le_bytes());
    let response = unsafe { prims::invoke(INVOKE_QUERY_CONTRACT_BALANCE_TAG, data.as_ptr(), 16) };
    let mut return_value = parse_query_contract_balance_response_code(response)?;
    Ok(Amount::deserial(&mut return_value).unwrap_abort())
}

/// Helper factoring out the common behaviour of exchange_rates for the
/// two extern hosts below.
fn query_exchange_rates_worker() -> ExchangeRates {
    let response_code = unsafe { prims::invoke(INVOKE_QUERY_EXCHANGE_RATES_TAG, [].as_ptr(), 0) };

    let mut response = parse_query_exchange_rates_response_code(response_code);
    ExchangeRates::deserial(&mut response).unwrap_abort()
}

impl<S> StateBuilder<S>
where
    S: HasStateApi,
{
    /// Open a new state_builder. Only a single instance of the state_builder
    /// should exist during contract execution, thus this should only be
    /// called at the very beginning of execution.
    pub fn open(state: S) -> Self {
        Self {
            state_api: state,
        }
    }

    /// Create a new empty [`StateMap`].
    pub fn new_map<K, V>(&mut self) -> StateMap<K, V, S> {
        let prefix = self.get_and_update_item_prefix();
        StateMap::open(self.state_api.clone(), prefix)
    }

    /// Create a new empty [`StateSet`].
    pub fn new_set<T>(&mut self) -> StateSet<T, S> {
        let prefix = self.get_and_update_item_prefix();
        StateSet::open(self.state_api.clone(), prefix)
    }

    /// Create a new [`StateBox`] and insert the `value` into the state.
    /// This stores the serialized value in the contract state. Thus **if the
    /// `StateBox` is dropped without calling [`delete`](StateBox::delete)
    /// then the value will remain in contract state, leading to a space leak.**
    ///
    /// Note that this dropping can happen implicitly via assignment. For
    /// example,
    ///
    /// ```no_run
    /// # use concordium_std::*;
    /// struct MyState<S: HasStateApi> {
    ///     inner: StateBox<u64, S>,
    /// }
    /// fn incorrect_replace<S: HasStateApi>(
    ///     state_builder: &mut StateBuilder<S>,
    ///     state: &mut MyState<S>,
    /// ) {
    ///     // The following is incorrect. The old value of `inner` is not properly deleted.
    ///     // from the state.
    ///     state.inner = state_builder.new_box(0); // ⚠️
    /// }
    /// ```
    /// Instead, the old value should be manually deleted.
    /// ```no_run
    /// # use concordium_std::*;
    /// # struct MyState<S: HasStateApi> {
    /// #    inner: StateBox<u64, S>
    /// # }
    /// fn correct_replace<S: HasStateApi>(
    ///     state_builder: &mut StateBuilder<S>,
    ///     state: &mut MyState<S>,
    /// ) {
    ///     let old_box = mem::replace(&mut state.inner, state_builder.new_box(0));
    ///     old_box.delete()
    /// }
    /// ```
    #[must_use]
    pub fn new_box<T: Serial>(&mut self, value: T) -> StateBox<T, S> {
        let prefix = self.get_and_update_item_prefix();

        // Insert the value into the state
        let mut state_entry = self.state_api.create_entry(&prefix).unwrap_abort();
        value.serial(&mut state_entry).unwrap_abort();
        StateBox::new(value, self.state_api.clone(), state_entry)
    }

    fn get_and_update_item_prefix(&mut self) -> [u8; 8] {
        // Get the next prefix or insert and use the initial one.
        // Unwrapping is safe when using the high-level API because it is not possible
        // to get an iterator that locks this entry.
        let mut next_collection_prefix_entry = self
            .state_api
            .entry(NEXT_ITEM_PREFIX_KEY)
            .or_insert_raw(&INITIAL_NEXT_ITEM_PREFIX)
            .unwrap_abort();

        // Get the next collection prefix
        let collection_prefix = next_collection_prefix_entry.read_u64().unwrap_abort(); // Unwrapping is safe if only using the high-level API.

        // Rewind state entry position.
        next_collection_prefix_entry.move_to_start();

        // Increment the collection prefix
        next_collection_prefix_entry.write_u64(collection_prefix + 1).unwrap_abort(); // Writing to state cannot fail.

        collection_prefix.to_le_bytes()
    }
}

#[cfg(test)]
/// Some helper methods that are used for internal tests.
impl<S> StateBuilder<S>
where
    S: HasStateApi,
{
    /// Get a value from the generic map.
    /// `Some(Err(_))` means that something exists in the state with that key,
    /// but it isn't of type `V`.
    pub(crate) fn get<K: Serial, V: DeserialWithState<S>>(&self, key: K) -> Option<ParseResult<V>> {
        let key_with_map_prefix = Self::prepend_generic_map_key(key);

        self.state_api
            .lookup_entry(&key_with_map_prefix)
            .map(|mut entry| V::deserial_with_state(&self.state_api, &mut entry))
    }

    /// Inserts a value in the generic map.
    /// The key and value are serialized before insert.
    pub(crate) fn insert<K: Serial, V: Serial>(
        &mut self,
        key: K,
        value: V,
    ) -> Result<(), StateError> {
        let key_with_map_prefix = Self::prepend_generic_map_key(key);
        match self.state_api.entry(key_with_map_prefix) {
            EntryRaw::Vacant(vac) => {
                let _ = vac.insert(&value);
            }
            EntryRaw::Occupied(mut occ) => occ.insert(&value),
        }
        Ok(())
    }

    /// Serializes the key and prepends [GENERIC_MAP_PREFIX].
    /// This is similar to how [StateMap] works, where a unique prefix is
    /// prepended onto keys. Since there is only one generic map, the prefix
    /// is a constant.
    fn prepend_generic_map_key<K: Serial>(key: K) -> Vec<u8> {
        let mut key_with_map_prefix = to_bytes(&GENERIC_MAP_PREFIX);
        key_with_map_prefix.append(&mut to_bytes(&key));
        key_with_map_prefix
    }
}

impl<S> HasHost<S> for ExternHost<S>
where
    S: Serial + DeserialWithState<ExternStateApi>,
{
    type ReturnValueType = ExternCallResponse;
    type StateApiType = ExternStateApi;

    fn invoke_transfer(&self, receiver: &AccountAddress, amount: Amount) -> TransferResult {
        invoke_transfer_worker(receiver, amount)
    }

    fn invoke_contract_raw(
        &mut self,
        to: &ContractAddress,
        parameter: Parameter,
        method: EntrypointName,
        amount: Amount,
    ) -> CallContractResult<Self::ReturnValueType> {
        let data = invoke_contract_construct_parameter(to, parameter, method, amount);
        let len = data.len();
        // save the state before the out-call to reflect any changes we might have done.
        // this is not optimal, and ideally we'd keep track of changes. But that is more
        // error prone for the programmer.
        self.commit_state();
        let response = unsafe { prims::invoke(INVOKE_CALL_TAG, data.as_ptr(), len as u32) };
        let (state_modified, res) = parse_call_response_code(response)?;
        if state_modified {
            // The state of the contract changed as a result of the call.
            // So we refresh it.
            if let Ok(new_state) = S::deserial_with_state(
                &self.state_builder.state_api,
                &mut self.state_builder.state_api.lookup_entry(&[]).unwrap_abort(),
            ) {
                self.state = new_state;
            } else {
                crate::trap()
            }
        }
        Ok((state_modified, res))
    }

    fn invoke_contract_raw_read_only(
        &self,
        to: &ContractAddress,
        parameter: Parameter,
        method: EntrypointName,
        amount: Amount,
    ) -> ReadOnlyCallContractResult<Self::ReturnValueType> {
        let data = invoke_contract_construct_parameter(to, parameter, method, amount);
        let len = data.len();
        let response = unsafe { prims::invoke(INVOKE_CALL_TAG, data.as_ptr(), len as u32) };
        let (state_modified, res) = parse_call_response_code(response)?;
        if state_modified {
            crate::trap()
        } else {
            Ok(res)
        }
    }

    #[inline(always)]
    fn account_balance(&self, address: AccountAddress) -> QueryAccountBalanceResult {
        query_account_balance_worker(&address)
    }

    #[inline(always)]
    fn contract_balance(&self, address: ContractAddress) -> QueryContractBalanceResult {
        query_contract_balance_worker(&address)
    }

    #[inline(always)]
    fn exchange_rates(&self) -> ExchangeRates { query_exchange_rates_worker() }

    fn upgrade(&mut self, module: ModuleReference) -> UpgradeResult {
        let response = unsafe { prims::upgrade(module.as_ref().as_ptr()) };
        parse_upgrade_response_code(response)
    }

    fn state(&self) -> &S { &self.state }

    fn state_mut(&mut self) -> &mut S { &mut self.state }

    fn commit_state(&mut self) {
        let mut root_entry = self.state_builder.state_api.lookup_entry(&[]).unwrap_abort();
        self.state.serial(&mut root_entry).unwrap_abort();
        let new_state_size = root_entry.size().unwrap_abort();
        root_entry.truncate(new_state_size).unwrap_abort();
    }

    #[inline(always)]
    fn self_balance(&self) -> Amount {
        Amount::from_micro_ccd(unsafe { prims::get_receive_self_balance() })
    }

    #[inline(always)]
    fn state_builder(&mut self) -> &mut StateBuilder<Self::StateApiType> { &mut self.state_builder }

    #[inline(always)]
    fn state_and_builder(&mut self) -> (&mut S, &mut StateBuilder<Self::StateApiType>) {
        (&mut self.state, &mut self.state_builder)
    }
}

impl HasHost<ExternStateApi> for ExternLowLevelHost {
    type ReturnValueType = ExternCallResponse;
    type StateApiType = ExternStateApi;

    #[inline(always)]
    fn invoke_transfer(&self, receiver: &AccountAddress, amount: Amount) -> TransferResult {
        invoke_transfer_worker(receiver, amount)
    }

    fn invoke_contract_raw(
        &mut self,
        to: &ContractAddress,
        parameter: Parameter,
        method: EntrypointName,
        amount: Amount,
    ) -> CallContractResult<Self::ReturnValueType> {
        let data = invoke_contract_construct_parameter(to, parameter, method, amount);
        let len = data.len();
        let response = unsafe { prims::invoke(INVOKE_CALL_TAG, data.as_ptr(), len as u32) };
        parse_call_response_code(response)
    }

    #[inline(always)]
    fn account_balance(&self, address: AccountAddress) -> QueryAccountBalanceResult {
        query_account_balance_worker(&address)
    }

    #[inline(always)]
    fn contract_balance(&self, address: ContractAddress) -> QueryContractBalanceResult {
        query_contract_balance_worker(&address)
    }

    #[inline(always)]
    fn exchange_rates(&self) -> ExchangeRates { query_exchange_rates_worker() }

    fn upgrade(&mut self, module: ModuleReference) -> UpgradeResult {
        let response = unsafe { prims::upgrade(module.as_ref().as_ptr()) };
        parse_upgrade_response_code(response)
    }

    #[inline(always)]
    fn state(&self) -> &ExternStateApi { &self.state_api }

    #[inline(always)]
    fn state_mut(&mut self) -> &mut ExternStateApi { &mut self.state_api }

    #[inline(always)]
    fn commit_state(&mut self) {
        // do nothing since the low level host does not maintain any state
    }

    #[inline(always)]
    fn self_balance(&self) -> Amount {
        Amount::from_micro_ccd(unsafe { prims::get_receive_self_balance() })
    }

    #[inline(always)]
    fn state_builder(&mut self) -> &mut StateBuilder<Self::StateApiType> { &mut self.state_builder }

    #[inline(always)]
    fn state_and_builder(
        &mut self,
    ) -> (&mut ExternStateApi, &mut StateBuilder<Self::StateApiType>) {
        (&mut self.state_api, &mut self.state_builder)
    }

    fn invoke_contract_raw_read_only(
        &self,
        to: &ContractAddress,
        parameter: Parameter<'_>,
        method: EntrypointName<'_>,
        amount: Amount,
    ) -> ReadOnlyCallContractResult<Self::ReturnValueType> {
        let data = invoke_contract_construct_parameter(to, parameter, method, amount);
        let len = data.len();
        let response = unsafe { prims::invoke(INVOKE_CALL_TAG, data.as_ptr(), len as u32) };
        let (state_modified, res) = parse_call_response_code(response)?;
        if state_modified {
            crate::trap()
        } else {
            Ok(res)
        }
    }
}

impl HasCryptoPrimitives for ExternCryptoPrimitives {
    fn verify_ed25519_signature(
        &self,
        public_key: PublicKeyEd25519,
        signature: SignatureEd25519,
        message: &[u8],
    ) -> bool {
        let res = unsafe {
            prims::verify_ed25519_signature(
                public_key.0.as_ptr(),
                signature.0.as_ptr(),
                message.as_ptr(),
                message.len() as u32,
            )
        };
        res == 1
    }

    fn verify_ecdsa_secp256k1_signature(
        &self,
        public_key: PublicKeyEcdsaSecp256k1,
        signature: SignatureEcdsaSecp256k1,
        message_hash: [u8; 32],
    ) -> bool {
        let res = unsafe {
            prims::verify_ecdsa_secp256k1_signature(
                public_key.0.as_ptr(),
                signature.0.as_ptr(),
                message_hash.as_ptr(),
            )
        };
        res == 1
    }

    fn hash_sha2_256(&self, data: &[u8]) -> HashSha2256 {
        let mut output: MaybeUninit<[u8; 32]> = MaybeUninit::uninit();
        unsafe {
            prims::hash_sha2_256(data.as_ptr(), data.len() as u32, output.as_mut_ptr() as *mut u8);
            HashSha2256(output.assume_init())
        }
    }

    fn hash_sha3_256(&self, data: &[u8]) -> HashSha3256 {
        let mut output: MaybeUninit<[u8; 32]> = MaybeUninit::uninit();
        unsafe {
            prims::hash_sha3_256(data.as_ptr(), data.len() as u32, output.as_mut_ptr() as *mut u8);
            HashSha3256(output.assume_init())
        }
    }

    fn hash_keccak_256(&self, data: &[u8]) -> HashKeccak256 {
        let mut output: MaybeUninit<[u8; 32]> = MaybeUninit::uninit();
        unsafe {
            prims::hash_keccak_256(
                data.as_ptr(),
                data.len() as u32,
                output.as_mut_ptr() as *mut u8,
            );
            HashKeccak256(output.assume_init())
        }
    }
}

/// # Trait implementations for the init context
impl HasInitContext for ExternContext<crate::types::ExternInitContext> {
    type InitData = ();

    /// Create a new init context by using an external call.
    fn open(_: Self::InitData) -> Self { ExternContext::default() }

    #[inline(always)]
    fn init_origin(&self) -> AccountAddress {
        let mut bytes: MaybeUninit<[u8; ACCOUNT_ADDRESS_SIZE]> = MaybeUninit::uninit();
        let ptr = bytes.as_mut_ptr();
        let address = unsafe {
            prims::get_init_origin(ptr as *mut u8);
            bytes.assume_init()
        };
        AccountAddress(address)
    }
}

/// # Trait implementations for the receive context
impl HasReceiveContext for ExternContext<crate::types::ExternReceiveContext> {
    type ReceiveData = ();

    /// Create a new receive context
    fn open(_: Self::ReceiveData) -> Self { ExternContext::default() }

    #[inline(always)]
    fn invoker(&self) -> AccountAddress {
        let mut bytes: MaybeUninit<[u8; ACCOUNT_ADDRESS_SIZE]> = MaybeUninit::uninit();
        let ptr = bytes.as_mut_ptr();
        let address = unsafe {
            prims::get_receive_invoker(ptr as *mut u8);
            bytes.assume_init()
        };
        AccountAddress(address)
    }

    #[inline(always)]
    fn self_address(&self) -> ContractAddress {
        let mut bytes: MaybeUninit<[u8; 16]> = MaybeUninit::uninit();
        let ptr = bytes.as_mut_ptr();
        let address = unsafe {
            prims::get_receive_self_address(ptr as *mut u8);
            bytes.assume_init()
        };
        match from_bytes(&address) {
            Ok(v) => v,
            Err(_) => crate::trap(),
        }
    }

    #[inline(always)]
    fn sender(&self) -> Address {
        let mut bytes: MaybeUninit<[u8; 33]> = MaybeUninit::uninit();
        let ptr = bytes.as_mut_ptr() as *mut u8;
        unsafe {
            prims::get_receive_sender(ptr);
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
            prims::get_receive_owner(ptr as *mut u8);
            bytes.assume_init()
        };
        AccountAddress(address)
    }

    fn named_entrypoint(&self) -> OwnedEntrypointName {
        let mut data = crate::vec![0u8; unsafe { prims::get_receive_entrypoint_size() as usize }];
        unsafe { prims::get_receive_entrypoint(data.as_mut_ptr()) };
        OwnedEntrypointName::new_unchecked(unsafe { String::from_utf8_unchecked(data) })
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
        let res = unsafe { prims::log_event(event.as_ptr(), event.len() as u32) };
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

/// Blanket implementation of [DeserialWithState] for any [Deserial] types,
/// which simply does not use the state argument.
impl<D: Deserial, S: HasStateApi> DeserialWithState<S> for D {
    #[inline(always)]
    fn deserial_with_state<R: Read>(_state: &S, source: &mut R) -> ParseResult<Self> {
        Self::deserial(source)
    }
}

/// Blanket implementation of [DeserialCtxWithState] for any [DeserialCtx]
/// types, which simply does not use the state argument.
impl<D: DeserialCtx, S: HasStateApi> DeserialCtxWithState<S> for D {
    #[inline(always)]
    fn deserial_ctx_with_state<R: Read>(
        size_length: schema::SizeLength,
        ensure_ordered: bool,
        _state: &S,
        source: &mut R,
    ) -> ParseResult<Self> {
        Self::deserial_ctx(size_length, ensure_ordered, source)
    }
}

impl<K, V, S> DeserialWithState<S> for StateMap<K, V, S>
where
    S: HasStateApi,
{
    fn deserial_with_state<R: Read>(state: &S, source: &mut R) -> ParseResult<Self> {
        source.read_array().map(|map_prefix| StateMap::open(state.clone(), map_prefix))
    }
}

impl<T, S> DeserialWithState<S> for StateSet<T, S>
where
    S: HasStateApi,
    T: Serial + DeserialWithState<S>,
{
    fn deserial_with_state<R: Read>(state: &S, source: &mut R) -> ParseResult<Self> {
        source.read_array().map(|set_prefix| StateSet::open(state.clone(), set_prefix))
    }
}

impl<T, S> DeserialWithState<S> for StateBox<T, S>
where
    S: HasStateApi,
    T: Serial + DeserialWithState<S>,
{
    fn deserial_with_state<R: Read>(state: &S, source: &mut R) -> ParseResult<Self> {
        let prefix = source.read_array()?;
        Ok(StateBox {
            state_api: state.clone(),
            inner:     UnsafeCell::new(StateBoxInner::Reference {
                prefix,
            }),
        })
    }
}

impl<T: Serialize> Deletable for T {
    #[inline(always)]
    fn delete(self) {} // Types that are Serialize have nothing to delete!
}

impl<T, S> Deletable for StateBox<T, S>
where
    T: Serial + DeserialWithState<S> + Deletable,
    S: HasStateApi,
{
    fn delete(mut self) {
        // replace the value with a dummy one for which drop is a no-op.
        let inner = mem::replace(
            &mut self.inner,
            UnsafeCell::new(StateBoxInner::Reference {
                prefix: [0u8; 8],
            }),
        );
        let (entry, value) = match inner.into_inner() {
            StateBoxInner::Loaded {
                entry,
                value,
                ..
            } => (entry, value),
            StateBoxInner::Reference {
                prefix,
            } => {
                // we load the value first because it might be necessary to delete
                // the nested value.
                // TODO: This is pretty bad for performance, but we cannot specialize the
                // implementation for flat values. Once rust supports specialization we might be
                // able to have a more precise implementation for flat values,
                // i.e., ones which are Deserial.
                let mut entry = self.state_api.lookup_entry(&prefix).unwrap_abort();
                let value = T::deserial_with_state(&self.state_api, &mut entry).unwrap_abort();
                (entry, value)
            }
        };
        self.state_api.delete_entry(entry).unwrap_abort();
        value.delete()
    }
}

impl<T, S> Deletable for StateSet<T, S>
where
    S: HasStateApi,
{
    fn delete(mut self) {
        // Statesets cannot contain state types (e.g. StateBox), so there is nothing to
        // delete, apart from the set itself.

        // Unwrapping is safe when only using the high-level API.
        self.state_api.delete_prefix(&self.prefix).unwrap_abort();
    }
}

impl<K, V, S> Deletable for StateMap<K, V, S>
where
    S: HasStateApi,
    K: Serialize,
    V: Serial + DeserialWithState<S> + Deletable,
{
    fn delete(mut self) { self.clear(); }
}

impl Serial for PublicKeyEd25519 {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> { self.0.serial(out) }
}

impl Deserial for PublicKeyEd25519 {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        Ok(PublicKeyEd25519(Deserial::deserial(source)?))
    }
}

impl schema::SchemaType for PublicKeyEd25519 {
    fn get_type() -> concordium_contracts_common::schema::Type { schema::Type::ByteArray(32) }
}

impl Serial for PublicKeyEcdsaSecp256k1 {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> { self.0.serial(out) }
}

impl Deserial for PublicKeyEcdsaSecp256k1 {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        Ok(PublicKeyEcdsaSecp256k1(Deserial::deserial(source)?))
    }
}

impl schema::SchemaType for PublicKeyEcdsaSecp256k1 {
    fn get_type() -> concordium_contracts_common::schema::Type { schema::Type::ByteArray(33) }
}

impl Serial for SignatureEd25519 {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> { self.0.serial(out) }
}

impl Deserial for SignatureEd25519 {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        Ok(SignatureEd25519(Deserial::deserial(source)?))
    }
}

impl schema::SchemaType for SignatureEd25519 {
    fn get_type() -> concordium_contracts_common::schema::Type { schema::Type::ByteArray(64) }
}

impl Serial for SignatureEcdsaSecp256k1 {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> { self.0.serial(out) }
}

impl Deserial for SignatureEcdsaSecp256k1 {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        Ok(SignatureEcdsaSecp256k1(Deserial::deserial(source)?))
    }
}

impl schema::SchemaType for SignatureEcdsaSecp256k1 {
    fn get_type() -> concordium_contracts_common::schema::Type { schema::Type::ByteArray(64) }
}

impl Serial for HashSha2256 {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> { self.0.serial(out) }
}

impl Deserial for HashSha2256 {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        Ok(HashSha2256(Deserial::deserial(source)?))
    }
}

impl schema::SchemaType for HashSha2256 {
    fn get_type() -> concordium_contracts_common::schema::Type { schema::Type::ByteArray(32) }
}

impl Serial for HashSha3256 {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> { self.0.serial(out) }
}

impl Deserial for HashSha3256 {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        Ok(HashSha3256(Deserial::deserial(source)?))
    }
}

impl schema::SchemaType for HashSha3256 {
    fn get_type() -> concordium_contracts_common::schema::Type { schema::Type::ByteArray(32) }
}

impl Serial for HashKeccak256 {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> { self.0.serial(out) }
}

impl Deserial for HashKeccak256 {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        Ok(HashKeccak256(Deserial::deserial(source)?))
    }
}

impl Serial for ExchangeRates {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.euro_per_energy().serial(out)?;
        self.micro_ccd_per_euro().serial(out)?;
        Ok(())
    }
}

impl Deserial for ExchangeRates {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let euro_per_energy = source.get()?;
        let micro_ccd_per_euro = source.get()?;
        Ok(Self::new(euro_per_energy, micro_ccd_per_euro))
    }
}

impl Serial for AccountBalance {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.total().serial(out)?;
        self.staked().serial(out)?;
        self.locked().serial(&mut *out)?;
        Ok(())
    }
}

impl Deserial for AccountBalance {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let total = source.get()?;
        let staked = source.get()?;
        let locked = source.get()?;
        Self::new(total, staked, locked).ok_or_else(ParseError::default)
    }
}

impl schema::SchemaType for HashKeccak256 {
    fn get_type() -> concordium_contracts_common::schema::Type { schema::Type::ByteArray(32) }
}

unsafe impl<T, S: HasStateApi> StateClone<S> for StateSet<T, S> {
    unsafe fn clone_state(&self, cloned_state_api: &S) -> Self {
        Self {
            _marker:   self._marker,
            prefix:    self.prefix,
            state_api: cloned_state_api.clone(),
        }
    }
}

unsafe impl<T, V, S: HasStateApi> StateClone<S> for StateMap<T, V, S> {
    unsafe fn clone_state(&self, cloned_state_api: &S) -> Self {
        Self {
            _marker_key:   self._marker_key,
            _marker_value: self._marker_value,
            prefix:        self.prefix,
            state_api:     cloned_state_api.clone(),
        }
    }
}

unsafe impl<T: DeserialWithState<S> + Serial, S: HasStateApi> StateClone<S> for StateBox<T, S> {
    unsafe fn clone_state(&self, cloned_state_api: &S) -> Self {
        let inner_value = match &*self.inner.get() {
            StateBoxInner::Loaded {
                entry,
                modified,
                value: _,
            } => {
                // Get a new entry from the cloned state.
                let mut new_entry = cloned_state_api.lookup_entry(entry.get_key()).unwrap_abort();
                let new_value =
                    T::deserial_with_state(cloned_state_api, &mut new_entry).unwrap_abort();

                // Set position of new entry to match the old entry.
                let old_entry_position = entry.cursor_position();
                new_entry.seek(SeekFrom::Start(old_entry_position)).unwrap_abort();

                StateBoxInner::Loaded {
                    entry:    new_entry,
                    modified: *modified,
                    value:    new_value,
                }
            }
            StateBoxInner::Reference {
                prefix,
            } => StateBoxInner::Reference {
                prefix: *prefix,
            },
        };

        Self {
            state_api: cloned_state_api.clone(),
            inner:     UnsafeCell::new(inner_value),
        }
    }
}

/// Blanket implementation for all cloneable, flat types that don't have
/// references to items in the state.
unsafe impl<T: Clone, S> StateClone<S> for T {
    unsafe fn clone_state(&self, _cloned_state_api: &S) -> Self { self.clone() }
}
