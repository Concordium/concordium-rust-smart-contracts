use crate::{
    cell::{Ref, RefCell, RefMut},
    collections::{BTreeMap, BTreeSet},
    convert::{self, TryFrom, TryInto},
    fmt,
    hash::Hash,
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

impl convert::From<()> for Reject {
    #[inline(always)]
    fn from(_: ()) -> Self { unsafe { num::NonZeroI32::new_unchecked(i32::MIN + 1) }.into() }
}

impl convert::From<ParseError> for Reject {
    #[inline(always)]
    fn from(_: ParseError) -> Self {
        unsafe { num::NonZeroI32::new_unchecked(i32::MIN + 2) }.into()
    }
}

/// Full is mapped to i32::MIN+3, Malformed is mapped to i32::MIN+4.
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

/// The error code is i32::MIN + 12
impl From<NotPayableError> for Reject {
    #[inline(always)]
    fn from(_: NotPayableError) -> Self {
        unsafe { crate::num::NonZeroI32::new_unchecked(i32::MIN + 12) }.into()
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
    // TODO: Should this use another error type?
    type StateEntryData = ();
    type StateEntryKey = ();

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
                let end = self.size()?;
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

impl Read for StateEntry {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
        let len: u32 = {
            match buf.len().try_into() {
                Ok(v) => v,
                _ => return Err(ParseError::default()),
            }
        };
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

// The low-level entry type.
impl<StateEntryType> VacantEntryRaw<StateEntryType>
where
    StateEntryType: HasStateEntry,
{
    pub fn new(state_entry: StateEntryType) -> Self {
        Self {
            state_entry,
        }
    }

    pub fn insert(mut self, value: &[u8]) -> StateEntryType {
        self.state_entry.write_all(value).unwrap_abort(); // Writing to state cannot fail.
        self.state_entry.seek(SeekFrom::Start(0)).unwrap_abort(); // Reset cursor.
        self.state_entry
    }
}

// The low-level entry type.
impl<StateEntryType> OccupiedEntryRaw<StateEntryType>
where
    StateEntryType: HasStateEntry,
{
    pub fn new(state_entry: StateEntryType) -> Self {
        Self {
            state_entry,
        }
    }

    pub fn get_ref(&self) -> &StateEntryType { &self.state_entry }

    pub fn get(self) -> StateEntryType { self.state_entry }

    pub fn get_mut(&mut self) -> &mut StateEntryType { &mut self.state_entry }

    pub fn insert(&mut self, value: &[u8]) {
        // Rewind state entry. Cannot fail.
        self.state_entry.seek(SeekFrom::Start(0)).unwrap_abort();
        self.state_entry.write_all(value).unwrap_abort();

        // Truncate any data leftover from previous value.
        self.state_entry.truncate(value.len() as u32).unwrap_abort();
    }
}

impl<StateEntryType> EntryRaw<StateEntryType>
where
    StateEntryType: HasStateEntry,
{
    pub fn or_insert(self, default: &[u8]) -> StateEntryType {
        match self {
            EntryRaw::Vacant(vac) => vac.insert(default),
            EntryRaw::Occupied(occ) => occ.get(),
        }
    }
}

impl<'a, K, V, StateEntryType> VacantEntry<'a, K, V, StateEntryType>
where
    K: Serial,
    V: Serial,
    StateEntryType: HasStateEntry,
{
    pub fn new(key: K, state_entry: StateEntryType) -> Self {
        Self {
            key,
            state_entry,
            _lifetime_marker: PhantomData,
        }
    }

    pub fn key(&self) -> &K { &self.key }

    pub fn into_key(self) -> K { self.key }

    pub fn insert(mut self, value: V) {
        // Writing to state cannot fail.
        value.serial(&mut self.state_entry).unwrap_abort();
        self.state_entry.seek(SeekFrom::Start(0)).unwrap_abort(); // Reset cursor.
    }
}

impl<'a, K, V, StateEntryType> OccupiedEntry<'a, K, V, StateEntryType>
where
    K: Serial,
    V: Serial,
    StateEntryType: HasStateEntry,
{
    pub(crate) fn new(key: K, value: V, state_entry: StateEntryType) -> Self {
        Self {
            key,
            value,
            state_entry,
            _lifetime_marker: PhantomData,
        }
    }

    /// Get a reference to the key that is associated with this entry.
    #[inline(always)]
    pub fn key(&self) -> &K { &self.key }

    pub fn insert(mut self, value: V) {
        self.value = value;
        self.store_value();
    }

    /// Get an immutable reference to the value contained in this entry.
    #[inline(always)]
    pub fn get_ref(&self) -> &V { &self.value }

    // If we had Stored<V> then we wouldn't need this.
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

    /// Like [modify](Self::modify), but allows the closure to signal failure,
    /// aborting the update.
    pub fn try_modify<F, A, E>(&mut self, f: F) -> Result<A, E>
    where
        F: FnOnce(&mut V) -> Result<A, E>, {
        let res = f(&mut self.value)?;
        self.store_value();
        Ok(res)
    }

    fn store_value(&mut self) {
        let value_bytes = to_bytes(&self.value);
        // Rewind state entry. Cannot fail.
        self.state_entry.seek(SeekFrom::Start(0)).unwrap_abort();
        self.state_entry.write(&value_bytes).unwrap_abort();

        // Remove any additional data from prior value.
        self.state_entry.truncate(value_bytes.len() as u32).unwrap_abort();
    }
}

impl<'a, K, V, StateEntryType> Entry<'a, K, V, StateEntryType>
where
    K: Serial,
    V: Serial,
    StateEntryType: HasStateEntry,
{
    pub fn or_insert(self, default: V) {
        if let Entry::Vacant(vac) = self {
            vac.insert(default);
        }
    }

    /// Try to modify the entry using the given function.
    /// TODO: This might not be needed now that the high-level API unwraps the
    /// potential results.
    pub fn and_try_modify<F, E>(mut self, f: F) -> Result<Entry<'a, K, V, StateEntryType>, E>
    where
        F: FnOnce(&mut V) -> Result<(), E>, {
        if let Entry::Occupied(ref mut occ) = self {
            occ.try_modify(f)?;
        }
        Ok(self)
    }

    /// Modify the entry using the given function.
    pub fn and_modify<F>(mut self, f: F) -> Entry<'a, K, V, StateEntryType>
    where
        F: FnOnce(&mut V), {
        if let Entry::Occupied(ref mut occ) = self {
            occ.modify(f);
        }
        self
    }
}

impl<'a, K, V, StateEntryType> Entry<'a, K, V, StateEntryType>
where
    K: Serial,
    V: Serial + Default,
    StateEntryType: HasStateEntry,
{
    pub fn or_default(self) {
        if let Entry::Vacant(vac) = self {
            vac.insert(Default::default());
        }
    }
}

const NEXT_ITEM_PREFIX_KEY: u64 = 0;
#[cfg(test)]
const GENERIC_MAP_PREFIX: u64 = 1;
pub(crate) const INITIAL_NEXT_ITEM_PREFIX: u64 = 2;

impl HasState for StateApiExtern {
    type EntryType = StateEntry;
    type IterType = StateIterExtern;

    fn entry(&mut self, key: &[u8]) -> Result<EntryRaw<Self::EntryType>, StateError> {
        let key_start = key.as_ptr();
        let key_len = key.len() as u32; // Wasm usize == 32bit.
        let res = unsafe { prims::state_lookup_entry(key_start, key_len) };

        if res == u64::MAX {
            // No entry exists. Create one.
            let state_entry = self.create(key)?;
            Ok(EntryRaw::Vacant(VacantEntryRaw::new(state_entry)))
        } else {
            // Lookup returned an entry.
            let entry_id = res;
            Ok(EntryRaw::Occupied(OccupiedEntryRaw::new(StateEntry::open(entry_id, key.to_vec()))))
        }
    }

    fn create(&mut self, key: &[u8]) -> Result<Self::EntryType, StateError> {
        let key_start = key.as_ptr();
        let key_len = key.len() as u32; // Wasm usize == 32bit.
        let entry_id = unsafe { prims::state_create_entry(key_start, key_len) };
        if entry_id == u64::MAX {
            return Err(StateError::SubtreeLocked);
        }
        Ok(StateEntry::open(entry_id, key.to_vec()))
    }

    fn lookup(&self, key: &[u8]) -> Option<Self::EntryType> {
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
            _ => crate::fail!(), // Cannot happen.
        }
    }

    fn delete_prefix(&mut self, prefix: &[u8]) -> Result<(), StateError> {
        let res = unsafe { prims::state_delete_prefix(prefix.as_ptr(), prefix.len() as u32) };
        match res {
            0 => Err(StateError::SubtreeLocked),
            1 => Err(StateError::EntryNotFound),
            2 => Ok(()),
            _ => crate::fail!(), // Cannot happen.
        }
    }

    fn iterator(&self, prefix: &[u8]) -> Result<Self::IterType, StateError> {
        let prefix_start = prefix.as_ptr();
        let prefix_len = prefix.len() as u32; // Wasm usize == 32bit.
        let iterator_id = unsafe { prims::state_iterate_prefix(prefix_start, prefix_len) };
        let all_ones = u64::MAX;
        if iterator_id == all_ones {
            return Err(StateError::IteratorLimitForPrefixExceeded);
        }
        if iterator_id | 1u64.rotate_right(2) == all_ones {
            return Err(StateError::EntryNotFound);
        }
        Ok(StateIterExtern {
            iterator_id,
        })
    }

    fn delete_iterator(&mut self, iter: Self::IterType) {
        // This call can never fail because the only way to get an `StateIterExtern`
        // is through `StateApi::iterator(..)`. And this call consumes
        // the iterator.
        // These conditions rule out the two types of errors that the prims
        // call can return, iterator not found and iterator already deleted.
        // The iterator can also be deleted with `delete_iterator_by_id`, but that is
        // only called when a [StateMapIter] or [StateSetIter] is dropped (which
        // also drops the [StateIterExtern]). Again ruling out the already
        // deleted error.
        unsafe { prims::state_iterator_delete(iter.iterator_id) };
    }
}

impl Iterator for StateIterExtern {
    type Item = StateEntry;

    fn next(&mut self) -> Option<Self::Item> {
        let res = unsafe { prims::state_iterator_next(self.iterator_id) };
        match res {
            // This means that an iterator never existed or was deleted.
            // In both cases, it is not possible to call `next` on such an iterator with the current
            // API. The only way to get an iterator is through
            // [HasState::iterator] and the only way to delete it is through
            // [HasState::delete_iterator].
            u64::MAX => crate::fail!(),
            _ if res | 1u64.rotate_right(2) == u64::MAX => None,
            _ => {
                // This will always return a valid size, because the iterator is guaranteed to
                // exist.
                let key_size = unsafe { prims::state_iterator_key_size(self.iterator_id) };
                let mut key = Vec::with_capacity(key_size as usize);
                // The key will always be read, because the iterator is guaranteed to exist.
                unsafe {
                    prims::state_iterator_key_read(self.iterator_id, key.as_mut_ptr(), key_size, 0)
                };
                Some(StateEntry::open(res, key))
            }
        }
    }
}

impl<K, V, S> StateMap<K, V, S>
where
    S: HasState,
    K: Serialize,
    V: Serial + DeserialWithState<S> + Deletable,
{
    /// Lookup the value with the given key. Return [None] if there is no value
    /// with the given key.
    pub fn get(&self, key: &K) -> Option<StateRef<V>> {
        let k = self.key_with_map_prefix(&key);
        self.state_ll.lookup(&k).map(|mut entry| {
            // Unwrapping is safe when using only the high-level API.
            StateRef::new(V::deserial_with_state(&self.state_ll, &mut entry).unwrap_abort())
        })
    }

    /// Inserts the value with the given key. If a value already exists at the
    /// given key it is replaced, and the old value is returned.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let key_bytes = self.key_with_map_prefix(&key);
        let value_bytes = to_bytes(&value);
        // Unwrapping is safe because iter() holds a reference to the stateset.
        match self.state_ll.entry(&key_bytes).unwrap_abort() {
            EntryRaw::Vacant(vac) => {
                let _ = vac.insert(&value_bytes);
                None
            }
            EntryRaw::Occupied(mut occ) => {
                // Unwrapping is safe when using only the high-level API.
                let old_value =
                    V::deserial_with_state(&self.state_ll, occ.get_mut()).unwrap_abort();
                occ.insert(&value_bytes);
                Some(old_value)
            }
        }
    }

    /// Get an entry for the given key.
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V, S::EntryType> {
        let key_bytes = self.key_with_map_prefix(&key);
        // Unwrapping is safe because iter() holds a reference to the stateset.
        match self.state_ll.entry(&key_bytes).unwrap_abort() {
            EntryRaw::Vacant(vac) => Entry::Vacant(VacantEntry::new(key, vac.state_entry)),
            EntryRaw::Occupied(mut occ) => {
                // Unwrapping is safe when using only the high-level API.
                let value = V::deserial_with_state(&self.state_ll, occ.get_mut()).unwrap_abort();
                Entry::Occupied(OccupiedEntry::new(key, value, occ.state_entry))
            }
        }
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool { self.state_ll.lookup(&self.prefix).is_none() }

    /// Clears the map, removing all key-value pairs.
    /// This also includes values pointed at, if `V`, for example, is a
    /// [StateBox].
    // Note: This does not use delete() because delete consumes self.
    pub fn clear(&mut self) {
        // Delete all values pointed at by the statemap. This is necessary if `V` is a
        // StateBox/StateMap.
        // TODO: Ideally, only delete when `V` _is_ a statetype.
        for (_, value) in self.iter() {
            value.value.delete()
        }

        // Then delete the map itself.
        // Unwrapping is safe when only using the high-level API.
        self.state_ll.delete_prefix(&self.prefix).unwrap_abort();
    }

    /// Remove a key from the map, returning the value at the key if the key was
    /// previously in the map.
    ///
    /// *Caution*: If `V` is a [StateBox], [StateMap], then it is
    /// important to call `Deletable::delete` on the value returned when you're
    /// finished with it. Otherwise, it will remain in the contract state.
    #[must_use]
    pub fn remove_and_get(&mut self, key: &K) -> Option<V> {
        let key_bytes = self.key_with_map_prefix(key);
        // Unwrapping is safe because iter() holds a reference to the stateset.
        let entry_raw = self.state_ll.entry(&key_bytes).unwrap_abort();
        match entry_raw {
            EntryRaw::Vacant(_) => None,
            EntryRaw::Occupied(mut occ) => {
                // Unwrapping safe in high-level API.
                let old_value =
                    V::deserial_with_state(&self.state_ll, occ.get_mut()).unwrap_abort();
                let _existed = self.state_ll.delete_entry(occ.state_entry);
                Some(old_value)
            }
        }
    }

    /// Remove a key from the map.
    /// This also deletes the value in the state.
    pub fn remove(&mut self, key: &K) {
        if let Some(v) = self.remove_and_get(key) {
            v.delete()
        }
    }

    fn key_with_map_prefix(&self, key: &K) -> Vec<u8> {
        let mut key_with_prefix = self.prefix.clone();
        key.serial(&mut key_with_prefix).unwrap_abort();
        key_with_prefix
    }
}

impl<'a, K, V, S: HasState> Drop for StateMapIter<'a, K, V, S> {
    fn drop(&mut self) {
        // Delete the iterator to unlock the subtree.
        if let Some(valid) = self.state_iter.take() {
            self.state_ll.delete_iterator(valid);
        }
    }
}

impl<K, V, S> StateMap<K, V, S>
where
    S: HasState,
{
    pub(crate) fn open<P: Serial>(state_ll: S, prefix: P) -> Self {
        Self {
            _marker_key: PhantomData,
            _marker_value: PhantomData,
            prefix: to_bytes(&prefix),
            state_ll,
        }
    }

    /// Get an iterator over the key-value pairs of the map. The iterator
    /// returns values in increasing order of keys, where keys are ordered
    /// lexicographically via their serializations.
    pub fn iter(&self) -> StateMapIter<'_, K, V, S> {
        let state_iter = self.state_ll.iterator(&self.prefix).unwrap_abort();
        StateMapIter {
            state_iter:       Some(state_iter),
            state_ll:         self.state_ll.clone(),
            _lifetime_marker: PhantomData,
        }
    }

    /// Like [iter](Self::iter), but allows modifying the values during
    /// iterator.
    pub fn iter_mut(&mut self) -> StateMapIterMut<'_, K, V, S> {
        let state_iter = self.state_ll.iterator(&self.prefix).unwrap_abort();
        StateMapIterMut {
            state_iter:       Some(state_iter),
            state_ll:         self.state_ll.clone(),
            _lifetime_marker: PhantomData,
        }
    }
}

impl<'a, K, V, S: HasState> Iterator for StateMapIter<'a, K, V, S>
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
        let v = V::deserial_with_state(&self.state_ll, &mut entry).unwrap_abort();
        Some((StateRef::new(k), StateRef::new(v)))
    }
}

impl<'a, K, V, S: HasState> Iterator for StateMapIterMut<'a, K, V, S>
where
    K: Deserial + 'a,
    V: DeserialWithState<S> + 'a,
{
    type Item = (StateRef<'a, K>, StateRefMut<'a, V, S>);

    fn next(&mut self) -> Option<Self::Item> {
        let mut entry = self.state_iter.as_mut()?.next()?;
        let key_bytes = entry.get_key().to_vec();
        let mut key_cursor = Cursor {
            data:   &key_bytes,
            offset: 8, // Items in a map always start with the set prefix which is 8 bytes.
        };
        // Unwrapping is safe when only using the high-level API.
        let k = K::deserial(&mut key_cursor).unwrap_abort();
        let v = V::deserial_with_state(&self.state_ll, &mut entry).unwrap_abort();
        Some((StateRef::new(k), StateRefMut::new(v, &key_bytes, self.state_ll.clone())))
    }
}

impl<'a, V, S> StateRefMut<'a, V, S>
where
    V: Serial + DeserialWithState<S>,
    S: HasState,
{
    pub fn get(&self) -> Ref<'_, V> { self.state_box.get() }

    pub fn set(&mut self, new_val: V) { self.state_box.set(new_val) }

    pub fn update<F>(&mut self, f: F)
    where
        F: FnOnce(&mut V), {
        self.state_box.update(f);
    }
}

impl<K, V, S> Serial for StateMap<K, V, S> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        serial_vector_no_length(&self.prefix, out)
    }
}

impl<T, S> StateSet<T, S>
where
    T: Serialize,
    S: HasState,
{
    /// Adds a value to the set.
    /// If the set did not have this value, `true` is returned. Otherwise,
    /// `false`.
    pub fn insert(&mut self, value: T) -> bool {
        let key_bytes = self.key_with_set_prefix(&value);
        // Unwrapping is safe, because iter() keeps a reference to the statemap.
        match self.state_ll.entry(&key_bytes).unwrap_abort() {
            EntryRaw::Vacant(vac) => {
                let _ = vac.insert(&[]);
                true
            }
            EntryRaw::Occupied(_) => false,
        }
    }

    /// Returns `true` if the set contains no elements.
    pub fn is_empty(&self) -> bool { self.state_ll.lookup(&self.prefix).is_none() }

    /// Returns `true` if the set contains a value.
    pub fn contains(&self, value: &T) -> bool {
        let key_bytes = self.key_with_set_prefix(value);
        self.state_ll.lookup(&key_bytes).is_some()
    }

    /// Clears the set, removing all values.
    /// This also includes values pointed at, if `V`, for example, is a
    /// [StateBox].
    // Note: This does not use delete() because delete consumes self.
    pub fn clear(&mut self) {
        // Delete all values in the stateset. This is necessary if `T` is a
        // StateBox/StateMap.
        for value in self.iter() {
            value.value.delete()
        }
        // Unwrapping is safe when only using the high-level API.
        self.state_ll.delete_prefix(&self.prefix).unwrap_abort()
    }

    /// Removes a value from the set. Returns whether the value was present in
    /// the set.
    pub fn remove(&mut self, value: &T) -> bool {
        let key_bytes = self.key_with_set_prefix(value);

        // Unwrapping is safe, because iter() keeps a reference to the stateset.
        match self.state_ll.entry(&key_bytes).unwrap_abort() {
            EntryRaw::Vacant(_) => false,
            EntryRaw::Occupied(occ) => {
                // Unwrapping is safe, because iter() keeps a reference to the stateset.
                self.state_ll.delete_entry(occ.get()).unwrap_abort();
                true
            }
        }
    }

    fn key_with_set_prefix(&self, key: &T) -> Vec<u8> {
        let mut key_with_prefix = self.prefix.clone();
        key.serial(&mut key_with_prefix).unwrap_abort();
        key_with_prefix
    }
}

impl<T, S: HasState> StateSet<T, S> {
    pub(crate) fn open<P: Serial>(state_ll: S, prefix: P) -> Self {
        Self {
            _marker: PhantomData,
            prefix: to_bytes(&prefix),
            state_ll,
        }
    }

    pub fn iter(&self) -> StateSetIter<T, S> {
        let state_iter = self.state_ll.iterator(&self.prefix).unwrap_abort();
        StateSetIter {
            state_iter:       Some(state_iter),
            state_ll:         self.state_ll.clone(),
            _marker_lifetime: PhantomData,
        }
    }
}

impl<T, S> StateBox<T, S> {
    /// Create a new statebox.
    pub(crate) fn new(value: T, state_ll: S, prefix: StateItemPrefix) -> Self {
        Self {
            prefix,
            state_ll,
            lazy_value: RefCell::new(Some(value)),
        }
    }
}

impl<T, S> StateBox<T, S>
where
    T: Serial + DeserialWithState<S>,
    S: HasState,
{
    /// Get a reference to the value.
    // TODO: Figure out if we can implement Deref that uses this method.
    pub fn get(&self) -> Ref<'_, T> {
        self.ensure_cached();
        // Unwrapping is safe because the value is cached.
        Ref::map(self.lazy_value.borrow(), |t| t.as_ref().unwrap_abort())
    }

    /// Set the value. Overwrites the existing one.
    pub fn set(&mut self, new_val: T) {
        self.store_value(&new_val);
        *self.lazy_value.borrow_mut() = Some(new_val);
    }

    /// Update the existing value with the given function.
    pub fn update<F>(&mut self, f: F)
    where
        F: FnOnce(&mut T), {
        self.ensure_cached();
        let mut value = RefMut::map(self.lazy_value.borrow_mut(), |t| t.as_mut().unwrap_abort());

        // Mutate the value (perhaps only in memory, depends on the type).
        f(&mut value);

        // Store the value in the state.
        self.store_value(&value)
    }

    /// Stores the value in the state.
    fn store_value(&self, value: &T) {
        // Both unwraps are safe when using only the high-level API.
        let mut state_entry = self.state_ll.lookup(&self.prefix).unwrap_abort();
        value.serial(&mut state_entry).unwrap_abort()
    }

    /// If the value isn't cached, it loads the value from the state and sets
    /// the lazy_value field.
    fn ensure_cached(&self) {
        if self.lazy_value.borrow_mut().is_none() {
            let mut state_entry = self.state_ll.lookup(&self.prefix).unwrap_abort();
            let value = T::deserial_with_state(&self.state_ll, &mut state_entry).unwrap_abort();
            *self.lazy_value.borrow_mut() = Some(value);
        }
    }
}

impl<T, S> Serial for StateBox<T, S> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        serial_vector_no_length(&self.prefix, out)
    }
}

impl<T, S> Serial for StateSet<T, S> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        serial_vector_no_length(&self.prefix, out)
    }
}

/// Unlock the part of the tree locked by the iterator.
impl<'a, T, S: HasState> Drop for StateSetIter<'a, T, S> {
    #[inline]
    fn drop(&mut self) {
        // Delete the iterator to unlock the subtree.
        if let Some(valid) = self.state_iter.take() {
            self.state_ll.delete_iterator(valid);
        }
    }
}

impl<'a, T, S: HasState> Iterator for StateSetIter<'a, T, S>
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
        let t = T::deserial_with_state(&self.state_ll, &mut key_cursor).unwrap_abort();
        Some(StateRef::new(t))
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
        let num_read = unsafe {
            prims::get_parameter_section(0, buf.as_mut_ptr(), len, self.current_position)
        };
        self.current_position += num_read as u32; // parameter 0 always exists, so this is safe.
        Ok(num_read as usize)
    }
}

impl HasParameter for ExternParameter {
    #[inline(always)]
    // parameter 0 always exists so this is correct
    fn size(&self) -> u32 { unsafe { prims::get_parameter_size(0) as u32 } }
}

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
impl HasChainMetadata for ChainMetaExtern {
    #[inline(always)]
    fn slot_time(&self) -> SlotTime {
        Timestamp::from_timestamp_millis(unsafe { prims::get_slot_time() })
    }
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
            let num_read = prims::get_policy_section(
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
            prims::get_policy_section(
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
            prims::get_policy_section(buf.as_mut_ptr() as *mut u8, 2, 0);
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

/// Tag of the transfer operation expected by the host. See [prims::invoke].
const INVOKE_TRANSFER_TAG: u32 = 0;
/// Tag of the transfer operation expected by the host. See [prims::invoke].
const INVOKE_CALL_TAG: u32 = 1;

/// Decode the the response code.
///
/// This is necessary since Wasm only allows us to pass simple scalars as
/// parameters. Everything else requires passing data in memory, or via host
/// functions, both of which are difficult.
///
/// The response is encoded as follows.
/// - success is encoded as 0
/// - every failure has all bits of the first 3 bytes set
/// - in case of failure
///   - if the 4th byte is 0 then the remaining 4 bytes encode the rejection
///     reason from the contract
///   - otherwise only the 4th byte is used, and encodes the enviroment failure.
fn parse_transfer_response_code(code: u64) -> TransferResult {
    if code & !0xffff_ff00_0000_0000 == 0 {
        // success
        // assume response from host conforms to spec, just return success.
        Ok(())
    } else {
        // failure.
        match (0x0000_00ff_0000_0000 & code) >> 32 {
            0x01 => Err(TransferError::AmountTooLarge),
            0x02 => Err(TransferError::MissingAccount),
            _ => crate::trap(), // host precondition violation
        }
    }
}

/// Decode the the response code.
///
/// This is necessary since Wasm only allows us to pass simple scalars as
/// parameters. Everything else requires passing data in memory, or via host
/// functions, both of which are difficult.
///
/// The response is encoded as follows.
/// - success is encoded as 0
/// - every failure has all bits of the first 3 bytes set
/// - in case of failure
///   - if the 4th byte is 0 then the remaining 4 bytes encode the rejection
///     reason from the contract
///   - otherwise only the 4th byte is used, and encodes the enviroment failure.
fn parse_call_response_code(code: u64) -> CallContractResult<ExternCallResponse> {
    if code & !0xffff_ff00_0000_0000 == 0 {
        // this means success
        let rv = (code >> 40) as u32;
        let tag = 0x80_0000u32;
        if tag & rv != 0 {
            Ok((true, NonZeroU32::new(rv & !tag).map(ExternCallResponse::new)))
        } else {
            Ok((false, NonZeroU32::new(rv).map(ExternCallResponse::new)))
        }
    } else {
        match (0x0000_00ff_0000_0000 & code) >> 32 {
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
                        crate::trap() // host precondition violation.
                    }
                }
            }
            0x01 => Err(CallContractError::AmountTooLarge),
            0x02 => Err(CallContractError::MissingAccount),
            0x03 => Err(CallContractError::MissingContract),
            0x04 => Err(CallContractError::MissingEntrypoint),
            0x05 => Err(CallContractError::MessageFailed),
            0x06 => Err(CallContractError::Trap),
            _ => crate::trap(), // host precondition violation
        }
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

impl<S> Allocator<S>
where
    S: HasState,
{
    /// Open a new allocator. Only a single instance of the allocator should
    /// exist during contract execution, thus this should only be called at
    /// the very beginning of execution.
    pub fn open(state: S) -> Self {
        Self {
            state,
        }
    }

    /// Create a new empty [`StateMap`].
    pub fn new_map<K, V>(&mut self) -> StateMap<K, V, S> {
        let prefix = self.get_and_update_item_prefix();
        StateMap::open(self.state.clone(), prefix)
    }

    /// Create a new empty [`StateSet`].
    pub fn new_set<T>(&mut self) -> StateSet<T, S> {
        let prefix = self.get_and_update_item_prefix();
        StateSet::open(self.state.clone(), prefix)
    }

    /// Create a new [`StateBox`] and insert the `value` into the state.
    pub fn new_box<T: Serial>(&mut self, value: T) -> StateBox<T, S> {
        let prefix = self.get_and_update_item_prefix();
        let prefix_bytes = to_bytes(&prefix);

        // Insert the value into the state
        let mut state_entry = self.state.create(&prefix_bytes).unwrap_abort();
        value.serial(&mut state_entry).unwrap_abort();

        StateBox::new(value, self.state.clone(), prefix_bytes)
    }

    fn get_and_update_item_prefix(&mut self) -> u64 {
        // Get the next prefix or insert and use the initial one.
        let entry_key = to_bytes(&NEXT_ITEM_PREFIX_KEY);
        let default_prefix = to_bytes(&INITIAL_NEXT_ITEM_PREFIX);
        // Unwrapping is safe when using the high-level API because it is not possible
        // to get an iterator that locks this entry.
        let mut next_collection_prefix_entry =
            self.state.entry(&entry_key).unwrap_abort().or_insert(&default_prefix);

        // Get the next collection prefix
        let collection_prefix = next_collection_prefix_entry.read_u64().unwrap_abort(); // Unwrapping is safe if only using the high-level API.

        // Rewind state entry position. Cannot fail.
        next_collection_prefix_entry.seek(SeekFrom::Start(0)).unwrap_abort();

        // Increment the collection prefix
        next_collection_prefix_entry.write_u64(collection_prefix + 1).unwrap_abort(); // Writing to state cannot fail.

        collection_prefix
    }
}

#[cfg(test)]
/// Some helper methods that are used for internal tests.
impl<S> Allocator<S>
where
    S: HasState,
{
    /// Some(Err(_)) means that something exists in the state with that key, but
    /// it isn't of type `V`.
    pub(crate) fn get<K: Serial, V: DeserialWithState<S>>(&self, key: K) -> Option<ParseResult<V>> {
        let key_with_map_prefix = Self::prepend_generic_map_key(key);

        self.state
            .lookup(&key_with_map_prefix)
            .map(|mut entry| V::deserial_with_state(&self.state, &mut entry))
    }

    pub(crate) fn insert<K: Serial, V: Serial>(
        &mut self,
        key: K,
        value: V,
    ) -> Result<(), StateError> {
        let key_with_map_prefix = Self::prepend_generic_map_key(key);
        let value_bytes = to_bytes(&value);
        match self.state.entry(&key_with_map_prefix)? {
            EntryRaw::Vacant(vac) => {
                let _ = vac.insert(&value_bytes);
            }
            EntryRaw::Occupied(mut occ) => occ.insert(&value_bytes),
        }
        Ok(())
    }

    fn prepend_generic_map_key<K: Serial>(key: K) -> Vec<u8> {
        let mut key_with_map_prefix = to_bytes(&GENERIC_MAP_PREFIX);
        key_with_map_prefix.append(&mut to_bytes(&key));
        key_with_map_prefix
    }
}

impl<S> HasHost<S> for ExternHost<S>
where
    S: DeserialWithState<StateApiExtern>,
{
    type ReturnValueType = ExternCallResponse;
    type StateType = StateApiExtern;

    fn invoke_transfer(&self, receiver: &AccountAddress, amount: Amount) -> TransferResult {
        invoke_transfer_worker(receiver, amount)
    }

    fn invoke_contract(
        &mut self,
        to: &ContractAddress,
        parameter: Parameter,
        method: EntrypointName,
        amount: Amount,
    ) -> CallContractResult<Self::ReturnValueType> {
        let data = invoke_contract_construct_parameter(to, parameter, method, amount);
        let len = data.len();
        let response = unsafe { prims::invoke(INVOKE_CALL_TAG, data.as_ptr(), len as u32) };
        let (state_modified, res) = parse_call_response_code(response)?;
        if state_modified {
            // The state of the contract changed as a result of the call.
            // So we refresh it.
            if let Ok(new_state) = S::deserial_with_state(
                &self.allocator.state,
                &mut self.allocator.state.lookup(&[]).unwrap_abort(),
            ) {
                self.state = new_state;
            } else {
                crate::trap() // FIXME: With new state this needs to be revised.
            }
        }
        Ok((state_modified, res))
    }

    fn state(&self) -> &S { &self.state }

    fn state_mut(&mut self) -> &mut S { &mut self.state }

    #[inline(always)]
    fn self_balance(&self) -> Amount {
        Amount::from_micro_ccd(unsafe { prims::get_receive_self_balance() })
    }

    fn allocator(&mut self) -> &mut Allocator<Self::StateType> { &mut self.allocator }
}

impl HasHost<StateApiExtern> for ExternLowLevelHost {
    type ReturnValueType = ExternCallResponse;
    type StateType = StateApiExtern;

    fn invoke_transfer(&self, receiver: &AccountAddress, amount: Amount) -> TransferResult {
        invoke_transfer_worker(receiver, amount)
    }

    fn invoke_contract(
        &mut self,
        to: &ContractAddress,
        parameter: Parameter,
        method: EntrypointName,
        amount: Amount,
    ) -> CallContractResult<Self::ReturnValueType> {
        let data = invoke_contract_construct_parameter(to, parameter, method, amount);
        let len = data.len();
        let response = unsafe { prims::invoke(INVOKE_CALL_TAG, data.as_ptr(), len as u32) };
        // TODO: Figure out if we need to do anything special here.
        // Old entries are invalidated by the host, so no cursors should need to be
        // reset.
        parse_call_response_code(response)
    }

    #[inline(always)]
    fn state(&self) -> &StateApiExtern { &self.state }

    #[inline(always)]
    fn state_mut(&mut self) -> &mut StateApiExtern { &mut self.state }

    #[inline(always)]
    fn self_balance(&self) -> Amount {
        Amount::from_micro_ccd(unsafe { prims::get_receive_self_balance() })
    }

    fn allocator(&mut self) -> &mut Allocator<Self::StateType> { &mut self.allocator }
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
            prims::get_init_origin(ptr as *mut u8);
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

/// Blanket implementation for Deserial, which simply does not use the state
/// argument.
impl<D: Deserial, S: HasState> DeserialWithState<S> for D {
    fn deserial_with_state<R: Read>(_state: &S, source: &mut R) -> ParseResult<Self> {
        Self::deserial(source)
    }
}

/// Blanket implementation for DeserialCtx, which simply does not use the state
/// argument.
impl<D: DeserialCtx, S: HasState> DeserialCtxWithState<S> for D {
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
    S: HasState,
{
    fn deserial_with_state<R: Read>(state: &S, source: &mut R) -> ParseResult<Self> {
        source.read_u64().map(|map_prefix| StateMap::open(state.clone(), map_prefix))
    }
}

impl<T, S> DeserialWithState<S> for StateSet<T, S>
where
    S: HasState,
    T: Serial + DeserialWithState<S>,
{
    fn deserial_with_state<R: Read>(state: &S, source: &mut R) -> ParseResult<Self> {
        source.read_u64().map(|set_prefix| StateSet::open(state.clone(), set_prefix))
    }
}

impl<T, S> DeserialWithState<S> for StateBox<T, S>
where
    S: HasState,
    T: Serial + DeserialWithState<S>,
{
    fn deserial_with_state<R: Read>(state: &S, source: &mut R) -> ParseResult<Self> {
        let mut prefix = [0u8; 8];
        source.read_exact(&mut prefix)?;
        Ok(StateBox {
            state_ll:   state.clone(),
            prefix:     prefix.to_vec(),
            lazy_value: RefCell::new(None),
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
    S: HasState,
{
    fn delete(mut self) {
        // Make sure the actual value is cached, so we can delete it.
        self.ensure_cached();

        // Delete the box node itself.
        // Unwrapping is safe when only using the high-level API.
        let entry = self.state_ll.lookup(&self.prefix).unwrap_abort();
        self.state_ll.delete_entry(entry).unwrap_abort();

        // Then delete the lazy value.
        // Unwrapping the option is safe, because we ensured the value is cached.
        self.lazy_value.into_inner().unwrap_abort().delete();
    }
}

impl<T, S> Deletable for StateSet<T, S>
where
    S: HasState,
{
    fn delete(mut self) {
        // Statesets cannot contain state types (e.g. StateBox), so there is nothing to
        // delete, apart from the set itself.

        // Unwrapping is safe when only using the high-level API.
        self.state_ll.delete_prefix(&self.prefix).unwrap_abort()
    }
}

impl<K, V, S> Deletable for StateMap<K, V, S>
where
    S: HasState,
    K: Deserial,
    V: DeserialWithState<S> + Deletable,
{
    fn delete(mut self) {
        // Delete all values pointed at by the statemap. This is necessary if `V` is a
        // StateBox/StateMap.
        for (_, value) in self.iter() {
            value.value.delete()
        }

        // Then delete the map itself.
        // Unwrapping is safe when only using the high-level API.
        self.state_ll.delete_prefix(&self.prefix).unwrap_abort()
    }
}
