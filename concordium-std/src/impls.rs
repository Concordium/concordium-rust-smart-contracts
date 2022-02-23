use crate::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    convert::{self, TryFrom, TryInto},
    fail, fmt,
    hash::Hash,
    marker::PhantomData,
    mem, num,
    num::NonZeroU32,
    prims::{self, *},
    rc::Rc,
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

/// Return values are intended to be produced by writing to the [ReturnValue]
/// buffer, either in a high-level interface via serialization, or in a
/// low-level interface by manually using the [Write] trait's interface.
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

impl ReturnValue {
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
    pub(crate) fn open(state_entry_id: StateEntryId) -> Self {
        Self {
            state_entry_id,
            current_position: 0,
        }
    }

    /// Returns the key length or an error if the iterator is not found.
    fn get_key_length(&self) -> Result<u32, ()> {
        let key_len = unsafe { prims::state_iterator_key_size(self.state_entry_id) };
        match key_len {
            u32::MAX => Err(()),
            n => Ok(n),
        }
    }

    /// Returns the next iterator key or an error if the iterator is not found.
    fn load_key(&self, key_len: u32) -> Result<Vec<u8>, ContractStateError> {
        let mut key = Vec::with_capacity(key_len as usize);
        let key_ptr = key.as_mut_ptr();
        let res = unsafe { prims::state_iterator_key_read(self.state_entry_id, key_ptr, key_len, 0) };
        match res {
            u32::MAX => Err(ContractStateError::EntryNotFound),
            _ => Ok(key),
        }
    }

    fn state_entry_read(&mut self, buf: &mut [u8]) -> Result<u32, ContractStateError> {
        let len = buf.len().try_into().map_err(|_| ContractStateError::SizeTooLarge)?;
        let num_read =
            unsafe { prims::state_entry_read(self.state_entry_id, buf.as_mut_ptr(), len, self.current_position) };
        match num_read {
            u32::MAX => Err(ContractStateError::EntryNotFound),
            _ => Ok(num_read)
        }
    }

    fn state_entry_write(&mut self, buf: &[u8]) -> Result<u32, ContractStateError> {
        let len = buf.len().try_into().map_err(|_| ContractStateError::SizeTooLarge)?;
        if self.current_position.checked_add(len).is_none() {
            return Err(ContractStateError::SizeTooLarge);
        }
        let res = unsafe {
            prims::state_entry_write(self.state_entry_id, buf.as_ptr(), len, self.current_position)
        };
        match res {
            u32::MAX => Err(ContractStateError::EntryNotFound),
            _ => Ok(res),
        }
    }

    fn state_entry_size(&self) -> Result<u32, ContractStateError> {
        let res = unsafe { prims::state_entry_size(self.state_entry_id) };
        match res {
            u32::MAX => Err(ContractStateError::EntryNotFound),
            _ => Ok(res),
        }
    }
}

impl HasContractStateEntry for StateEntry {
    type Error = ();
    type StateEntryData = ();
    type StateEntryKey = ();

    fn open(_: Self::StateEntryData, _: Self::StateEntryKey, entry_id: StateEntryId) -> Self {
        Self::open(entry_id)
    }

    #[inline(always)]
    fn size(&self) -> Result<u32, Self::Error> {
        self.state_entry_size().map_err(|_| ())
    }

    fn get_key(&self) -> Result<Vec<u8>, ()> {
        let key_len = self.get_key_length()?;
        self.load_key(key_len).map_err(|_| ())
    }

    fn get_position(&self) -> u32 {
        self.current_position
    }

    fn set_position(&mut self, new_size: u32) {
        self.current_position = new_size
    }

    fn resize(&mut self, new_size: u32) -> Result<(), Self::Error> {
        let res = unsafe { prims::state_entry_resize(self.state_entry_id, new_size) };
        match res {
            1 => Ok(()),
            0 => Err(()),
            _ => Err(()),
        }
    }
}

/// # NEW Contract state trait implementations.
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
        let num_read = self.state_entry_read(buf).map_err(|_| ParseError::default())?;
        self.current_position += num_read;
        Ok(num_read as usize)
    }
}

impl Write for StateEntry {
    type Err = ();

    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Err> {
        let num_bytes = self.state_entry_write(buf).map_err(|_| ())?;
        self.current_position += num_bytes; // safe because of check above that len + pos is small enough
        Ok(num_bytes as usize)
    }
}

// The low-level entry type.
impl<StateEntryType> VacantEntryRaw<StateEntryType>
where
    StateEntryType: HasContractStateEntry,
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
    StateEntryType: HasContractStateEntry,
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
        self.state_entry.write_all(value).unwrap_abort(); // Writing to state
                                                          // cannot fail.
    }
}

impl<StateEntryType> EntryRaw<StateEntryType>
where
    StateEntryType: HasContractStateEntry,
{
    pub fn or_insert(self, default: &[u8]) -> StateEntryType {
        match self {
            EntryRaw::Vacant(vac) => vac.insert(default),
            EntryRaw::Occupied(occ) => occ.get(),
        }
    }
}

impl<K, V, StateEntryType> VacantEntry<K, V, StateEntryType>
where
    K: Serial,
    V: Serial,
    StateEntryType: HasContractStateEntry,
{
    pub fn new(key: K, state_entry: StateEntryType) -> Self {
        Self {
            key,
            state_entry,
            _marker_value: PhantomData,
        }
    }

    pub fn key(&self) -> &K { &self.key }

    pub fn into_key(self) -> K { self.key }

    pub fn insert(mut self, value: V) {
        // Writing to state cannot fail.
        self.state_entry.write_all(&to_bytes(&value)).unwrap_abort();
        self.state_entry.seek(SeekFrom::Start(0)).unwrap_abort(); // Reset cursor.
    }
}

impl<K, V, StateEntryType> OccupiedEntry<K, V, StateEntryType>
where
    K: Serial,
    V: Serial,
    StateEntryType: HasContractStateEntry,
{
    pub fn new(key: K, value: V, state_entry: StateEntryType) -> Self {
        Self {
            key,
            value,
            state_entry,
        }
    }

    pub fn key(&self) -> &K { &self.key }

    pub fn insert(mut self, value: V) {
        // Rewind state entry. Cannot fail.
        self.state_entry.seek(SeekFrom::Start(0)).unwrap_abort();
        value.serial(&mut self.state_entry).unwrap_abort(); // Writing to
                                                            // state cannot
                                                            // fail.
    }

    pub fn get_ref(&self) -> &V { &self.value }

    pub fn get(self) -> V { self.value }

    // If we had Stored<V> then we wouldn't need this.
    pub fn modify<F>(&mut self, f: F)
    where
        F: FnOnce(&mut V), {
        f(&mut self.value);
        // Rewind state entry. Cannot fail.
        self.state_entry.seek(SeekFrom::Start(0)).unwrap_abort();
        self.value.serial(&mut self.state_entry).unwrap_abort(); // Writing to
                                                                 // state cannot
                                                                 // fail.
    }

    pub fn try_modify<F, E>(&mut self, f: F) -> Result<(), E>
    where
        F: FnOnce(&mut V) -> Result<(), E>, {
        f(&mut self.value)?;
        // Rewind state entry. Cannot fail.
        self.state_entry.seek(SeekFrom::Start(0)).unwrap_abort();
        self.value.serial(&mut self.state_entry).unwrap_abort(); // Writing to state cannot fail.
        Ok(())
    }
}

impl<K, V, StateEntryType> Entry<K, V, StateEntryType>
where
    K: Serial,
    V: Serial,
    StateEntryType: HasContractStateEntry,
{
    pub fn or_insert(self, default: V) {
        if let Entry::Vacant(vac) = self {
            vac.insert(default);
        }
    }

    /// Try to modify the entry using the given function.
    /// TODO: This might not be needed now that the high-level API unwraps the
    /// potential results.
    pub fn and_try_modify<F, E>(mut self, f: F) -> Result<Entry<K, V, StateEntryType>, E>
    where
        F: FnOnce(&mut V) -> Result<(), E>, {
        if let Entry::Occupied(ref mut occ) = self {
            occ.try_modify(f)?;
        }
        Ok(self)
    }

    /// Modify the entry using the given function.
    pub fn and_modify<F>(mut self, f: F) -> Entry<K, V, StateEntryType>
    where
        F: FnOnce(&mut V), {
        if let Entry::Occupied(ref mut occ) = self {
            occ.modify(f);
        }
        self
    }
}

impl<K, V, StateEntryType> Entry<K, V, StateEntryType>
where
    K: Serial,
    V: Serial + Default,
    StateEntryType: HasContractStateEntry,
{
    pub fn or_default(self) {
        if let Entry::Vacant(vac) = self {
            vac.insert(Default::default());
        }
    }
}

const NEXT_COLLECTION_PREFIX_KEY: u64 = 0;
#[cfg(test)]
const GENERIC_MAP_PREFIX: u64 = 1;
const INITIAL_NEXT_COLLECTION_PREFIX: u64 = 2;

impl HasFunctionsAPIWrapper for ContractStateLL {}

/// Provides higher level wrapper functions for the implementors around the unsafe host functions.
trait HasFunctionsAPIWrapper {

    #[inline(always)]
    fn create_entry(&mut self, key: &[u8]) -> Result<StateEntry, ContractStateError> {
        let key_start = key.as_ptr();
        let key_len = key.len() as u32; // Wasm usize == 32bit.
        let entry_id = unsafe { prims::state_create_entry(key_start, key_len) };
        match entry_id {
            u64::MAX => Err(ContractStateError::SubtreeLocked),
            _ => {
                Ok(StateEntry::open(entry_id))
            }
        }
    }

    #[inline(always)]
    fn get_parameter_size(&self, i: u32) -> Result<u32, ContractStateError> {
        let size = unsafe { prims::get_parameter_size(i) };
        if size == -1 {
            return Err(ContractStateError::ParameterNotFound);
        }
        Ok(size as u32)
    }

    #[inline(always)]
    fn get_parameter_section(&self, i: u32, buf: &mut [u8], offset: u32) -> Result<u32, ContractStateError> {
        let len = buf.len().try_into().map_err(|_| ContractStateError::SizeTooLarge)?;
        let res = unsafe {
            prims::get_parameter_section(i, buf.as_mut_ptr(), len, offset)
        };
        if res == -1 {
            return Err(ContractStateError::ParameterNotFound);
        }
        Ok(res as u32)
    }
}

impl HasContractStateLL for ContractStateLL
{
    type ContractStateData = ();
    type EntryType = StateEntry;
    type IterType = ContractStateIter;

    /// Open the contract state.
    fn open(_: Self::ContractStateData) -> Self { ContractStateLL }

    fn entry(&mut self, key: &[u8]) -> Result<EntryRaw<Self::EntryType>, ContractStateError> {
        let entry = match self.lookup(key) {
            Some(entry) => EntryRaw::Occupied(OccupiedEntryRaw::new(entry)),
            None => {
                let entry = self.create_entry(key)?;
                EntryRaw::Vacant(VacantEntryRaw::new(entry))
            }
        };
        Ok(entry)
    }

    fn lookup(&self, key: &[u8]) -> Option<Self::EntryType> {
        let key_start = key.as_ptr();
        let key_len = key.len() as u32; // Wasm usize == 32bit.
        let res = unsafe { prims::state_lookup_entry(key_start, key_len) };
        if res == u64::MAX {
            None
        } else {
            Some(StateEntry::open(res))
        }
    }

    /// Delete the entry. Returns true if the entry was occupied and false
    /// otherwise.
    fn delete_entry(&mut self, entry: Self::EntryType) -> Result<(), ContractStateError> {
        let res = unsafe { prims::state_delete_entry(entry.state_entry_id) };
        match res {
            u32::MAX => Err(ContractStateError::EntryNotFound),
            1 => Ok(()),
            _ => unreachable!(),
        }
    }

    /// If exact, delete the specific key, otherwise delete the subtree.
    /// Returns Ok(()) if entry/subtree was occupied Err(ContractStateError) otherwise
    /// (including if the subtree is locked or the entry not found).
    fn delete_prefix(&mut self, prefix: &[u8]) -> Result<(), ContractStateError> {
        let res = unsafe { prims::state_delete_prefix(prefix.as_ptr(), prefix.len() as u32) };
        match res {
            0 => Err(ContractStateError::SubtreeLocked),
            1 => Err(ContractStateError::EntryNotFound),
            2 => Ok(()),
            _ => unreachable!(),
        }
    }

    fn iterator(
        &self,
        prefix: &[u8],
    ) -> Result<ContractStateIter, ContractStateError> {
        let prefix_start = prefix.as_ptr();
        let prefix_len = prefix.len() as u32; // Wasm usize == 32bit.
        let iterator_id = unsafe { prims::state_iterate_prefix(prefix_start, prefix_len) };
        let all_ones = u64::MAX;
        if iterator_id == all_ones {
            return Err(ContractStateError::IteratorLimitForPrefixExceeded);
        }
        if iterator_id | 1u64.rotate_right(2) == all_ones {
            return Err(ContractStateError::EntryNotFound);
        }
        Ok(ContractStateIter {
            iterator_id,
        })
    }

    fn delete_iterator(&mut self, iter: ContractStateIter) -> Result<bool, ContractStateError> {
        let res = unsafe { prims::state_iterator_delete(iter.iterator_id) };
        match res {
            u32::MAX => Err(ContractStateError::IteratorNotFound),
            0 => Ok(false),
            1 => Ok(true),
            _ => unreachable!(),
        }
    }
}

impl ContractStateIter {

    fn state_iterator_next(&mut self) -> Result<Option<StateEntry>, ContractStateError> {
        let res = unsafe { prims::state_iterator_next(self.iterator_id) };
        match res {
            u64::MAX => Err(ContractStateError::IteratorNotFound),
            _ if res | 1u64.rotate_right(2) == u64::MAX => Ok(None),
            _ => {
                Ok(Some(StateEntry::open(res)))
            },
        }
    }
}

impl Iterator for ContractStateIter {
    type Item = StateEntry;

    fn next(&mut self) -> Option<Self::Item> {
        self.state_iterator_next().unwrap_abort()
    }
}

impl<K, V, S> StateMap<K, V, S>
where
    S: HasContractStateLL,
    K: Serialize,
    V: Serial + DeserialStateCtx<S>,
{
    pub fn open<P: Serial>(state_ll: Rc<RefCell<S>>, prefix: P) -> Self {
        Self {
            _marker_key: PhantomData,
            _marker_value: PhantomData,
            prefix: to_bytes(&prefix),
            state_ll,
        }
    }

    pub fn get(&self, key: K) -> Option<V> {
        let k = self.key_with_map_prefix(&key);
        self.state_ll.borrow().lookup(&k).map(|mut entry| {
            V::deserial_state_ctx(&self.state_ll, &mut entry).expect_report(
                "Deserial failed. State has been incorrectly altered using the low-level API.",
            )
        })
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let key_bytes = self.key_with_map_prefix(&key);
        let value_bytes = to_bytes(&value);
        match self.state_ll.borrow_mut().entry(&key_bytes).unwrap_abort() {
            EntryRaw::Vacant(vac) => {
                let _ = vac.insert(&value_bytes);
                None
            }
            EntryRaw::Occupied(mut occ) => {
                let old_value = V::deserial_state_ctx(&self.state_ll, occ.get_mut()).expect_report(
                    "Deserial failed. State has been incorrectly altered using the low-level API.",
                );
                occ.insert(&value_bytes);
                Some(old_value)
            }
        }
    }

    pub fn entry(&mut self, key: K) -> Entry<K, V, S::EntryType> {
        let key_bytes = self.key_with_map_prefix(&key);
        match self.state_ll.borrow_mut().entry(&key_bytes).unwrap_abort() {
            EntryRaw::Vacant(vac) => Entry::Vacant(VacantEntry::new(key, vac.state_entry)),
            EntryRaw::Occupied(mut occ) => {
                let value = V::deserial_state_ctx(&self.state_ll, occ.get_mut()).expect_report(
                    "Deserial failed. State has been incorrectly altered using the low-level API.",
                );
                Entry::Occupied(OccupiedEntry::new(key, value, occ.state_entry))
            }
        }
    }

    pub fn is_empty(&self) -> bool {
        let mut iterator = self.state_ll.borrow().iterator(&self.prefix).unwrap_abort();
        iterator.next().is_none()
    }

    pub fn iter(&self) -> Result<StateMapIter<K, V, S>, ContractStateError> {
        let state_iter = self.state_ll.borrow().iterator(&self.prefix)?;
        Ok(StateMapIter {
            state_iter,
            state_ll: Rc::clone(&self.state_ll),
            _marker_key: PhantomData,
            _marker_value: PhantomData,
        })
    }

    fn key_with_map_prefix(&self, key: &K) -> Vec<u8> {
        let mut key_with_prefix = self.prefix.clone();
        key_with_prefix.append(&mut to_bytes(key));
        key_with_prefix
    }
}

impl<K, V, S> Iterator for StateMapIter<K, V, S>
where
    K: Serialize,
    V: Serial + DeserialStateCtx<S>,
    S: HasContractStateLL,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.state_iter.next().and_then(|mut entry| {
            let key = entry.get_key();
            if let Ok(key) = key {
                let mut key_cursor = Cursor {
                    data:   key,
                    offset: 8, // Items in a map always start with the set prefix which is 8 bytes.
                };
                let k = K::deserial(&mut key_cursor).expect_report(
                    "Deserializing key failed. State has been incorrectly altered using the low-level \
                     API.",
                );
                let v = V::deserial_state_ctx(&self.state_ll, &mut entry).expect_report(
                    "Deserializing value failed. State has been incorrectly altered using the \
                     low-level API.",
                );
                Some((k, v))
            } else {
                None
            }
        })
    }
}

impl<K, V, S> Serial for StateMap<K, V, S>
where
    K: Serialize,
    V: Serial + DeserialStateCtx<S>,
    S: HasContractStateLL,
{
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        serial_vector_no_length(&self.prefix, out)
    }
}

impl<T, S> StateSet<T, S>
where
    T: Serial + DeserialStateCtx<S>,
    S: HasContractStateLL,
{
    pub(crate) fn open<P: Serial>(state_ll: Rc<RefCell<S>>, prefix: P) -> Self {
        Self {
            _marker: PhantomData,
            prefix: to_bytes(&prefix),
            state_ll,
        }
    }

    /// Adds a value to the set.
    /// If the set did not have this value, `true` is returned. Otherwise,
    /// `false`.
    pub fn insert(&mut self, value: T) -> bool {
        let key_bytes = self.key_with_set_prefix(&value);
        match self.state_ll.borrow_mut().entry(&key_bytes).unwrap_abort() {
            EntryRaw::Vacant(vac) => {
                let _ = vac.insert(&[]);
                true
            }
            EntryRaw::Occupied(_) => false,
        }
    }

    pub fn contains(&self, value: &T) -> bool {
        let key_bytes = self.key_with_set_prefix(value);
        self.state_ll.borrow().lookup(&key_bytes).is_some()
    }

    /// Removes a value from the set. Returns whether the value was present in
    /// the set.
    pub fn remove(&mut self, value: &T) -> bool {
        let key_bytes = self.key_with_set_prefix(value);
        let entry_opt = match self.state_ll.borrow_mut().entry(&key_bytes).unwrap_abort() {
            EntryRaw::Vacant(_) => None,
            EntryRaw::Occupied(occ) => Some(occ.get()),
        };
        if let Some(entry) = entry_opt {
            self.state_ll.borrow_mut().delete_entry(entry).unwrap_abort();
            true
        } else {
            false
        }
    }

    fn key_with_set_prefix(&self, key: &T) -> Vec<u8> {
        let mut key_with_prefix = self.prefix.clone();
        key_with_prefix.append(&mut to_bytes(key));
        key_with_prefix
    }

    pub fn iter(&self) -> Result<StateSetIter<T, S>, ContractStateError> {
        let state_iter = self.state_ll.borrow().iterator(&self.prefix)?;
        let iter = StateSetIter {
            state_iter,
            state_ll: Rc::clone(&self.state_ll),
            _marker: PhantomData,
        };
        Ok(iter)
    }
}

impl<T, S> Persistable<S> for T
where
    T: Serial + DeserialStateCtx<S>,
    S: HasContractStateLL,
{
    fn store(self, prefix: &[u8], state_ll: Rc<RefCell<S>>) {
        match state_ll.borrow_mut().entry(prefix).unwrap_abort() {
            EntryRaw::Vacant(vac) => {
                let _ = vac.insert(&to_bytes(&self));
            }
            EntryRaw::Occupied(mut occ) => occ.insert(&to_bytes(&self)),
        }
    }

    fn load(prefix: &[u8], state_ll: Rc<RefCell<S>>) -> ParseResult<Self> {
        match state_ll.borrow().lookup(prefix) {
            Some(mut entry) => Self::deserial_state_ctx(&state_ll, &mut entry),
            None => Err(ParseError::default()),
        }
    }
}

impl<T, S> StateBox<T, S>
where
    T: Serial + DeserialStateCtx<S>,
    S: HasContractStateLL + std::fmt::Debug,
{
    /// Inserts the value in the state and returns Self.
    pub(crate) fn new<P: Serial>(value: T, state_ll: Rc<RefCell<S>>, prefix: P) -> Self {
        let prefix_bytes = to_bytes(&prefix);
        let value_bytes = to_bytes(&value);

        // Insert the value into state.
        match state_ll.borrow_mut().entry(&prefix_bytes).unwrap_abort() {
            EntryRaw::Vacant(vac) => {
                let _ = vac.insert(&value_bytes);
            }
            EntryRaw::Occupied(_) => fail!("Internal error. Allocator gave out occupied prefix."),
        };

        Self {
            _marker: PhantomData,
            prefix: prefix_bytes,
            state_ll,
        }
    }

    /// Get a copy of the value.
    // StateBox does not hold the actual value, so it we cannot give out a
    // reference. to it. This design choice allows users to create arbitrary
    // nested data structures, such as linked lists. Similar to what is possible
    // with `Box`.
    pub fn get_copy(&self) -> T {
        match self.state_ll.borrow_mut().entry(&self.prefix).unwrap_abort() {
            EntryRaw::Vacant(_) => {
                fail!(
                    "Get failed: Entry is vacant. State has been incorrectly altered using the \
                     low-level API."
                )
            }
            EntryRaw::Occupied(mut occ) => T::deserial_state_ctx(&self.state_ll, occ.get_mut())
                .expect_report(
                    "Deserial failed. State has been incorrectly altered using the low-level API.",
                ),
        }
    }

    /// Set the value. Overwrites the existing one.
    pub fn set(&mut self, new_val: T) {
        match self.state_ll.borrow_mut().entry(&self.prefix).unwrap_abort() {
            // Technically, we do not need to fail in this case, we can just insert, but it should
            // /never/ happen.
            EntryRaw::Vacant(_) => {
                fail!(
                    "Set failed: Entry is vacant. State has been incorrectly altered using the \
                     low-level API."
                )
            }
            EntryRaw::Occupied(mut occ) => occ.insert(&to_bytes(&new_val)),
        }
    }

    /// Update the existing value with the given function.
    pub fn update<F>(&mut self, f: F)
    where
        F: FnOnce(&mut T), {
        match self.state_ll.borrow_mut().entry(&self.prefix).unwrap_abort() {
            EntryRaw::Vacant(_) => {
                fail!(
                    "Update failed: Entry is vacant. State has been incorrectly altered using the \
                     low-level API."
                )
            }
            EntryRaw::Occupied(mut occ) => {
                let mut value = T::deserial_state_ctx(&self.state_ll, occ.get_mut()).expect_report(
                    "Update failed: could not deserialize. State has been incorrectly altered \
                     using the low-level API.",
                );
                // Mutate the value (perhaps only in memory, depends on the type).
                f(&mut value);
                // Store the value. TODO: If `T` is a StateBox/Set/Map, then it is only
                // necessary to insert if the whole item has been replaced via the assignment
                // operator.
                occ.insert(&to_bytes(&value));
            }
        }
    }
}

impl<T, S> Serial for StateBox<T, S>
where
    T: Serial + DeserialStateCtx<S>,
    S: HasContractStateLL + std::fmt::Debug,
{
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        serial_vector_no_length(&self.prefix, out)
    }
}

impl<T, S> Serial for StateSet<T, S>
where
    T: Serial + DeserialStateCtx<S>,
    S: HasContractStateLL,
{
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        serial_vector_no_length(&self.prefix, out)
    }
}

impl<T, S> Iterator for StateSetIter<T, S>
where
    T: Serial + DeserialStateCtx<S>,
    S: HasContractStateLL,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.state_iter.next().and_then(|entry| {
            let key = entry.get_key();
            if let Ok(key) = key {
                let mut key_cursor = Cursor {
                    data:   key,
                    offset: 8, // Items in a set always start with the set prefix which is 8 bytes.
                };
                let res = T::deserial_state_ctx(&self.state_ll, &mut key_cursor).expect_report(
                    "Deserial failed. State has been incorrectly altered using the low-level API.",
                );
                Some(res)
            } else {
                None
            }
        })
    }
}

/// # Trait implementations for Parameter
impl Read for ExternParameter {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
        let num_read = self.get_parameter_section(0, buf, self.current_position).unwrap_abort();
        self.current_position += num_read as u32; // parameter 0 always exists, so this is safe.
        Ok(num_read as usize)
    }
}

impl HasParameter for ExternParameter {
    #[inline(always)]
    // parameter 0 always exists so this is correct
    fn size(&self) -> u32 {
        self.get_parameter_size(0).unwrap_abort()
    }
}

impl HasFunctionsAPIWrapper for ExternParameter {}

/// The read implementation uses host functions to read chunks of return value
/// on demand.
impl Read for CallResponse {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
        let num_read = self.get_parameter_section(self.i.into(), buf, self.current_position).map_err(|_| ParseError::default())?;
        self.current_position += num_read as u32;
        Ok(num_read as usize)
    }
}

impl HasFunctionsAPIWrapper for CallResponse {}

/// CallResponse can only be constured in this crate. As a result whenever it is
/// constructed it will point to a valid parameter, which means that
/// `get_parameter_size` will always return a non-negative value.
impl HasCallResponse for CallResponse {
    fn size(&self) -> u32 { self.get_parameter_size(self.i.get()).unwrap_abort() }
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
fn parse_call_response_code(code: u64) -> CallContractResult<CallResponse> {
    if code & !0xffff_ff00_0000_0000 == 0 {
        // this means success
        let rv = (code >> 40) as u32;
        let tag = 0x80_0000u32;
        if tag & rv != 0 {
            Ok((true, NonZeroU32::new(rv & !tag).map(CallResponse::new)))
        } else {
            Ok((false, NonZeroU32::new(rv).map(CallResponse::new)))
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
                            return_value: CallResponse::new(unsafe {
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
    let response =
        unsafe { invoke(INVOKE_TRANSFER_TAG, data.as_ptr(), (ACCOUNT_ADDRESS_SIZE + 8) as u32) };
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

impl<StateLL> Allocator<StateLL>
where
    StateLL: HasContractStateLL + std::fmt::Debug,
{
    pub fn open(state_ll: Rc<RefCell<StateLL>>) -> Self {
        Self {
            state_ll,
        }
    }

    pub fn new_map<K: Serialize, V: Serial + DeserialStateCtx<StateLL>>(
        &mut self,
    ) -> StateMap<K, V, StateLL> {
        let prefix = self.get_and_update_item_prefix();
        StateMap::open(Rc::clone(&self.state_ll), prefix)
    }

    pub fn new_set<T: Serial + DeserialStateCtx<StateLL>>(&mut self) -> StateSet<T, StateLL> {
        let prefix = self.get_and_update_item_prefix();
        StateSet::open(Rc::clone(&self.state_ll), prefix)
    }

    pub fn new_box<T: Serial + DeserialStateCtx<StateLL>>(
        &mut self,
        value: T,
    ) -> StateBox<T, StateLL> {
        let prefix = self.get_and_update_item_prefix();
        StateBox::new(value, Rc::clone(&self.state_ll), prefix)
    }

    fn get_and_update_item_prefix(&self) -> u64 {
        // Get the next prefix or insert and use the initial one.
        let entry_key = to_bytes(&NEXT_COLLECTION_PREFIX_KEY);
        let default_prefix = to_bytes(&INITIAL_NEXT_COLLECTION_PREFIX);
        let mut next_collection_prefix_entry =
            self.state_ll.borrow_mut().entry(&entry_key).unwrap_abort().or_insert(&default_prefix);

        // Get the next collection prefix
        let collection_prefix = next_collection_prefix_entry
            .read_u64()
            .expect_report("next_collection_prefix is not a valid u64.");

        // Rewind state entry position. Cannot fail.
        next_collection_prefix_entry.seek(SeekFrom::Start(0)).unwrap_abort();

        // Increment the collection prefix
        next_collection_prefix_entry.write_u64(collection_prefix + 1).unwrap_abort(); // Writing to state cannot fail.

        collection_prefix
    }
}

#[cfg(test)]
/// Some helper methods that are used for internal tests.
impl<StateLL> Allocator<StateLL>
where
    StateLL: HasContractStateLL + std::fmt::Debug,
{
    /// Some(Err(_)) means that something exists in the state with that key, but
    /// it isn't of type `V`.
    pub(crate) fn get<K: Serial, V: DeserialStateCtx<StateLL>>(
        &self,
        key: K,
    ) -> Option<ParseResult<V>> {
        let key_with_map_prefix = Self::prepend_generic_map_key(key);

        self.state_ll
            .borrow_mut()
            .lookup(&key_with_map_prefix)
            .map(|mut entry| V::deserial_state_ctx(&self.state_ll, &mut entry))
    }

    pub(crate) fn insert<K: Serial, V: Serial>(&mut self, key: K, value: V) {
        let key_with_map_prefix = Self::prepend_generic_map_key(key);
        let value_bytes = to_bytes(&value);
        match self.state_ll.borrow_mut().entry(&key_with_map_prefix).unwrap_abort() {
            EntryRaw::Vacant(vac) => {
                let _ = vac.insert(&value_bytes);
            }
            EntryRaw::Occupied(mut occ) => occ.insert(&value_bytes),
        }
    }

    fn prepend_generic_map_key<K: Serial>(key: K) -> Vec<u8> {
        let mut key_with_map_prefix = to_bytes(&GENERIC_MAP_PREFIX);
        key_with_map_prefix.append(&mut to_bytes(&key));
        key_with_map_prefix
    }
}

impl<State> HasHost<State> for ExternHost<State>
where
    State: Persistable<ContractStateLL>,
{
    type ContractStateLLType = ContractStateLL;
    type ReturnValueType = CallResponse;

    fn invoke_transfer(&mut self, receiver: &AccountAddress, amount: Amount) -> TransferResult {
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
        let response = unsafe { invoke(INVOKE_CALL_TAG, data.as_ptr(), len as u32) };
        let (state_modified, res) = parse_call_response_code(response)?;
        if state_modified {
            // The state of the contract changed as a result of the call.
            // So we refresh it.
            if let Ok(new_state) = State::load(&[], Rc::clone(&self.allocator.state_ll)) {
                self.state = new_state;
            } else {
                crate::trap() // FIXME: With new state this needs to be revised.
            }
        }
        Ok((state_modified, res))
    }

    fn state(&mut self) -> &mut State { &mut self.state }

    #[inline(always)]
    fn self_balance(&self) -> Amount {
        Amount::from_micro_ccd(unsafe { get_receive_self_balance() })
    }

    fn allocator(&mut self) -> &mut Allocator<Self::ContractStateLLType> { &mut self.allocator }
}

impl HasHost<ContractStateLL> for ExternLowLevelHost {
    type ContractStateLLType = ContractStateLL;
    type ReturnValueType = CallResponse;

    fn invoke_transfer(&mut self, receiver: &AccountAddress, amount: Amount) -> TransferResult {
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
        let response = unsafe { invoke(INVOKE_CALL_TAG, data.as_ptr(), len as u32) };
        // TODO: Figure out if we need to do anything special here.
        // Old entries are invalidated by the host, so no cursors should need to be
        // reset.
        parse_call_response_code(response)
    }

    #[inline(always)]
    fn state(&mut self) -> &mut ContractStateLL { &mut self.state }

    #[inline(always)]
    fn self_balance(&self) -> Amount {
        Amount::from_micro_ccd(unsafe { get_receive_self_balance() })
    }

    fn allocator(&mut self) -> &mut Allocator<Self::ContractStateLLType> { &mut self.allocator }
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
    fn unwrap_abort(self) -> Self::Unwrap {
        match self {
            Some(x) => x,
            None => crate::trap(),
        }
    }
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
impl<D: Deserial, S: HasContractStateLL> DeserialStateCtx<S> for D {
    fn deserial_state_ctx<R: Read>(_state: &Rc<RefCell<S>>, source: &mut R) -> ParseResult<Self> {
        Self::deserial(source)
    }
}

impl<K, V, S> DeserialStateCtx<S> for StateMap<K, V, S>
where
    S: HasContractStateLL,
    K: Serialize,
    V: Serial + DeserialStateCtx<S>,
{
    fn deserial_state_ctx<R: Read>(state: &Rc<RefCell<S>>, source: &mut R) -> ParseResult<Self> {
        source.read_u64().map(|map_prefix| StateMap::open(Rc::clone(state), map_prefix))
    }
}

impl<T, S> DeserialStateCtx<S> for StateSet<T, S>
where
    S: HasContractStateLL,
    T: Serial + DeserialStateCtx<S>,
{
    fn deserial_state_ctx<R: Read>(state: &Rc<RefCell<S>>, source: &mut R) -> ParseResult<Self> {
        source.read_u64().map(|set_prefix| StateSet::open(Rc::clone(state), set_prefix))
    }
}

impl<T, S> DeserialStateCtx<S> for StateBox<T, S>
where
    S: HasContractStateLL + std::fmt::Debug,
    T: Serial + DeserialStateCtx<S>,
{
    fn deserial_state_ctx<R: Read>(state: &Rc<RefCell<S>>, source: &mut R) -> ParseResult<Self> {
        let mut prefix = [0u8; 8];
        source.read_exact(&mut prefix).map(|_| {
            StateBox {
                state_ll: Rc::clone(state),
                prefix:   prefix.to_vec(),
                _marker:  PhantomData,
            }
        })
    }
}
