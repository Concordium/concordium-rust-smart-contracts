use crate::{
    collections::{BTreeMap, BTreeSet},
    convert::{self, TryFrom, TryInto},
    hash::Hash,
    mem, num, prims,
    prims::*,
    traits::*,
    types::*,
    vec::Vec,
    String,
};
pub(crate) use concordium_contracts_common::*;
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

impl StateEntry {
    pub(crate) fn open(state_entry_id: StateEntryId) -> Self {
        Self {
            state_entry_id,
            current_position: 0,
        }
    }
}

impl HasContractStateEntry for StateEntry {
    type StateEntryData = ();

    fn open(_: Self::StateEntryData, entry_id: StateEntryId) -> Self { Self::open(entry_id) }

    fn state_entry_id(&self) -> StateEntryId { self.state_entry_id }

    #[inline(always)]
    fn size(&self) -> u32 { unsafe { entry_state_size(self.state_entry_id) } }

    fn truncate(&mut self, new_size: u32) {
        let cur_size = self.size();
        if cur_size > new_size {
            unsafe { resize_entry_state(self.state_entry_id, new_size) };
        }
        if new_size < self.current_position {
            self.current_position = new_size
        }
    }

    fn reserve(&mut self, len: u32) -> bool {
        let cur_size = unsafe { entry_state_size(self.state_entry_id) };
        if cur_size < len {
            let res = unsafe { resize_entry_state(self.state_entry_id, len) };
            res == 1
        } else {
            true
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

impl Read for StateEntry {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
        let len: u32 = {
            match buf.len().try_into() {
                Ok(v) => v,
                _ => return Err(ParseError::default()),
            }
        };
        let num_read = unsafe {
            load_entry_state(self.state_entry_id, buf.as_mut_ptr(), len, self.current_position)
        };
        self.current_position += num_read;
        Ok(num_read as usize)
    }

    /// Read a `u32` in little-endian format. This is optimized to not
    /// initialize a dummy value before calling an external function.
    fn read_u64(&mut self) -> ParseResult<u64> {
        let mut bytes: MaybeUninit<[u8; 8]> = MaybeUninit::uninit();
        let num_read = unsafe {
            load_entry_state(
                self.state_entry_id,
                bytes.as_mut_ptr() as *mut u8,
                8,
                self.current_position,
            )
        };
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
            load_entry_state(
                self.state_entry_id,
                bytes.as_mut_ptr() as *mut u8,
                4,
                self.current_position,
            )
        };
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
            load_entry_state(
                self.state_entry_id,
                bytes.as_mut_ptr() as *mut u8,
                1,
                self.current_position,
            )
        };
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
            write_entry_state(self.state_entry_id, buf.as_ptr(), len, self.current_position)
        };
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
            state_entry_id: state_entry.state_entry_id(),
            state_entry,
        }
    }

    pub fn state_entry_id(&self) -> &StateEntryId { &self.state_entry_id }

    pub fn into_entry_id(self) -> StateEntryId { self.state_entry_id }

    pub fn insert(mut self, value: &[u8]) -> StateEntryType {
        self.state_entry.write_all(value).unwrap_abort(); // Writing to state cannot fail.
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
            state_entry_id: state_entry.state_entry_id(),
            state_entry,
        }
    }

    pub fn state_entry_id(&self) -> &StateEntryId { &self.state_entry_id }

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
    pub fn state_entry_id(&self) -> &StateEntryId {
        match self {
            EntryRaw::Vacant(vac) => vac.state_entry_id(),
            EntryRaw::Occupied(occ) => occ.state_entry_id(),
        }
    }

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
    pub fn modify<F, E>(&mut self, f: F) -> Result<(), E>
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

    // TODO: Add non-result version for non-nested maps.
    pub fn and_modify<F, E>(mut self, f: F) -> Result<Entry<K, V, StateEntryType>, E>
    where
        F: FnOnce(&mut V) -> Result<(), E>, {
        if let Entry::Occupied(ref mut occ) = self {
            occ.modify(f)?;
        }
        Ok(self)
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
const GENERIC_MAP_PREFIX: u64 = 1;
const INITIAL_NEXT_COLLECTION_PREFIX: u64 = 2;

/// Keeps the following state:
/// 0 => next_collection_prefix: u64
/// 1/<key> => values stored and retrieved with insert/get
/// <2..u64::MAX>/ => collections with a prefix from new_map or new_set.
///
/// The slashes (/) are only added conceptually for readability.
impl HasContractStateHL for ContractStateHL {
    type ContractStateData = ();
    type ContractStateLLType = ContractStateLL;

    fn open(_: Self::ContractStateData) -> Self {
        Self {
            state_ll: Rc::new(RefCell::new(ContractStateLL::open(()))),
        }
    }

    fn new_map<K: Serialize, V: Serial + DeserialStateCtx<Self::ContractStateLLType>>(
        &mut self,
    ) -> StateMap<K, V, Self::ContractStateLLType> {
        // Get the next prefix or insert and use the initial one.
        let entry_key = to_bytes(&NEXT_COLLECTION_PREFIX_KEY);
        let default_prefix = to_bytes(&INITIAL_NEXT_COLLECTION_PREFIX);
        let mut next_collection_prefix_entry =
            self.state_ll.borrow_mut().entry(&entry_key).or_insert(&default_prefix);

        // Get the next collection prefix
        let map_prefix = next_collection_prefix_entry
            .read_u64()
            .expect_report("next_collection_prefix is not a valid u64.");

        // Rewind state entry position. Cannot fail.
        next_collection_prefix_entry.seek(SeekFrom::Start(0)).unwrap_abort();

        // Increment the collection prefix
        next_collection_prefix_entry.write_u64(map_prefix + 1).unwrap_abort(); // Writing to state cannot fail.

        StateMap::open(Rc::clone(&self.state_ll), map_prefix)
    }

    /// Some(Err(_)) means that something exists in the state with that key, but
    /// it isn't of type `V`.
    fn get<K: Serial, V: DeserialStateCtx<Self::ContractStateLLType>>(
        &self,
        key: K,
    ) -> Option<ParseResult<V>> {
        let key_with_map_prefix = prepend_generic_map_key(key);

        self.state_ll
            .borrow_mut()
            .lookup(&key_with_map_prefix)
            .and_then(|mut entry| Some(V::deserial_state_ctx(&self.state_ll, &mut entry)))
    }

    fn insert<K: Serial, V: Serial>(&mut self, key: K, value: V) {
        let key_with_map_prefix = prepend_generic_map_key(key);
        let value_bytes = to_bytes(&value);
        match self.state_ll.borrow_mut().entry(&key_with_map_prefix) {
            EntryRaw::Vacant(vac) => {
                let _ = vac.insert(&value_bytes);
            }
            EntryRaw::Occupied(mut occ) => occ.insert(&value_bytes),
        }
    }
}

fn prepend_generic_map_key<K: Serial>(key: K) -> Vec<u8> {
    let mut key_with_map_prefix = to_bytes(&GENERIC_MAP_PREFIX);
    key_with_map_prefix.append(&mut to_bytes(&key));
    key_with_map_prefix
}

impl HasContractStateLL for ContractStateLL {
    type ContractStateData = ();
    type EntryType = StateEntry;
    type IterType = ContractStateIter<Self::EntryType>;

    /// Open the contract state.
    fn open(_: Self::ContractStateData) -> Self { ContractStateLL }

    fn entry(&self, key: &[u8]) -> EntryRaw<Self::EntryType> {
        let key_start = key.as_ptr();
        let key_len = key.len() as u32; // Wasm usize == 32bit.
        let res = unsafe { lookup(key_start, key_len) };

        if res == -1 {
            let entry_id = unsafe { create(key_start, key_len) };
            EntryRaw::Vacant(VacantEntryRaw::new(StateEntry::open(entry_id)))
        } else {
            let entry_id = res as u32;
            EntryRaw::Occupied(OccupiedEntryRaw::new(StateEntry::open(entry_id)))
        }
    }

    fn lookup(&self, key: &[u8]) -> Option<Self::EntryType> {
        let key_start = key.as_ptr();
        let key_len = key.len() as u32; // Wasm usize == 32bit.
        let entry_id_option = unsafe { lookup(key_start, key_len) };
        if entry_id_option < 0 {
            None
        } else {
            Some(StateEntry::open(entry_id_option as u32))
        }
    }

    /// Delete the entry. Returns true if the entry was occupied and false
    /// otherwise.
    fn delete_entry(&mut self, entry_id: StateEntryId) -> bool {
        unsafe { delete_entry(entry_id) == 1 }
    }

    /// If exact, delete the specific key, otherwise delete the subtree.
    /// Returns true if entry/subtree was occupied and false otherwise
    /// (including if the key was too long or empty).
    fn delete_prefix(&mut self, prefix: &[u8], exact: bool) -> bool {
        let len = prefix.len() as u32; // Safe because usize is 32bit in WASM.
        let prefix_ptr = prefix.as_ptr();
        unsafe { delete_prefix(prefix_ptr, len, exact as u32) == 1 }
    }

    fn iterator(&self, prefix: &[u8]) -> Self::IterType {
        let prefix_start = prefix.as_ptr();
        let prefix_len = prefix.len() as u32; // Wasm usize == 32bit.
        let iterator_id = unsafe { iterator(prefix_start, prefix_len) };
        ContractStateIter {
            iterator_id,
        }
    }
}

impl Iterator for ContractStateIter {
    type Item = StateEntry;

    fn next(&mut self) -> Option<Self::Item> {
        let res = unsafe { next(self.iterator_id) };
        if res < 0 {
            None
        } else {
            Some(StateEntry::open(res as u32))
        }
    }
}

impl<K, V, S> HasStateMap<K, V> for StateMap<K, V, S>
where
    S: HasContractStateLL,
    K: Serialize,
    V: Serial + DeserialStateCtx<S>,
{
    type ContractStateLLType = S;

    fn open<P: Serial>(state_ll: Rc<RefCell<Self::ContractStateLLType>>, prefix: P) -> Self {
        Self {
            phantom_k: PhantomData,
            phantom_v: PhantomData,
            prefix: to_bytes(&prefix),
            state_ll,
        }
    }

    fn get(&self, key: K) -> Option<ParseResult<V>> {
        let k = self.key_with_map_prefix(&key);
        self.state_ll
            .borrow()
            .lookup(&k)
            .and_then(|mut entry| Some(V::deserial_state_ctx(&self.state_ll, &mut entry)))
    }

    fn insert(&mut self, key: K, value: V) -> Option<ParseResult<V>> {
        let key_bytes = self.key_with_map_prefix(&key);
        let value_bytes = to_bytes(&value);
        match self.state_ll.borrow_mut().entry(&key_bytes) {
            EntryRaw::Vacant(vac) => {
                let _ = vac.insert(&value_bytes);
                None
            }
            EntryRaw::Occupied(mut occ) => {
                let old_value = V::deserial_state_ctx(&self.state_ll, occ.get_mut());
                occ.insert(&value_bytes);
                Some(old_value)
            }
        }
    }

    fn entry(
        &mut self,
        key: K,
    ) -> ParseResult<Entry<K, V, <Self::ContractStateLLType as HasContractStateLL>::EntryType>>
    {
        let key_bytes = self.key_with_map_prefix(&key);
        match self.state_ll.borrow_mut().entry(&key_bytes) {
            EntryRaw::Vacant(vac) => Ok(Entry::Vacant(VacantEntry::new(key, vac.state_entry))),
            EntryRaw::Occupied(mut occ) => {
                let value = V::deserial_state_ctx(&self.state_ll, occ.get_mut())?;
                Ok(Entry::Occupied(OccupiedEntry::new(key, value, occ.state_entry)))
            }
        }
    }
}

impl<K, V, S> StateMap<K, V, S>
where
    K: Serialize,
    V: Serial,
    S: HasContractStateLL,
{
    pub(crate) fn key_with_map_prefix(&self, key: &K) -> Vec<u8> {
        let mut key_with_prefix = self.prefix.clone();
        key_with_prefix.append(&mut to_bytes(key));
        key_with_prefix
    }
}

impl<K, V, S> Serial for StateMap<K, V, S>
where
    K: Serialize,
    V: Serial + DeserialStateCtx<S>,
    S: HasContractStateLL,
{
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> { self.prefix.serial(out) }
}

/// # Trait implementations for Parameter
impl Read for Parameter {
    fn read(&mut self, buf: &mut [u8]) -> ParseResult<usize> {
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
    type ParamType = Parameter;
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
        Parameter {
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
    fn send_raw(
        ca: &ContractAddress,
        receive_name: ReceiveName,
        amount: Amount,
        parameter: &[u8],
    ) -> Self {
        let receive_bytes = receive_name.get_chain_name().as_bytes();
        let res = unsafe {
            prims::send(
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

/// Wrapper for
/// [HasActions::send_raw](./trait.HasActions.html#tymethod.send_raw), which
/// automatically serializes the parameter. Note that if the parameter is
/// already a byte array or convertible to a byte array without allocations it
/// is preferrable to use [send_raw](./trait.HasActions.html#tymethod.send_raw).
/// It is more efficient and avoids memory allocations.
pub fn send<A: HasActions, P: Serial>(
    ca: &ContractAddress,
    receive_name: ReceiveName,
    amount: Amount,
    parameter: &P,
) -> A {
    let param_bytes = to_bytes(parameter);
    A::send_raw(ca, receive_name, amount, &param_bytes)
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
use std::{cell::RefCell, marker::PhantomData, rc::Rc};

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
        source.read_u64().and_then(|map_prefix| Ok(StateMap::open(Rc::clone(state), map_prefix)))
    }
}
