//! This module contains a "bump allocator", which is a simple type of allocator
//! designed for a small code footprint and to suit most smart contracts.
//!
//! A bump allocator has a `next` pointer which points to the next address in
//! the heap to hand out. The `next` pointer is incremented by the size of
//! each allocation. This is sufficient for the allocator to work, but it also
//! leaks memory. However, for short-lived programs such as smart contracts,
//! memory leaks are perfectly fine and even preferable since the need for
//! cleanup and advanced allocation schemes is removed.
//!
//! The bump allocator here has two extra features:
//!  - It keeps track of the number of active allocations in the `allocations`
//!    field and resets the `next` pointer to `heap_start` if there are no
//!    active allocations, thus allowing the reuse of memory.
//!  - On deallocations it checks whether it is the very last memory block
//!    handed out that is deallocated. If it is, then it moves the `next`
//!    pointer back to the beginning of that block. Thus also allowing memory to
//!    be reused.
use core::{
    alloc::{GlobalAlloc, Layout},
    cell::UnsafeCell,
    ptr,
};

/// The byte size of Wasm pages.
const PAGE_SIZE: usize = 65536;

/// A number of WebAssembly memory pages.
#[derive(Eq, PartialEq, Copy, Clone)]
struct PageCount(usize);

impl PageCount {
    /// The size in bytes, i.e. `PageCount * PAGE_SIZE`.
    fn size_in_bytes(&self) -> usize { self.0 * PAGE_SIZE }
}

/// The number of pages returned from `memory_grow` to indicate out of memory.
const ERROR_PAGE_COUNT: PageCount = PageCount(usize::MAX);

extern "C" {
    /// A pointer to the `__heap_base` field defined in the Wasm files that
    /// specifies which memory address the heap starts at. Memory addresses
    /// prior to that are used for the data and the stack.
    ///
    /// To get the actual memory location as a `usize`, do the following:
    ///
    /// ```
    /// let heap_base = unsafe { &__heap_base as *const _ as usize }; 
    /// ```
    static __heap_base: u8;
}

/// This is an invalid implementation of [`Sync`].
/// The [`BumpAllocator`] cannot be safely used from multiple threads, but that
/// is OK since it won't be in Wasm. This [`Sync`] implementation is required
/// for defining it as the global allocator.
unsafe impl Sync for BumpAllocator {}

/// A bump allocator for Wasm.
///
/// See the module documentation for more details.
pub struct BumpAllocator {
    /// The pointer to the next memory to hand out.
    next:        UnsafeCell<usize>,
    /// The start of the heap.
    /// This value is used for resetting `next` if all memory chunks are
    /// deallocated and `allocations` thus becomes 0.
    /// The actual location of the heap cannot be known at compile time and
    /// the initial value is thus 0. It is set to `__heap_base` value on the
    /// first allocation.
    heap_start:  UnsafeCell<usize>,
    /// The end of the heap. Cannot be known at compile time and thus the
    /// initial value is 0. It is updated on the first allocation.
    heap_end:    UnsafeCell<usize>,
    /// The number of active allocations. Used for resetting `next` to
    /// `heap_start` if there are no more active allocations.
    allocations: UnsafeCell<usize>,
    /// Stores the last address given out, and allows for a small improvement
    /// over the always-increasing bump allocator. Namely that if an item
    /// `a` is allocated and deallocated without any allocations in between,
    /// then the memory of `a` is reused for the next allocation.
    last_alloc:  UnsafeCell<usize>,
}

impl BumpAllocator {
    /// Create a new [`BumpAllocator`].
    ///
    /// This must be a `const` method for it to be used as a global allocator,
    /// where it is called staticly. Since we cannot know the start and end
    /// locations of the heap on compile time, several values are initialized to
    /// a dummy value `0` and updated appropriately during the first allocation.
    ///
    /// # Safety
    /// - Can only be used in single-threaded environments. The [`Sync`]
    ///   implementation is only invalid and is only there to support setting
    ///   this as the global allocator.
    pub const unsafe fn new() -> Self {
        Self {
            // Initialized to the dummy value `0`.
            next:        UnsafeCell::new(0),
            // Initialized to the dummy value `0`.
            heap_start:  UnsafeCell::new(0),
            // Initialized to the dummy value `0`, which is checked during first initialization.
            heap_end:    UnsafeCell::new(0),
            allocations: UnsafeCell::new(0),
            // Initialized to the dummy value `0`.
            // Must be set to the same initial address as `next`.
            last_alloc:  UnsafeCell::new(0),
        }
    }

    /// Grow the memory by `delta` pages, each of size [PAGE_SIZE].
    ///
    /// If successful, it returns the previous number of memory pages.
    /// Otherwise, it returns [`ERROR_PAGE_COUNT`] to indicate out of memory.
    fn grow_memory(&self, delta: PageCount) -> PageCount {
        // The first argument refers to the index of memory to return the size of.
        // Currently, Wasm only supports a single slot of memory, so `0` must always be
        // used. Source: https://doc.rust-lang.org/beta/core/arch/wasm32/fn.memory_grow.html
        PageCount(core::arch::wasm32::memory_grow(0, delta.0))
    }

    /// Get the size of memory in terms of pages.
    ///
    /// The memory has three sections in the following order:
    ///
    ///  - The data section.
    ///  - The stack.
    ///  - The heap.
    ///
    /// To get the start location of the heap, use `__heap_base`.
    fn size(&self) -> PageCount {
        // The argument refers to the index of memory to return the size of.
        // Currently, Wasm only supports a single slot of memory, so `0` must always be
        // used. Source: https://doc.rust-lang.org/beta/core/arch/wasm32/fn.memory_size.html
        PageCount(core::arch::wasm32::memory_size(0))
    }
}

unsafe impl GlobalAlloc for BumpAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let heap_end = &mut *self.heap_end.get();
        let next = &mut *self.next.get();

        // On the first allocation, we need to replace the dummy values in the struct
        // with the actual memory addresses of the `heap_start` and `heap_end` as well
        // as the `next` and `last_alloc`.
        //
        // This is because the size of the data and stack sections (which are located
        // before the beginning of the heap) and the initial size of the heap
        // can be configured in the wasm.
        if *heap_end == 0 {
            // Get the base/start of the heap.
            let heap_base = unsafe { &__heap_base as *const _ as usize };
            // Get the actual size of the memory, which is also the end of the heap, as the
            // heap is the last section in the memory.
            let actual_size = self.size().size_in_bytes();
            // Replace all the dummy values.
            *next = heap_base;
            *self.heap_start.get() = heap_base;
            *self.last_alloc.get() = heap_base;
            *heap_end = actual_size;
        }

        // Align the address.
        let alloc_start = align_up(*next, layout.align());
        // Get the end of the allocation. This should always return `Some` as the
        // contract memory is limited to much below usize::MAX.
        let alloc_end = match alloc_start.checked_add(layout.size()) {
            Some(end) => end,
            None => return ptr::null_mut(),
        };

        // Check if we need to request more memory.
        if alloc_end > *heap_end {
            let space_needed = alloc_end - *heap_end;
            let pages_to_request = pages_to_request(space_needed);
            let previous_page_count = self.grow_memory(pages_to_request);
            // Check if we are out of memory.
            if previous_page_count == ERROR_PAGE_COUNT {
                return ptr::null_mut();
            }
            // Increase the heap size.
            *heap_end += pages_to_request.size_in_bytes();
        }

        // Increment allocations counter.
        *self.allocations.get() += 1;
        // Remember the last address handed out, so that we may move `next` backwards if
        // it is deallocated before a new allocation occurs.
        *self.last_alloc.get() = alloc_start;
        *next = alloc_end;
        alloc_start as *mut u8
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        let allocations = self.allocations.get();
        let last_alloc = self.last_alloc.get();
        let next = self.next.get();
        // Decrease the allocation counter.
        *allocations -= 1;
        if *allocations == 0 {
            // Reset next and last allocation so they point at the start of the heap if
            // everything has been deallocated.
            let heap_start = self.heap_start.get();
            *next = *heap_start;
            *last_alloc = *heap_start;
        } else if *last_alloc as *mut u8 == ptr {
            // Move next back to last alloc. This is a small optimization over the regular
            // bump allocator.
            *next = *last_alloc;
        }
    }
}

/// Align the given address, `addr`, upwards to alignment `align`.
///
/// Requires that `align` is a power of two, which it always is due to the
/// design of [`Layout`].
///
/// Uses a bitmask to align the addresses for efficiency.
/// For details, see: https://os.phil-opp.com/allocator-designs/#address-alignment
fn align_up(addr: usize, align: usize) -> usize { (addr + align - 1) & !(align - 1) }

/// Calculates the number of memory pages needed to allocate an additional
/// `space_needed` bytes.
///
/// ```
/// assert_eq!(pages_to_request(0), PageCount(0));
/// assert_eq!(pages_to_request(1), PageCount(1));
/// assert_eq!(pages_to_request(PAGE_SIZE - 1), PageCount(1));
/// assert_eq!(pages_to_request(PAGE_SIZE), PageCount(1));
/// assert_eq!(pages_to_request(PAGE_SIZE + 1), PageCount(2));
/// assert_eq!(pages_to_request(10 * PAGE_SIZE + 1), PageCount(11));
/// assert_eq!(pages_to_request(200 * PAGE_SIZE - 1), PageCount(200));
/// ```
const fn pages_to_request(space_needed: usize) -> PageCount {
    let d = space_needed / PAGE_SIZE;
    let r = space_needed % PAGE_SIZE;
    let rounding = (r > 0) as usize;
    PageCount(d + rounding)
}
