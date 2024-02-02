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
//!    field and resets the `next` pointer to `MIN_PTR_ADDR` if there are no
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
/// The minimum pointer address used. Address `0` cannot be used, as that
/// corresponds to a null pointer, which indicates errors.
const MIN_PTR_ADDR: usize = 1;

/// A number of WebAssembly memory pages.
#[derive(Eq, PartialEq, Copy, Clone)]
struct PageCount(usize);

impl PageCount {
    /// The size in bytes. I.e. `PageCount * PAGE_SIZE`.
    fn size_in_bytes(&self) -> usize { self.0 * PAGE_SIZE }
}

/// The number of pages returned from `memory_grow` to indicate out of memory.
const ERROR_PAGE_COUNT: PageCount = PageCount(usize::MAX);

/// This is an invalid implementation of [`Sync`].
/// The [`BumpAllocator`] cannot be safely used from multiple threads, but that
/// is OK since it won't be in Wasm. This [`Sync`] implementation is required
/// for defining it as the global allocator.
unsafe impl Sync for BumpAllocator {}

pub struct BumpAllocator {
    /// The pointer to the next memory to hand out.
    next:        UnsafeCell<usize>,
    /// The end of the heap. Cannot be known at compile time and thus the
    /// initial value is 0. It is updated on the first allocation.
    heap_end:    UnsafeCell<usize>,
    /// The number of active allocations. Used for resetting `next` to
    /// `MIN_PTR_ADDR` if there are no more active allocations.
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
    /// where it is called staticly. Since we cannot know the actual size of
    /// the heap, `heap_end` is initialized to `0` and updated on the first
    /// allocation.
    ///
    /// # Safety
    /// - Can only be used in single-threaded environments. The [`Sync`]
    ///   implementation is only invalid and is only there to support setting
    ///   this as the global allocator.
    pub const unsafe fn new() -> Self {
        Self {
            next:        UnsafeCell::new(MIN_PTR_ADDR),
            heap_end:    UnsafeCell::new(0),
            allocations: UnsafeCell::new(0),
            // Must be set to the same initial address as `next`.
            last_alloc:  UnsafeCell::new(MIN_PTR_ADDR),
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

        // On the first allocation, the heap end is 0, as we cannot know how
        // many pages the contract is configured to start with. So we get the
        // actual size and update the value.
        if *heap_end == 0 {
            let actual_size = self.size().size_in_bytes();
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
            let pages_to_request = PageCount(div_ceil(space_needed, PAGE_SIZE));
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
        // Reset next and last allocation if everything has been deallocated.
        if *allocations == 0 {
            *next = MIN_PTR_ADDR;
            *last_alloc = MIN_PTR_ADDR;
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

/// Calculates the quotient of `lhs / rhs`, while rounding up to the nearest
/// integer.
///
/// Since `rhs` is used as the denominator in the division it **cannot be 0**.
/// If it is, this method panics.
///
/// ```
/// assert_eq!(div_ceil(8, 3), 3); // Round 2.66.. up to 3.
/// assert_eq!(div_ceil(10, 10), 1); // No rounding needed.
/// assert_eq!(div_ceil(10, 20), 1); // Round 0.5 up to 1.
/// ```
const fn div_ceil(lhs: usize, rhs: usize) -> usize {
    let d = lhs / rhs;
    let r = lhs % rhs;
    let rounding = (r > 0) as usize;
    d + rounding
}
