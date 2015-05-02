
use block_allocator::Allocator;
use iobuf::Allocator as IAllocator;
use core::nonzero::NonZero;
use std::ptr::null_mut;

impl<'a> IAllocator for Allocator<'a> {
    fn allocate(&self, _: usize, _: usize) -> *mut u8 {
        self.alloc_raw().unwrap_or(null_mut())
    }

    fn deallocate(&self, ptr: NonZero<*mut u8>, _: usize, _: usize) {
        self.free_raw(*ptr);
    }
}
