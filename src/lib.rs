//! A thread-safe, reusable allocator of fixed-size blocks
//! (c) 2015 Rick Richardson <rick.richardson@gmail.com>
//!
//! Provides fixed size, buffers out of a pre-allocated arena.
//!
//! # Limitations
//! * Max number of buffers that can be provided is u32::MAX - 1
//! * Max size of a buffer is u32::MAX
//! * Currently only works on 64 bit word systems (due to a present limitation in Atomic types)
//!
//! #example
//! ```
//! use block_allocator::Allocator;
//!
//! let myalloc = Allocator::new(500, 1000);
//! let ptr = myalloc.alloc();
//!
//! //do stuff
//!
//! myalloc.free(ptr);
//! ```
//!
extern crate mmap;

pub mod block_allocator;


#[test]
fn it_works() {
}
