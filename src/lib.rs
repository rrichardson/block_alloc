//! A thread-safe, reusable allocator of fixed-size blocks
//!
//! (c) 2015 Rick Richardson <rick.richardson@gmail.com>
//!
//! Provides fixed size, buffers out of a pre-allocated arena.
//!
//! # Limitations
//! * Max number of buffers that can be provided is `u32::MAX` - 1
//! * Max size of a buffer is `u32::MAX`
//! * Currently only works on 64 bit architectures
//! * (all of these due to a present limitation in Atomic types)
//!
//!
#![feature(test)]

#![feature(integer_atomics)]

extern crate memmap;
extern crate test;
extern crate core;

mod block_allocator;

pub use block_allocator::Allocator;
