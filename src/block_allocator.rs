//! Basic block allocator implementation
//!
//! (c) 2015 Rick Richardson <rick.richardson@gmail.com>
//!
//!
//!

use mmap::{MemoryMap, MapOption};
use std::mem;
use std::u32;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Allocator
/// Provides fixed-sized buffers from a pre-allocated arena specified at creation
/// Current limitations: Max number of buffers it can produce is u32::MAX - 1
/// Multiple allocators may be in use at any time, but their buffers may not be
/// used interchangibly :)
///
/// Note : This allocator will produce blocks in sizes of powers of two, but guarantees
/// that it will provide a buffer at least as large as what you specify, it also keeps
/// some basic accounting information in the head of each buffer, this means that if you
/// specify a block_size of 256, it will create buffers of size 512 in order to accomodate
/// your basic requirement of 256 usable bytes.
///
/// # Example
/// ```
/// use block_allocator::Allocator;
///
/// //reserve 100 usable blocks of size 500 bytes
/// let myalloc = Allocator::new(500, 100).unwrap();
/// let ptr = myalloc.alloc().unwrap();
///
/// //do stuff
///
/// myalloc.free(ptr);
/// ```
///
pub struct Allocator {
    head : AtomicUsize,
    block_size : u32,
    region : MemoryMap,
    _num_blocks : u32,
}

impl Allocator {


    pub fn new(block_size: u32, num_blocks: u32) -> Result<Allocator, String> {
        // for now this can only work on 64 bit platforms
        // it would be nice to have atomics other than register sizes
        assert!(mem::size_of::<isize>() >= mem::size_of::<u64>());
        assert!(num_blocks < u32::MAX); //we can support u32::MAX - 1 entries

        let adjsz = next_pow_of_2(block_size + mem::size_of::<u32>() as u32);
        let rgn = match MemoryMap::new(adjsz as usize * num_blocks as usize,
                                        &[MapOption::MapReadable, MapOption::MapWritable]) {
            Ok(r) => r,
            Err(e) => return Err(format!("{}", e))
        };

        unsafe {
            let p = rgn.data();

            for i in 0 .. num_blocks {
                let cell = p.offset(adjsz as isize * i as isize) as *mut u32;
                *cell = i;
            }
            let cell = p.offset( (num_blocks - 1) as isize * adjsz as isize) as *mut u32;
            *cell = u32::MAX; //sentinel value indicating end of list
        }
        Ok(Allocator {
            head : AtomicUsize::new(0),
            block_size : adjsz,
            _num_blocks : num_blocks,
            region : rgn
        })

    }

    pub fn alloc(&self) -> Option<*mut u8> {

        let mut hd = self.head.load(Ordering::Relaxed);
        let mut offset = hd >> 32; //top 32 bits are the offset to the start of the free list
        if offset as u32 == u32::MAX {
            return None;
        }

        loop {
            offset = self.get_next_offset((hd >> 32) as isize) as usize;
            let counter = hd & 0xffffffff;
            let newhd = (offset << 32) | (counter + 1);
            let oldhead = hd;
            hd = self.head.compare_and_swap(hd, newhd, Ordering::SeqCst);
            if hd == oldhead { return Some(self.get_cell((hd >> 32) as isize)) }
        }
    }

    pub fn free(&self, item : *mut u8) { unsafe {

        let cell = item.offset(-1 * (mem::size_of::<u32>() as isize));
        let newoffset = *(cell as *mut u32);
        let mut hd = self.head.load(Ordering::Relaxed);

        loop {
            let counter = hd & 0xffffffff;
            let newhd = ((newoffset as usize) << 32) | (counter + 1);
            *(cell as *mut u32) = (hd >> 32) as u32;
            let oldhead = hd;
            hd = self.head.compare_and_swap(hd, newhd, Ordering::SeqCst);
            if hd == oldhead { break; }
        }
    }}

    #[inline(always)]
    fn get_next_offset(&self, index : isize) -> u32 { unsafe {
        let cell = self.region.data().offset(index * self.block_size as isize) as *const u32;
        *cell
    }}

    #[inline(always)]
    fn get_cell(&self, index : isize) -> *mut u8 { unsafe {
        self.region.data().offset((index * self.block_size as isize) + mem::size_of::<u32>() as isize)
    }}
}


#[inline]
fn next_pow_of_2(mut n : u32) -> u32
{
    n -= 1;
    n |= n >> 1;
    n |= n >> 2;
    n |= n >> 4;
    n |= n >> 8;
    n |= n >> 16;
    n += 1;
    n
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let myalloc = Allocator::new(200, 100).unwrap();
        let ptr = myalloc.alloc().unwrap();
        myalloc.free(ptr);
    }

    #[test]
    fn max_cap() {
        let myalloc = Allocator::new(200, 10).unwrap();
        for _ in 0..10 {
            let ptr = myalloc.alloc().unwrap();
        }
        let ptr = myalloc.alloc();
        assert!(ptr.is_none());
    }
}

