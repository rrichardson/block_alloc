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
use std::slice;
use std::marker::PhantomData;

/// Allocator
/// Provides fixed-sized buffers from a pre-allocated arena specified at creation
/// Current limitations: Max number of buffers it can produce is u32::MAX - 1
/// Multiple allocators may be in use at any time, but their buffers may not be
/// used interchangibly :)
///
/// Note : This allocator will only produce blocks in sizes of powers of two, but
/// the usable buffer space is going to be 4 bytes smaller than the requested size
/// so if you need the full power of 2 space, request the next power of 2
///
/// Implementation
/// This keeps track of the next available buffer in the slab using a Double CAS Treiber Stack
/// Since Rust atomics don't actually support a double CAS yet, I am simulating it by 
/// CAS'ing on a single 64 bit value that is actually a [u32; 2], where the lower bits
/// are the counter, and the higher order bits is the next offset
///
/// # Example
/// ```
/// use block_allocator::Allocator;
///
/// //reserve 100 usable blocks of size 512 (-4) bytes
/// let myalloc = Allocator::new(512, 100).unwrap();
/// let ptr = myalloc.alloc_raw().unwrap();
///
/// //do stuff
///
/// myalloc.free_raw(ptr);
/// ```
///
pub struct Allocator<'a> {
    head : AtomicUsize,
    block_size : u32,
    region : MemoryMap,
    _num_blocks : u32,
    _phantom: PhantomData<&'a u8>
}

impl<'a> Allocator<'a> {


    pub fn new(block_size: u32, num_blocks: u32) -> Result<Allocator<'a>, String> {
        // for now this can only work on 64 bit platforms
        // it would be nice to have atomics other than register sizes
        assert!(mem::size_of::<isize>() >= mem::size_of::<u64>());
        assert!(num_blocks < u32::MAX); //we can support u32::MAX - 1 entries
        assert!(block_size != 0);
        assert!(num_blocks != 0);
        assert!(block_size.is_power_of_two());
        let rgn = match MemoryMap::new(block_size as usize * num_blocks as usize,
                                        &[MapOption::MapReadable, MapOption::MapWritable]) {
            Ok(r) => r,
            Err(e) => return Err(format!("{}", e))
        };

        unsafe {
            let p = rgn.data();

            for i in 0 .. num_blocks {
                let cell = p.offset(block_size as isize * i as isize) as *mut u32;
                *cell = i + 1;
            }
            let cell = p.offset( (num_blocks - 1) as isize * block_size as isize) as *mut u32;
            *cell = u32::MAX; //sentinel value indicating end of list
        }
        Ok(Allocator {
            head : AtomicUsize::new(0),
            block_size : block_size,
            _num_blocks : num_blocks,
            region : rgn,
            _phantom: PhantomData
        })

    }

    pub fn alloc(&self) -> Option<&'a mut [u8]> { unsafe {
        self.alloc_raw().map(|a|
            slice::from_raw_parts_mut(a, self.block_size as usize)
        )
    }}

    pub fn free(&self, buf: &'a mut [u8]) {
        self.free_raw(buf.as_mut_ptr());
    }

    pub fn alloc_raw(&self) -> Option<*mut u8> {

        let mut hd = self.head.load(Ordering::Relaxed);
        let hd_ary : &[u32 ;2] = unsafe { mem::transmute(&hd) };
        let mut offset = hd_ary[0]; //top 32 bits are the offset to the start of the free list
        //println!("alloc - Loaded head {} | {}", hd_ary[0], hd_ary[1]);
        if offset == u32::MAX {
            return None;
        }

        loop {
            
            offset = self.get_next_offset(hd_ary[0]);
            let counter = hd_ary[1];
            let newhd_ary = [offset, counter.wrapping_add(1)];
            //println!("alloc - Setting newhd to {} | {}",  offset, counter.wrapping_add(1));
            let oldhead = hd;
            hd = self.head.compare_and_swap(hd, unsafe { mem::transmute(newhd_ary) }, Ordering::SeqCst);
            if hd == oldhead { 
                return Some(self.get_cell(hd_ary[0]))
            }
            if hd_ary[0] == u32::MAX {
                return None;
            }
        }
    }

    pub fn free_raw(&self, item : *mut u8) { unsafe {

        let cell = item.offset(-1 * (mem::size_of::<u32>() as isize));
        //println!("free  - cell ptr {:p} and value {}", cell, *(cell as *mut u32));

        let cell_addr : usize = mem::transmute(cell);
        let start_addr : usize = mem::transmute(self.region.data());
        let newoffset = (cell_addr - start_addr) as u32 / self.block_size;
        let mut hd = self.head.load(Ordering::Relaxed);
        let hd_ary : &[u32; 2] = mem::transmute(&hd);
        //println!("free  - Loaded head {} | {}", hd_ary[0], hd_ary[1]);

        loop {
            let counter = hd_ary[1];
            //println!("free  - Setting newhd to {} | {}",  newoffset, counter.wrapping_add(1));
            let newhd_ary = [newoffset,  counter.wrapping_add(1)];
            
            let oldhead = hd;
            let oldhd_ary : &[u32; 2] = mem::transmute(&oldhead);
            //println!("free  - Setting cell to {}", oldhd_ary[0]);
            *(cell as *mut u32) = oldhd_ary[0];

            hd = self.head.compare_and_swap(hd, mem::transmute(newhd_ary), Ordering::SeqCst);
            if hd == oldhead { 
                break; 
            }
        }
    }}

    #[inline(always)]
    fn get_next_offset(&self, index : u32) -> u32 { unsafe {
        let cell = self.region.data().offset(index as isize * self.block_size as isize) as *const u32;
        *cell
    }}

    #[inline(always)]
    fn get_cell(&self, index : u32) -> *mut u8 { unsafe {
        self.region.data().offset((index as isize * self.block_size as isize) + mem::size_of::<u32>() as isize)
    }}
}

unsafe impl<'a> Send for Allocator<'a> {}
unsafe impl<'a> Sync for Allocator<'a> {}

#[inline]
fn _next_pow_of_2(mut n : u32) -> u32
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
    use std::thread;
    use std::sync::Arc;
    use test::Bencher;
    use std::mem;
    #[test]
    fn basic() {
        let myalloc = Allocator::new(256, 100).unwrap();
        let ptr = myalloc.alloc_raw().unwrap();
        myalloc.free_raw(ptr);
    }

    #[test]
    fn max_cap() {
        let myalloc = Allocator::new(256, 10).unwrap();
        for _ in 0..10 {
            let _ = myalloc.alloc_raw().unwrap();
        }
        let ptr = myalloc.alloc_raw();
        assert!(ptr.is_none());
    }

    #[test]
    fn sizing() { unsafe {
        let myalloc = Allocator::new(256, 10).unwrap();
        let a = myalloc.alloc_raw().unwrap();
        let b = myalloc.alloc_raw().unwrap();
        let a1 : usize = mem::transmute(a);
        let b1 : usize = mem::transmute(b);
        let diff = b1 - a1;
        println!("block_size: {}", diff);
        assert!(diff >= 256);
    } }

    #[test]
    fn up_down() {
        let myalloc = Allocator::new(256, 10).unwrap();
        let ptrs : Vec<*mut u8> = (0..10).map(|_| myalloc.alloc_raw().unwrap()).collect();

        let ptr = myalloc.alloc_raw();
        assert!(ptr.is_none());

        for p in ptrs.iter() {
            myalloc.free_raw(*p);
        }

        let ptrs : Vec<*mut u8> = (0..10).map(|_| myalloc.alloc_raw().unwrap()).collect();

        let ptr = myalloc.alloc_raw();
        assert!(ptr.is_none());

        for p in ptrs.iter() {
            myalloc.free_raw(*p);
        }

        let ptr = myalloc.alloc_raw();
        assert!(ptr.is_some());
    }
    #[test]
    fn concurrency() {
        let myalloc = Arc::new(Allocator::new(256, 1000).unwrap());

        let threads : Vec<thread::JoinHandle<()>> = (0..10).map(|_| {
            let ma = myalloc.clone();
            thread::spawn(move || {
                for _ in (0 .. 100000) {
                    let p = ma.alloc_raw().unwrap();
                    ma.free_raw(p);
                    let p = ma.alloc_raw().unwrap();
                    ma.free_raw(p);
                    let p = ma.alloc_raw().unwrap();
                    ma.free_raw(p);
                    let p = ma.alloc_raw().unwrap();
                    ma.free_raw(p);
                }
        }) }).collect();

        for t in threads {
            t.join().unwrap();
        }

        //we should be back to 0 at this point, so this should succeed
        let _ : Vec<*mut u8> = (0..1000).map(|_| myalloc.alloc_raw().unwrap()).collect();
        // then this should fail
        let ptr = myalloc.alloc_raw();
        assert!(ptr.is_none());
    }

    #[bench]
    fn speedtest(b: &mut Bencher) {
        let myalloc = Arc::new(Allocator::new(256, 1000).unwrap());
        b.iter(||{
            let p = myalloc.alloc_raw().unwrap();
            myalloc.free_raw(p);
        });
    }
}

