//! Basic block allocator implementation
//!
//! (c) 2015, 2016 Rick Richardson <rick.richardson@gmail.com>
//!
//!
//!


use memmap::{Mmap, Protection};
use std::mem;
use std::u32;
use std::sync::atomic::{AtomicUsize, AtomicU32, Ordering};
use std::slice;
use std::error::Error;
use std::fmt::{self, Display};
use std::marker::PhantomData;
use std::cell::UnsafeCell;

const PAGE_SIZE : u32 = (1 << 12);

/// Allocator
/// Provides fixed-sized buffers from a pre-allocated arena specified at creation
/// Current limitations: Max number of buffers it can produce is `u32::MAX` - 1
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
/// let buf = myalloc.alloc().unwrap();
///
/// //do stuff
///
/// myalloc.free(buf);
/// ```
///
pub struct Allocator<'a> {
head : AtomicUsize,
     block_size : u32,
     freelist : UnsafeCell<&'static [AtomicU32]>,
     data : UnsafeCell<*mut u8>,
     _region : Mmap,
     num_blocks : u32,
     _phantom: PhantomData<&'a u8>
}

impl<'a> Allocator<'a> {

    /// Constructs a new Block Allocator
    pub fn new(block_size: u32, num_blocks: u32) -> Result<Allocator<'a>, AllocError> {
        // for now this can only work on 64 bit platforms
        // it would be nice to have atomics other than register sizes
        assert!(mem::size_of::<isize>() >= mem::size_of::<u64>());
        assert!(num_blocks < u32::MAX); //we can support u32::MAX - 1 entries
        assert!(block_size >= mem::size_of::<u32>() as u32);
        assert!(num_blocks > 0);
        assert!(block_size.is_power_of_two());

        let table_size = num_blocks * mem::size_of::<u32>() as u32;
        let table_size = PAGE_SIZE + (table_size & !(PAGE_SIZE - 1)); 

        let mut rgn = match Mmap::anonymous(table_size as usize + (block_size as usize * num_blocks as usize), Protection::ReadWrite) {
            Ok(r) => r,
            Err(e) => return Err(AllocError::MemoryMapFail(format!("{}", e)))
        };

        let table : &[AtomicU32] = unsafe {
            slice::from_raw_parts_mut(mem::transmute::<_,_>(rgn.mut_ptr()), num_blocks as usize)
        };

        //initialize the "linked list" within the table
        for i in 0 .. (num_blocks as usize - 1) {
            table[i].store(i as u32 + 1, Ordering::Relaxed);
        }
        table[num_blocks as usize - 1].store(u32::MAX, Ordering::Relaxed); //sentinel value indicating end of list

        let data = unsafe { rgn.mut_ptr().offset(table_size as isize) };

        Ok(Allocator {
            head : AtomicUsize::new(0),
            block_size : block_size,
            num_blocks : num_blocks,
            _region : rgn,
            data : UnsafeCell::new(data),
            freelist : UnsafeCell::new(table),
            _phantom: PhantomData
        })
    }

    /// Acquire the next free buffer from the allocator's slab
    pub fn alloc(&self) -> Result<&'a mut [u8], AllocError> { unsafe {
        self.alloc_raw().map(|a|
            slice::from_raw_parts_mut(a, self.block_size as usize)
        )
    }}

    /// Free the buffer back into the allocator's slab
    pub fn free(&self, buf: &'a mut [u8]) -> Result<(), AllocError> {
        if buf.len() as u32 != self.block_size {
          return Err(AllocError::BadArgument("Slice != allocator's block_size".to_string()));
        }
        unsafe {self.free_raw(buf.as_mut_ptr()) }
    }

    /// Acquire the next buffer as a raw `std::u8` pointer from the allocator's slab
    pub unsafe fn alloc_raw(&self) -> Result<*mut u8, AllocError> {

        let mut hd = self.head.load(Ordering::Acquire);
        let hd_ary : &[u32 ;2] = mem::transmute(&hd);
        let mut offset = hd_ary[0]; //top 32 bits are the offset to the start of the free list
        //println!("alloc - Loaded head {} | {}", hd_ary[0], hd_ary[1]);
        if offset == u32::MAX {
            return Err(AllocError::NoMemory);
        }

        loop {

            offset = self.get_next_offset(hd_ary[0]);
            let counter = hd_ary[1];
            let newhd_ary = [offset, counter.wrapping_add(1)];
            //println!("alloc - Setting newhd to {} | {}",  offset, counter.wrapping_add(1));
            let oldhead = hd;
            hd = self.head.compare_and_swap(hd, mem::transmute(newhd_ary), Ordering::SeqCst);
            if hd == oldhead { 
                return Ok(self.get_cell(hd_ary[0]))
            }
            if hd_ary[0] == u32::MAX {
                return Err(AllocError::NoMemory);
            }
        }
    }

    /// Free a raw (previously alloc'd pointer) back into the allocator's slab
    pub unsafe fn free_raw(&self, item : *mut u8) -> Result<(), AllocError> {
        // this gets the offset from the pointer that is being freed, then
        // uses that in the freelist table.  The offset becomes the new head
        // and the previous head becomes the 'next' offset
        if item.is_null() {
            return Err(AllocError::BadArgument("Null".to_string()));
        }

        let cell_addr : usize = mem::transmute(item);
        let start_addr : usize = mem::transmute(*self.data.get());
        let end_addr : usize = mem::transmute((*self.data.get()).offset((self.block_size * self.num_blocks) as isize));

        if (cell_addr < start_addr) || (cell_addr > end_addr) {
            return Err(AllocError::BadArgument("Out of bounds".to_string()));
        }

        //ensure that the ptr falls on the alignment of the block_size
        if (cell_addr & (self.block_size as usize - 1)) != 0 {
            return Err(AllocError::BadArgument("Misaligned value".to_string()));
        }

        let newoffset = (cell_addr - start_addr) as u32 / self.block_size;
        let mut hd = self.head.load(Ordering::Acquire);
        let hd_ary : &[u32; 2] = mem::transmute(&hd);
        //println!("free  - Loaded head {} | {}", hd_ary[0], hd_ary[1]);

        loop {
            let counter = hd_ary[1];
            //println!("free  - Setting newhd to {} | {}",  newoffset, counter.wrapping_add(1));
            let newhd_ary = [newoffset,  counter.wrapping_add(1)];

            let oldhead = hd;
            let oldhd_ary : &[u32; 2] = mem::transmute(&oldhead);
            
            (*self.freelist.get())[newoffset as usize].store(oldhd_ary[0], Ordering::Relaxed);

            hd = self.head.compare_and_swap(hd, mem::transmute(newhd_ary), Ordering::SeqCst);
            if hd == oldhead { 
                break; 
            }
        }

        Ok(())
    }

    #[inline(always)]
    fn get_next_offset(&self, index : u32) -> u32 { unsafe {
        (*self.freelist.get())[index as usize].load(Ordering::Relaxed)
    } }

    #[inline(always)]
    fn get_cell(&self, index : u32) -> *mut u8 { unsafe {
        (*self.data.get()).offset(index as isize * self.block_size as isize)
    }}

    #[inline(always)]
    pub fn get_block_size(&self) -> u32 {
        self.block_size
    }
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

#[derive(Debug)]
pub enum AllocError {
    BadArgument(String),
    MemoryMapFail(String), 
    NoMemory,
}

impl Display for AllocError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AllocError::BadArgument(ref s) => write!(f, "Bad Argument : {}", s),
            AllocError::MemoryMapFail(ref s) => write!(f, "Memory Map Failure : {}", s),
            AllocError::NoMemory => write!(f, "Out of memory")
        }
    }
}

impl Error for AllocError {
    fn description(&self) -> &str {
        match *self {
            AllocError::BadArgument(_) => "Bad Argument",
            AllocError::MemoryMapFail(_) => "Memory Map Failure",
            AllocError::NoMemory => "Out of memory"
        }
    }

    fn cause(&self) -> Option<&Error> { 
        None 
    }
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
        let ptr = myalloc.alloc().unwrap();
        myalloc.free(ptr).unwrap();
    }

#[test]
    fn max_cap() {
        let myalloc = Allocator::new(256, 10).unwrap();
        for _ in 0..10 {
            let _ = myalloc.alloc().unwrap();
        }
        let ptr = myalloc.alloc();
        assert!(ptr.is_err());
    }

#[test]
    fn sizing() { unsafe {
        let myalloc = Allocator::new(256, 10).unwrap();
        let a = myalloc.alloc().unwrap();
        let b = myalloc.alloc().unwrap();
        let a1 : usize = mem::transmute(a.as_ptr());
        let b1 : usize = mem::transmute(b.as_ptr());
        let diff = b1 - a1;
        println!("block_size: {}", diff);
        assert!(diff >= 256);
    } }

#[test]
    fn up_down() {
        let myalloc = Allocator::new(256, 10).unwrap();
        let mut ptrs : Vec<&mut [u8]> = (0..10).map(|_| myalloc.alloc().unwrap()).collect();

        let ptr = myalloc.alloc();
        assert!(ptr.is_err());

        for p in ptrs.iter_mut() {
            myalloc.free(*p).unwrap();
        }

        let mut ptrs : Vec<&mut [u8]> = (0..10).map(|_| myalloc.alloc().unwrap()).collect();

        let ptr = myalloc.alloc();
        assert!(ptr.is_err());

        for p in ptrs.iter_mut() {
            myalloc.free(*p).unwrap();
        }

        let ptr = myalloc.alloc();
        assert!(ptr.is_ok());
    }
#[test]
    fn concurrency() {
        let myalloc = Arc::new(Allocator::new(256, 1000).unwrap());

        let threads : Vec<thread::JoinHandle<()>> = (0..10).map(|_| {
            let ma = myalloc.clone();
            thread::spawn(move || {
                for _ in 0 .. 100000 {
                    let p = ma.alloc().unwrap();
                    ma.free(p).unwrap();
                    let p = ma.alloc().unwrap();
                    ma.free(p).unwrap();
                    let p = ma.alloc().unwrap();
                    ma.free(p).unwrap();
                    let p = ma.alloc().unwrap();
                    ma.free(p).unwrap();
                    }
        })}).collect();

        for t in threads {
            t.join().unwrap();
        }

        //we should be back to 0 at this point, so this should succeed
        let _ : Vec<&mut [u8]> = (0..1000).map(|_| myalloc.alloc().unwrap()).collect();
        // then this should fail
        let ptr = myalloc.alloc();
        assert!(ptr.is_err());
    }



#[test]
    fn basic_raw() { unsafe {
        let myalloc = Allocator::new(256, 100).unwrap();
        let ptr = myalloc.alloc_raw().unwrap();
        myalloc.free_raw(ptr).unwrap();
    } }

#[test]
    fn max_cap_raw() { unsafe {
        let myalloc = Allocator::new(256, 10).unwrap();
        for _ in 0..10 {
            let _ = myalloc.alloc_raw().unwrap();
        }
        let ptr = myalloc.alloc_raw();
        assert!(ptr.is_err());
    } }

#[test]
    fn sizing_raw() { unsafe {
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
    fn up_down_raw() { unsafe {
        let myalloc = Allocator::new(256, 10).unwrap();
        let ptrs : Vec<*mut u8> = (0..10).map(|_| myalloc.alloc_raw().unwrap()).collect();

        let ptr = myalloc.alloc_raw();
        assert!(ptr.is_err());

        for p in ptrs.iter() {
            myalloc.free_raw(*p).unwrap();
        }

        let ptrs : Vec<*mut u8> = (0..10).map(|_| myalloc.alloc_raw().unwrap()).collect();

        let ptr = myalloc.alloc_raw();
        assert!(ptr.is_err());

        for p in ptrs.iter() {
            myalloc.free_raw(*p).unwrap();
        }

        let ptr = myalloc.alloc_raw();
        assert!(ptr.is_ok());
    } }
#[test]
    fn concurrency_raw() {  unsafe {
        let myalloc = Arc::new(Allocator::new(256, 1000).unwrap());

        let threads : Vec<thread::JoinHandle<()>> = (0..10).map(|_| {
            let ma = myalloc.clone();
            thread::spawn(move || {
                for _ in 0 .. 100000 {
                    let p = ma.alloc_raw().unwrap();
                    ma.free_raw(p).unwrap();
                    let p = ma.alloc_raw().unwrap();
                    ma.free_raw(p).unwrap();
                    let p = ma.alloc_raw().unwrap();
                    ma.free_raw(p).unwrap();
                    let p = ma.alloc_raw().unwrap();
                    ma.free_raw(p).unwrap();
                    }
        })}).collect();

        for t in threads {
            t.join().unwrap();
        }

        //we should be back to 0 at this point, so this should succeed
        let _ : Vec<*mut u8> = (0..1000).map(|_| myalloc.alloc_raw().unwrap()).collect();
        // then this should fail
        let ptr = myalloc.alloc_raw();
        assert!(ptr.is_err());
    } }

#[bench]
    fn speedtest(b: &mut Bencher) {
        let myalloc = Arc::new(Allocator::new(256, 1000).unwrap());
        b.iter(||{
                let p = myalloc.alloc().unwrap();
                myalloc.free(p).unwrap();
                });
    }

#[bench]
    fn speedtest_big(b: &mut Bencher) {
        let myalloc = Arc::new(Allocator::new(1 << 14, 1000).unwrap());
        b.iter(||{
                let p = myalloc.alloc().unwrap();
                myalloc.free(p).unwrap();
                });
    }

#[bench]
    fn concurrent_speed(b: &mut Bencher) {
        let myalloc = Arc::new(Allocator::new(256, 1000).unwrap());
        b.iter(||{
            let threads : Vec<thread::JoinHandle<()>> = (0..20).map(|_| {
                let ma = myalloc.clone();
                thread::spawn(move || {
                    for _ in 0 .. 1000 {
                        let p = ma.alloc().unwrap();
                        ma.free(p).unwrap();
                        let p = ma.alloc().unwrap();
                        ma.free(p).unwrap();
                        let p = ma.alloc().unwrap();
                        ma.free(p).unwrap();
                        let p = ma.alloc().unwrap();
                        ma.free(p).unwrap();
                        }
            })}).collect();

            for t in threads {
                t.join().unwrap();
            }
       });
   }
}

