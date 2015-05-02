
# Block Allocator

[![crates.io](https://img.shields.io/crates/v/block_allocator.svg)](https://crates.io/crates/block_allocator/)

[![Build Status](https://travis-ci.org/rrichardson/block_alloc.svg?branch=master)](https://travis-ci.org/rrichardson/block_alloc)

This is a basic, thread-safe, fixed sized arena which allocates re-usable blocks
of your specified sized. Re-usable meaning this isn't a basic arena which is
use-once, blocks are free-able and re-allocatable. The intended use case for this
allocator are multithreaded services which frequently allocate and deallocate uniform blocks of
memory, such as web servers or videogames.  It can run forever without any loss of performance
due to fragmentation.

Presently it will allocate mutable u8 slices which are bound to the lifetime of the allocator itself, or raw *mut u8
pointers.

Its current limitations are that it can only work on 64 bit architectures, and it can only manage UINT32_MAX - 1 blocks because it uses a pair of 32 bit numbers
for offset management.  After some [refactoring to atomics](https://github.com/rust-lang/rust/issues/24564) some time in
    the future, both limitations will be lifted.

It is currently fairly fast, running concurrently, it can alloc then free in 28ns per iteration, regardless of the size
of the buffer or arena.

To use it, simply construct a new allocator, specifying the size of the block and the number of blocks you would like
the allocator to manage (note that this number is not growable at runtime, so choose wisely)

```rust
    // create blocks of size 200 with a max of 100
    let myalloc = Allocator::new(200, 100).unwrap();
```

then you can alloc and free to your heart`s content

```rust
    let buf : &mut [u8] = myalloc.alloc();
    myalloc.free(buf);

    or

    let ptr : *mut u8 = myalloc.alloc_raw();
    myalloc.free_raw(ptr);
```

## Iobuf support

This implements the Iobuf::Allocator trait, so it can be used to construct [Iobufs](https://github.com/cgaebel/iobuf)
which are very efficient reference counted, thread-safe buffers.


