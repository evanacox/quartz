# Quartz IR Reference

## Structure

## Memory Model

Bytes in QIR are 8-bit. 

## Types

### `bool`: Booleans

`bool` models the pure idea of a boolean, with two states: `true` and `false`. 

They are not 'integers' as they are in LLVM and some other IRs, although they can be
converted into integers and back easily with the `btoi` and `itob` instructions.

All `bool`s are exactly byte sized and byte aligned, i.e. they are equivalent to an `i8`
in size, alignment, and other storage expectations.

### `iN`: Integers

`iN` models the concept of two's complement integers, and acts the same way that
integers do on the vast majority of computers. Unlike integers in most languages, they
are sign-less. Note that this does not mean *unsigned*, instead, sign is determined by the
instruction. This more closely models the hardware, and allows more granular control over
the behavior / guarantees that are desired. 

Integers are in the form `iN`, such that \\(N \in \\{8, 16, 32, 64\\} \\). Support for
wider integers (i.e. `i128`) or arbitrary-width integers (i.e. `i37`) may come in the future.

The size of an integer is exactly as many bytes as is required to store \\( N \\) bits,
and the alignment of an integer is exactly the same as its size. 

### `fN`: Floats

`fN` model floating-point numbers that follow the IEEE-754 standard. Currently, only two
are supported:

* `f32`: IEEE single-precision, i.e. `binary32`
* `f64`: IEEE double-precision, i.e. `binary64`

In the future, others may be supported (e.g. `f128` for IEEE quads).

The size of a float is exactly as many bytes as is required to store \\( N \\) bits,
and the alignment of a float is exactly the same as its size.

### `ptr`: Pointers

`ptr` models the idea of a pointer, and nothing else. Unlike many high-level languages, pointers
are untyped.

### `[T; N]`: Arrays

`[T; N]` models contiguous blocks of storage, approximately equivalent to arrays in C. Arrays are considered to 
be aggregate types, and thus aggregate operations can be used on them. Each array index is considered
an independent element.

They take up exactly `sizeof(T) * N` bytes of storage, with alignment that is equal to `alignof(T)`. 
Note that this means that arrays that satisfy one of the following conditions are zero-sized:

* `N == 0`
* `sizeof(T) == 0`

```
%Empty = [i8; 0]
%Empty2 = [Empty; 64]
%Ints = [i64; 512]
%Matrix3D = [[[i64; 16]; 16]; 16]
```

### `{ Ts... }`: Structures

`{ T... }` models a `struct` in C, and conform to the same ABI as C structures would for a given target. They
are aggregate types, and thus each member of the structure is one element and can be accessed using
aggregate instructions. 

Structures are padded, and their size is thus determined by the order of each element, and the size/align
of each element. Note that structures satisfying one of the following conditions are zero-sized:

* No elements
* Every element is zero-sized

```
%Vec = { ptr, i64, i64 }
%Empty = { }
%Nested = { { i32, i32 }, f64, [i8; 64] }
```

## Instructions

### Aggregate Access

#### `extract` - Get Element

#### `insert` - Set Element

#### `ptrinto` - Get Pointer To Element

### Conversions

#### `btoi` - Bool to Int

#### `ftoi` - Float to Int

#### `itob` - Int to Bool

#### `itof` - 