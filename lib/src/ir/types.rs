//======---------------------------------------------------------------======//
// Copyright (c) 2022 Evan Cox <evanacox00@gmail.com>.                       //
//                                                                           //
// Licensed under the Apache License, Version 2.0 (the "License");           //
// you may not use this file except in compliance with the License.          //
// You may obtain a copy of the License at                                   //
//                                                                           //
//     http://www.apache.org/licenses/LICENSE-2.0                            //
//                                                                           //
// Unless required by applicable law or agreed to in writing, software       //
// distributed under the License is distributed on an "AS IS" BASIS,         //
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  //
// See the License for the specific language governing permissions and       //
// limitations under the License.                                            //
//======---------------------------------------------------------------======//

//! # Quartz IR Types
//!
//! Types are modeled in the IR as value types (ish), unlike in other IRs
//! that choose to make each type unique for memory reasons. This simplifies
//! the design and makes multithreading easier, but it may change in the future.
//!
//! The main workhorse of the type system is [`IRType`]. The other types are used
//! as type-safe data storage for the various properties of each variant of type.
//!
//! ```
//! use quartz::ir::*;
//!
//! let t1 = Type::bool();
//! let t2 = Type::int(32);
//!
//! match t2 {
//!     Type::Int(data) => {
//!         assert_eq!(data.width(), 32);
//!     }
//!     _ => {}
//! }
//!
//! assert_ne!(t1, t2);
//! ```

use contracts::{contract_trait, ensures, requires};
use smallvec::SmallVec;
use static_assertions::const_assert_eq;
use std::fmt::{Debug, Formatter, Result};
use std::hash::Hash;
use std::mem;
use strum_macros::IntoStaticStr;

/// Models the layout requirements of a given type.
///
/// This simplifies using both [`Type::size_req`] and [`Type::align_req`]
/// due to the uncheckable guarantees they provide.
///
/// # Example
/// ```
/// # use quartz::ir::*;
/// let ty = Type::i16();
/// let layout = ty.layout().unwrap();
///
/// assert_eq!(layout.size(), 2);
/// assert_eq!(layout.align(), 2);
/// ```
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct TypeLayout {
    size: u64,
    align: u64,
}

impl TypeLayout {
    #[inline]
    #[requires(size >= align, "size must always exceed or equal alignment")]
    fn new(size: u64, align: u64) -> Self {
        Self { size, align }
    }

    /// Gets the size of the type, in bytes.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::*;
    /// let ty = Type::i32();
    /// let layout = ty.layout().unwrap();
    ///
    /// assert_eq!(layout.size(), 4);
    /// ```
    #[inline]
    pub fn size(self) -> u64 {
        self.size
    }

    /// Gets the alignment requirement of the type, in bytes.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::*;
    /// let ty = Type::i32();
    /// let layout = ty.layout().unwrap();
    ///
    /// assert_eq!(layout.align(), 4);
    /// ```
    #[inline]
    pub fn align(self) -> u64 {
        self.align
    }
}

/// Models the accessible operations on any given type.
///
/// Note that *any* type includes odd types, such as opaque structures,
/// zero-length arrays, empty structures, etc.
///
/// ```
/// # use quartz::ir::*;
/// fn check_if_16_bytes_large(ty: &dyn IRType) -> bool {
///     match ty.layout() {
///         Some(layout) => layout.size() == 16,
///         None => false
///     }
/// }
/// ```
#[contract_trait]
pub trait IRType {
    /// Gets the exact size (in bytes) of the types. If the type is zero-sized,
    /// `None` is returned. Otherwise, `Some(size_in_bytes)` is returned.
    ///
    /// This size can be considered as the minimum amount of storage required
    /// to properly store the given type.
    ///
    /// Alignment is either the same or smaller than this size.
    ///
    /// # Unchecked Contracts
    /// * `ret >= self.align_req()`: The return value of [`align_req`] never exceeds the return value
    ///   of this method.
    ///
    /// * `ret.is_none() == self.align_req().is_none()`: If the return value is `None`,
    ///   so will be the return value of [`align_req`].
    #[ensures(ret != Some(0), "ret is never `Some(0)`")]
    fn size_req(&self) -> Option<u64>;

    /// Gets the size (in bytes) of the types. If the type is zero-sized,
    /// `None` is returned. Otherwise, `Some(size_in_bytes)` is returned.
    ///
    /// # Unchecked Contracts
    /// * `ret <= self.size_req()`: The return value of [`size_req`] is always the same
    ///   as or greater than the return value of this method.
    ///
    /// * `ret.is_none() == self.size_req().is_none()`: If the return value is `None`,
    ///   so will be the return value of [`size_req`].
    #[ensures(ret != Some(0), "ret is never `Some(0)`")]
    #[ensures(ret.is_none() || ret.unwrap().is_power_of_two(), "alignment is always a power of 2")]
    fn align_req(&self) -> Option<u64>;

    /// The preferred way of getting both size and alignment data for a type.
    ///
    /// This better codifies the unchecked contracts of [`size_req`] and [`align_req`],
    /// as if both would be `None` this returns `None`.
    ///
    /// If this returns `None`, the type is zero-sized and therefore has no layout requirements.
    /// Otherwise, the [`size`] and [`align`] functions return the requirements.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::*;
    /// let ty = Type::f64();
    /// let layout = ty.layout().unwrap();
    ///
    /// assert_eq!(layout.size(), 8);
    /// assert_eq!(layout.align(), 8);
    /// ```
    #[inline]
    #[ensures(ret != Some(TypeLayout { size: 0, align: 0 }), "ret is never `Some(0)`")]
    fn layout(&self) -> Option<TypeLayout> {
        debug_assert!(self.size_req().is_some() == self.align_req().is_some());

        // the contracts guarantee that if this is not `None`, neither will `self.align_req()`.
        self.size_req()
            .map(|x| TypeLayout::new(x, unsafe { self.align_req().unwrap_unchecked() }))
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct HiddenZeroSize();

impl Debug for HiddenZeroSize {
    fn fmt(&self, _: &mut Formatter<'_>) -> Result {
        Ok(())
    }
}

/// Models the `iN` class of fundamental types.
///
/// Integers are in the form `iN`, such that $N \in \\{8, 16, 32, 64\\}$. Other
/// bit widths are currently unsupported by the library.
///
/// See `iN` in the [Reference](https://pages.evanacox.io/quartz/qir/reference#in-integers).
///
/// # Example
/// ```
/// # use quartz::ir::*;
/// let t1 = IntType::i8();
/// assert_eq!(t1.width(), 8);
/// assert_eq!(t1.mask(), 0xFF);
/// assert_eq!(t1.sign_bit(), 0b1000_0000);
///
/// let t2 = IntType::new(8);
/// assert_eq!(t1, t2);
///
/// let t3 = IntType::i64();
/// assert_ne!(t1, t3);
/// ```
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct IntType {
    width: u32,
}

macro_rules! int_const_shorthand {
    ($n:tt, $lower:ident) => {
        #[doc = concat!("Shorthand for creating an integer of width `", stringify!($n), "`.")]
        #[doc = concat!("Exactly equivalent to `IntType::new(", stringify!($n), ")`.")]
        #[doc = ""]
        #[doc = "# Example"]
        #[doc = "```"]
        #[doc = "# use quartz::ir::IntType;"]
        #[doc = concat!("let t1 = IntType::i", stringify!($n), "();")]
        #[doc = concat!("let t2 = IntType::new(", stringify!($n), ");")]
        #[doc = ""]
        #[doc = "assert_eq!(t1, t2);"]
        #[doc = "```"]
        pub const fn $lower() -> Self {
            Self::of_width_unchecked($n)
        }
    };
}

impl IntType {
    /// The minimum bit-width of an integer type.
    pub const MIN_WIDTH: u64 = 8;

    /// The maximum bit-width of an integer type.
    pub const MAX_WIDTH: u64 = 64;

    #[inline]
    const fn of_width_unchecked(bit_width: u32) -> Self {
        Self { width: bit_width }
    }

    /// Creates an `Int` with a given width.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::*;
    /// let ty = IntType::new(32); // ty => i32
    ///
    /// assert_eq!(ty.width(), 32);
    /// assert_eq!(ty.size_req(), Some(4));
    /// assert_eq!(ty.align_req(), Some(4));
    /// ```
    #[inline]
    #[requires([8, 16, 32, 64].contains(&bit_width), "`bit_width` is one of $ \\{ 8, 16, 32, 64 \\}$")]
    pub fn new(bit_width: u32) -> Self {
        Self::of_width_unchecked(bit_width)
    }

    int_const_shorthand!(8, i8);
    int_const_shorthand!(16, i16);
    int_const_shorthand!(32, i32);
    int_const_shorthand!(64, i64);

    /// Gets the width of the integer.
    ///
    /// The integer will be within the bounds of the type.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::IntType;
    /// let ty = IntType::new(64);
    ///
    /// assert_eq!(ty.width(), 64);
    /// ```
    #[inline]
    #[ensures([8, 16, 32, 64].contains(&ret), "`ret` is one of $\\{8, 16, 32, 64\\}$")]
    pub fn width(self) -> u64 {
        self.width as u64
    }

    /// Returns a mask with the sign bit (MSB in 2's complement) set for
    /// an integer of `self.width()` width.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::IntType;
    /// let t1 = IntType::i32();
    /// let t2 = IntType::i8();
    ///
    /// assert_eq!(t1.sign_bit(), 0x80000000);
    /// assert_eq!(t2.sign_bit(), 0b1000_0000);
    /// ```
    #[inline]
    pub fn sign_bit(self) -> u64 {
        1u64 << ((self.width() as u64) - 1)
    }

    /// Returns a mask with every usable bit in the type set. This equivalent
    /// to the value resulting from the instruction `xor iN $x, -1`
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::IntType;
    /// let t1 = IntType::new(64);
    /// let t2 = IntType::new(16);
    ///
    /// assert_eq!(t1.mask(), 0xFFFFFFFFFFFFFFFF);
    /// assert_eq!(t2.mask(), 0b1111_1111_1111_1111);
    /// ```
    #[inline]
    pub fn mask(self) -> u64 {
        !0u64 >> (Self::MAX_WIDTH - self.width())
    }

    /// Checks if the integer type has a width of 8.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::IntType;
    /// let t1 = IntType::new(8);
    /// assert_eq!(t1.is_i8(), true);
    ///
    /// let t2 = IntType::new(32);
    /// assert_eq!(t2.is_i8(), false);
    /// ```
    #[inline]
    pub const fn is_i8(self) -> bool {
        self.width == 8
    }

    /// Checks if the integer type has a width of 16.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::IntType;
    /// let t1 = IntType::new(16);
    /// assert_eq!(t1.is_i16(), true);
    ///
    /// let t2 = IntType::new(64);
    /// assert_eq!(t2.is_i16(), false);
    /// ```
    #[inline]
    pub const fn is_i16(self) -> bool {
        self.width == 16
    }

    /// Checks if the integer type has a width of 32.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::IntType;
    /// let t1 = IntType::new(32);
    /// assert_eq!(t1.is_i32(), true);
    ///
    /// let t2 = IntType::new(16);
    /// assert_eq!(t2.is_i32(), false);
    /// ```
    #[inline]
    pub const fn is_i32(self) -> bool {
        self.width == 32
    }

    /// Checks if the integer type has a width of 64.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::IntType;
    /// let t1 = IntType::new(64);
    /// assert_eq!(t1.is_i64(), true);
    ///
    /// let t2 = IntType::new(8);
    /// assert_eq!(t2.is_i64(), false);
    /// ```
    #[inline]
    pub const fn is_i64(self) -> bool {
        self.width == 64
    }
}

#[contract_trait]
impl IRType for IntType {
    fn size_req(&self) -> Option<u64> {
        Some(self.width() / 8)
    }

    fn align_req(&self) -> Option<u64> {
        self.size_req()
    }
}

/// Maps the hardware representation of the floating-point types
/// to enum variants.
///
/// These map directly to types defined in the IEEE-754 standard.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum IEEEFloat {
    /// Models `f32`, an IEEE single-precision float (`binary32`).
    Single,
    /// Models `f64`, an IEEE double-precision float (`binary64`).
    Double,
}

/// Models the `fN` class of fundamental types.
///
/// Floats are in the form `fN`, such that $N \in \\{32, 64\\}$. They follow
/// the IEEE-754 standard, so `f32` is an IEEE Single and `f64` is an IEEE Double.
///
/// See `fN` in the [Reference](https://pages.evanacox.io/quartz/qir/reference#fn-floats).
///
/// # Example
/// ```
/// # use quartz::ir::*;
/// let t1 = Type::float(IEEEFloat::Single);
/// let t2 = Type::f32();
///
/// assert_eq!(t1, t2);
/// ```
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct FloatType {
    real: IEEEFloat,
}

impl FloatType {
    /// Creates an `fN` type from a given IEEE floating-point type
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::*;
    /// let t1 = FloatType::new(IEEEFloat::Single);
    /// let t2 = FloatType::f32();
    ///
    /// assert_eq!(t1, t2);
    /// ```
    #[inline]
    pub const fn new(real: IEEEFloat) -> Self {
        Self { real }
    }

    /// Creates an `f32` type
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::*;
    /// let t1 = FloatType::new(IEEEFloat::Single);
    /// let t2 = FloatType::f32();
    ///
    /// assert_eq!(t1, t2);
    /// ```
    pub const fn f32() -> Self {
        Self::new(IEEEFloat::Single)
    }

    /// Creates an `f64` type
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::*;
    /// let t1 = FloatType::new(IEEEFloat::Double);
    /// let t2 = FloatType::f64();
    ///
    /// assert_eq!(t1, t2);
    /// ```
    pub const fn f64() -> Self {
        Self::new(IEEEFloat::Double)
    }

    /// Gets the underlying IEEE floating-point type from a given `fN` type
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::*;
    /// let t1 = FloatType::new(IEEEFloat::Single);
    ///
    /// assert_eq!(t1.real(), IEEEFloat::Single);
    /// ```
    pub const fn real(self) -> IEEEFloat {
        self.real
    }
}

#[contract_trait]
impl IRType for FloatType {
    fn size_req(&self) -> Option<u64> {
        match self.real() {
            IEEEFloat::Single => IntType::i32().size_req(),
            IEEEFloat::Double => IntType::i64().size_req(),
        }
    }

    fn align_req(&self) -> Option<u64> {
        match self.real() {
            IEEEFloat::Single => IntType::i32().align_req(),
            IEEEFloat::Double => IntType::i64().align_req(),
        }
    }
}

/// Models the `bool` fundamental type. As of right now this type is completely stateless,
/// but in the future that may change.
///
/// See `bool` in the [Reference](https://pages.evanacox.io/quartz/qir/reference#bool-booleans).
///
/// # Example
/// ```
/// # use quartz::ir::*;
/// let ty = Type::bool();
///
/// assert!(ty.is_bool());
/// ```
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct BoolType(HiddenZeroSize);

impl BoolType {
    /// Creates a new `bool` type.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::BoolType;
    /// let b = BoolType::new();
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self(HiddenZeroSize())
    }
}

#[contract_trait]
impl IRType for BoolType {
    fn size_req(&self) -> Option<u64> {
        Some(1)
    }

    fn align_req(&self) -> Option<u64> {
        self.size_req()
    }
}

/// Models the `ptr` fundamental type. As of right now this type is completely stateless,
/// but in the future that may change.
///
/// See `ptr` in the [Reference](https://pages.evanacox.io/quartz/qir/reference#ptr-pointers).
///
/// # Example
/// ```
/// # use quartz::ir::*;
/// let ty = Type::ptr();
///
/// assert!(ty.is_ptr());
/// ```
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct PtrType(HiddenZeroSize);

impl PtrType {
    /// Creates a new `ptr` type.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::PtrType;
    /// let b = PtrType::new();
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self(HiddenZeroSize())
    }
}

#[contract_trait]
impl IRType for PtrType {
    fn size_req(&self) -> Option<u64> {
        Some(8)
    }

    fn align_req(&self) -> Option<u64> {
        self.size_req()
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct ArrayData {
    element: Type,
    len: u64,
}

/// Models the `[T; N]` compound type.
///
/// Implemented as a wrapper around a boxed type, so we don't run into
/// recursive type issues with `IRType`.
///
/// See `[T; N]` in the [Reference](https://pages.evanacox.io/quartz/qir/reference#t-n-arrays).
///
/// # Example
/// ```
/// # use quartz::ir::*;
/// let ty = Type::array(Type::i16(), 512);
///
/// assert!(ty.is_array());
/// ```
#[repr(transparent)]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ArrayType {
    data: Box<ArrayData>,
}

impl ArrayType {
    /// Creates a new `[T; N]`. If `len` is zero, this type is zero-sized.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::{ArrayType, Type};
    /// let t1 = Type::i8();
    /// let t2 = ArrayType::new(t1.clone(), 16);
    ///
    /// assert_eq!(*t2.element_type(), t1);
    /// assert_eq!(t2.len(), 16);
    /// ```
    pub fn new(element: Type, len: u64) -> Self {
        Self {
            data: Box::new(ArrayData { element, len }),
        }
    }

    /// Gets the type of the array, i.e. returns the `T` in `[T; N]`.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::{ArrayType, Type};
    /// let t1 = Type::i8();
    /// let t2 = ArrayType::new(t1.clone(), 16);
    ///
    /// assert_eq!(*t2.element_type(), t1);
    /// ```
    pub fn element_type(&self) -> &Type {
        &self.data.element
    }

    /// Gets the length of the array, i.e. returns the `N` in `[T; N]`.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::{ArrayType, Type};
    /// let t1 = Type::i8();
    /// let t2 = ArrayType::new(t1.clone(), 64);
    ///
    /// assert_eq!(t2.len(), 64);
    /// ```
    pub fn len(&self) -> u64 {
        self.data.len
    }

    /// Checks if the length of the array is zero.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::{ArrayType, Type};
    /// let t1 = ArrayType::new(Type::i8(), 16);
    /// assert_eq!(t1.is_empty(), false);
    ///
    /// let t2 = ArrayType::new(Type::i8(), 0);
    /// assert_eq!(t2.is_empty(), true);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[contract_trait]
impl IRType for ArrayType {
    fn size_req(&self) -> Option<u64> {
        if self.is_empty() {
            None
        } else {
            self.element_type().size_req().map(|x| x * self.len())
        }
    }

    fn align_req(&self) -> Option<u64> {
        if self.is_empty() {
            None
        } else {
            self.element_type().align_req()
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct StructTypeData {
    members: SmallVec<[Type; 4]>,
    max_align: u64,
    total_size: u64,
}

fn padding(curr: u64, align: u64) -> u64 {
    match curr.checked_rem(align) {
        None | Some(0) => 0,
        Some(x) => align - x,
    }
}

fn padded_struct_size(members: &[Type], largest_align: u64) -> u64 {
    // map each type into (alignment, size_in_bytes).
    //
    // to get size of padded struct, you go member by member, incrementing the size by
    // each member. if the size when a member is added is not a multiple of the member's
    // alignment, the difference between alignment and the remainder is added too (this is the padding)
    let members_padded = members
        .iter()
        .map(|ty| (ty.align_req().unwrap_or(0), ty.size_req().unwrap_or(0)))
        .fold(0, |acc, (align, size)| acc + padding(acc, align) + size);

    // need to make sure we apply padding for the last member too, so the overall struct
    // is aligned properly for the member with the largest alignment
    members_padded + padding(members_padded, largest_align)
}

fn largest_member_alignment(members: &[Type]) -> u64 {
    members
        .iter()
        .map(|ty| ty.align_req().unwrap_or(0))
        .max()
        .unwrap_or(0)
}

/// Models the `{ T... }` compound type.
///
/// Implemented as a wrapper around a boxed type, so we don't run into
/// recursive type issues with `IRType`.
///
/// See `{ T... }` in the [Reference](https://pages.evanacox.io/quartz/qir/reference#-t--structures).
///
/// # Example
/// ```
/// # use quartz::ir::*;
/// // ty => { ptr, i64, i64 }
/// let ty = StructType::new([
///     Type::ptr(),
///     Type::i64(),
///     Type::i64()
/// ]);
/// ```
#[repr(transparent)]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct StructType(Box<StructTypeData>);

impl StructType {
    /// Creates an empty struct type, i.e. `{ }`.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::*;
    /// // ty => { }
    /// let ty = StructType::empty();
    ///
    /// assert_eq!(ty.members(), &([] as [Type; 0]));
    /// assert_eq!(ty.is_empty(), true);
    /// ```
    pub fn empty() -> Self {
        Self(Box::new(StructTypeData {
            members: SmallVec::default(),
            max_align: 0,
            total_size: 0,
        }))
    }

    /// Creates a struct type with a list of member types.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::{StructType, Type};
    /// // ty => { i32, ptr }
    /// let ty = StructType::new([Type::i32(), Type::ptr()]);
    ///
    /// assert_eq!(ty.members(), [Type::i32(), Type::ptr()]);
    /// ```
    #[inline]
    pub fn new<T: IntoIterator<Item = Type>>(members: T) -> Self {
        Self::from_vec(SmallVec::from_iter(members.into_iter()))
    }

    /// Creates a struct type with a list of member types.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::{StructType, Type};
    /// # use smallvec::smallvec;
    /// // ty => { i32, ptr }
    /// let ty = StructType::from_vec(smallvec![Type::i32(), Type::ptr()]);
    ///
    /// assert_eq!(ty.members(), [Type::i32(), Type::ptr()]);
    /// ```
    pub fn from_vec(members: SmallVec<[Type; 4]>) -> Self {
        let largest = largest_member_alignment(&members);

        Self(Box::new(StructTypeData {
            total_size: padded_struct_size(&members, largest),
            max_align: largest,
            members,
        }))
    }

    /// Gets the members of the structure as a slice. An empty structure
    /// will have a slice with a length of zero.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::*;
    /// let t1 = StructType::new([Type::i8(), Type::i8()]);
    /// assert_eq!(t1.members(), [Type::i8(), Type::i8()]);
    ///
    /// let t2 = StructType::empty();
    /// assert_eq!(t2.members(), &([] as [Type; 0]));
    /// ```
    #[inline]
    pub fn members(&self) -> &[Type] {
        &self.0.members
    }

    /// Gets the members of the structure as a slice.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::*;
    /// let t1 = StructType::new([Type::i8(), Type::i8()]);
    /// assert_eq!(t1.len(), 2);
    ///
    /// let t2 = StructType::empty();
    /// assert_eq!(t2.len(), 0);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.0.members.len()
    }

    /// Gets the members of the structure as a slice.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::*;
    /// let t1 = StructType::new([Type::i8(), Type::i8()]);
    /// assert_eq!(t1.is_empty(), false);
    ///
    /// let t2 = StructType::empty();
    /// assert_eq!(t2.is_empty(), true);
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[contract_trait]
impl IRType for StructType {
    fn size_req(&self) -> Option<u64> {
        match self.0.total_size {
            0 => None,
            x => Some(x),
        }
    }

    fn align_req(&self) -> Option<u64> {
        match self.0.max_align {
            0 => None,
            x => Some(x),
        }
    }
}

/// A single type in QIR.
///
/// This is the public-facing type that is used whenever a
#[derive(IntoStaticStr, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Type {
    /// A boolean type.
    ///
    /// See `bool` in the [Reference](https://pages.evanacox.io/quartz/qir/reference#bool-booleans)
    Bool(BoolType),
    /// A raw integer type of some width.
    ///
    /// See `iN` in the [Reference](https://pages.evanacox.io/quartz/qir/reference#in-integers)
    Int(IntType),
    /// An IEEE floating-point type of some width.
    ///
    /// See `fN` in the [Reference](https://pages.evanacox.io/quartz/qir/reference#fn-floats)
    Float(FloatType),
    /// The `ptr` type, equivalent to C's `void*`.
    ///
    /// See `ptr` in the [Reference](https://pages.evanacox.io/quartz/qir/reference#ptr-pointers)
    Ptr(PtrType),
    /// An array type of the form `[T; N]`.
    ///
    /// See `[T; N]` in the [Reference](https://pages.evanacox.io/quartz/qir/reference#t-n-arrays)
    Array(ArrayType),
    /// A structure type of the form `{ T... }`.
    ///
    /// See `{ T... }` in the [Reference](https://pages.evanacox.io/quartz/qir/reference#-t--structures)
    Struct(StructType),
}

const_assert_eq!(mem::size_of::<Type>(), 16);

macro_rules! helper_methods {
    ($variant:ident, $type:ty, $lower:ident, $wrong_lower:ident, $right_init:tt, $wrong_init:tt, $is:ident, $unwrap:ident, $expect:ident) => {
        #[doc = concat!("Checks if `self` is currently a `", stringify!($variant), "`.")]
        #[doc = ""]
        #[doc = "```"]
        #[doc = "# use quartz::ir::*;"]
        #[doc = concat!("let ty = ", $right_init, ";")]
        #[doc = concat!("assert_eq!(ty.is_", stringify!($lower), "(), true);")]
        #[doc = concat!("assert_eq!(ty.is_", stringify!($wrong_lower), "(), false);")]
        #[doc = "```"]
        pub fn $is(&self) -> bool {
            match self {
                Self::$variant(_) => true,
                _ => false,
            }
        }

        #[doc = concat!("Checks if the current variant is `", stringify!($variant), "`.")]
        #[doc = "If it is, it returns the data for that variant."]
        #[doc = ""]
        #[doc = "# Panics"]
        #[doc = concat!("Panics if the current variant is not `", stringify!($variant), "`.")]
        #[doc = ""]
        #[doc = "# Examples"]
        #[doc = "```"]
        #[doc = "# use quartz::ir::*;"]
        #[doc = concat!("let ty = ", $right_init, ";")]
        #[doc = concat!("let data: ", stringify!($type), " = ty.unwrap_", stringify!($lower), "();")]
        #[doc = "```"]
        #[doc = ""]
        #[doc = "```should_panic"]
        #[doc = "# use quartz::ir::*;"]
        #[doc = concat!("let ty = ", $wrong_init, ";")]
        #[doc = concat!("let data: ", stringify!($type), " = ty.unwrap_", stringify!($lower), "(); // panics!")]
        #[doc = "```"]
        pub fn $unwrap(self) -> $type {
            match self {
                Self::$variant(data) => data,
                _ => panic!("expected self to be `{}` but got '{}'", stringify!($variant), Into::<&'static str>::into(self)),
            }
        }

        #[doc = concat!("Checks if the current variant is `", stringify!($variant), "`.")]
        #[doc = "If it is, it returns the data for that variant."]
        #[doc = ""]
        #[doc = "# Panics"]
        #[doc = concat!("Panics with `message` if the current variant is not `", stringify!($variant), "`.")]
        #[doc = ""]
        #[doc = "# Examples"]
        #[doc = "```"]
        #[doc = "# use quartz::ir::*;"]
        #[doc = concat!("let ty = ", $right_init, ";")]
        #[doc = concat!("let data: ", stringify!($type), " = ty.expect_", stringify!($lower), "(\"should be the right type\");")]
        #[doc = "```"]
        #[doc = ""]
        #[doc = "```should_panic"]
        #[doc = "# use quartz::ir::*;"]
        #[doc = concat!("let ty = ", $wrong_init, ";")]
        #[doc = concat!("let data: ", stringify!($type), " = ty.expect_", stringify!($lower), "(\"should be the right type\"); // panics!")]
        #[doc = "```"]
        pub fn $expect(self, message: &str) -> $type {
            match self {
                Self::$variant(data) => data,
                _ => panic!(
                    "expected self to be `{}` but got '{}'. message: {}",
                    stringify!($variant),
                    Into::<&'static str>::into(self),
                    message
                ),
            }
        }
    };
}

macro_rules! int_shorthand {
    ($len:tt, $name:ident) => {
        #[doc = concat!("Creates a `Type` that models `i", stringify!($len), "`. Equivalent to `Type::int(", stringify!($len), ")`.")]
        #[doc = ""]
        #[doc = "# Example"]
        #[doc = "```"]
        #[doc = "# use quartz::ir::Type;"]
        #[doc = "let ty1 = Type::i8();"]
        #[doc = "let ty2 = Type::int(8);"]
        #[doc = ""]
        #[doc = "assert_eq!(ty1, ty2);"]
        #[doc = "```"]
        #[inline]
        pub const fn $name() -> Self {
            Self::Int(IntType::$name())
        }
    }
}

macro_rules! float_shorthand {
    ($len:tt, $long:ident, $name:ident) => {
        #[doc = concat!("Creates a `Type` that models `f", stringify!($len), "`.")]
        #[doc = concat!("Equivalent to `Type::float(FloatType::", stringify!($long), ")`.")]
        #[doc = ""]
        #[doc = "# Example"]
        #[doc = "```"]
        #[doc = "# use quartz::ir::*;"]
        #[doc = concat!("let ty1 = Type::f", stringify!($len), "();")]
        #[doc = concat!("let ty2 = Type::float(IEEEFloat::", stringify!($long), ");")]
        #[doc = ""]
        #[doc = "assert_eq!(ty1, ty2);"]
        #[doc = "```"]
        #[inline]
        pub const fn $name() -> Self {
            Self::Float(FloatType::new(IEEEFloat::$long))
        }
    };
}

impl Type {
    /// Creates a new `bool` type. Equivalent to `Type::Bool(BoolType::new())`.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::Type;
    /// let ty = Type::bool();
    ///
    /// assert!(ty.is_bool());
    /// ```
    #[inline]
    pub const fn bool() -> Self {
        Self::Bool(BoolType::new())
    }

    /// Creates a new `iN` type. Equivalent to `Type::Int(IntType::of_width(width))`.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::Type;
    /// let ty = Type::int(32);
    ///
    /// assert!(ty.is_int());
    /// ```
    #[inline]
    #[requires([8, 16, 32, 64].contains(&bit_width), "`bit_width` is one of $ \\{ 8, 16, 32, 64 \\}$")]
    pub fn int(bit_width: u32) -> Self {
        Self::Int(IntType::of_width_unchecked(bit_width))
    }

    /// Creates a type modeling `fN` from a given type of float.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::*;
    /// let ty = Type::float(IEEEFloat::Single);
    ///
    /// assert_eq!(ty.is_float(), true)
    /// ```
    #[inline]
    pub const fn float(ty: IEEEFloat) -> Self {
        Self::Float(FloatType::new(ty))
    }

    /// Creates a new `ptr` type. Equivalent to `Type::Ptr(PtrType::new())`.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::Type;
    /// let ty = Type::ptr();
    ///
    /// assert_eq!(ty.is_ptr(), true);
    /// ```
    #[inline]
    pub const fn ptr() -> Self {
        Self::Ptr(PtrType::new())
    }

    /// Creates a new `[T; N]` type. Equivalent to `Type::Array(ArrayType::new(ty, len))`.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::Type;
    /// let ty = Type::array(Type::i32(), 16);
    ///
    /// assert_eq!(ty.is_array(), true);
    /// ```
    #[inline]
    pub fn array(ty: Type, len: u64) -> Self {
        Self::Array(ArrayType::new(ty, len))
    }

    /// Creates a new `{ T... }` type. Equivalent to `Type::Struct(StructType::new(members))`.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::Type;
    /// let ty = Type::structure([Type::f64(), Type::f64()]);
    ///
    /// assert_eq!(ty.is_struct(), true);
    /// ```
    #[inline]
    pub fn structure<T: IntoIterator<Item = Type>>(members: T) -> Self {
        Self::Struct(StructType::new(members))
    }

    int_shorthand!(8, i8);
    int_shorthand!(16, i16);
    int_shorthand!(32, i32);
    int_shorthand!(64, i64);

    float_shorthand!(32, Single, f32);
    float_shorthand!(64, Double, f64);

    /// Creates the empty `{ }` type. Equivalent to `Type::Struct(StructType::empty())`.
    ///
    /// # Example
    /// ```
    /// # use quartz::ir::Type;
    /// let ty = Type::empty_struct();
    ///
    /// assert_eq!(ty.is_struct(), true);
    /// ```
    #[inline]
    pub fn empty_struct() -> Self {
        Self::Struct(StructType::empty())
    }

    helper_methods!(
        Bool,
        BoolType,
        bool,
        ptr,
        "Type::bool()",
        "Type::i32()",
        is_bool,
        unwrap_bool,
        expect_bool
    );

    helper_methods!(
        Int,
        IntType,
        int,
        bool,
        "Type::i64()",
        "Type::ptr()",
        is_int,
        unwrap_int,
        expect_int
    );

    helper_methods!(
        Float,
        FloatType,
        float,
        int,
        "Type::f64()",
        "Type::i32()",
        is_float,
        unwrap_float,
        expect_float
    );

    helper_methods!(
        Ptr,
        PtrType,
        ptr,
        array,
        "Type::ptr()",
        "Type::bool()",
        is_ptr,
        unwrap_ptr,
        expect_ptr
    );

    helper_methods!(
        Array,
        ArrayType,
        array,
        ptr,
        "Type::array(Type::ptr(), 512)",
        "Type::f32()",
        is_array,
        unwrap_array,
        expect_array
    );

    helper_methods!(
        Struct,
        StructType,
        struct,
        int,
        "Type::structure([Type::ptr(), Type::i64(), Type::i64()])",
        "Type::ptr()",
        is_struct,
        unwrap_struct,
        expect_struct
    );
}

#[contract_trait]
impl IRType for Type {
    fn size_req(&self) -> Option<u64> {
        match self {
            Type::Bool(b) => b.size_req(),
            Type::Int(i) => i.size_req(),
            Type::Float(f) => f.size_req(),
            Type::Ptr(p) => p.size_req(),
            Type::Array(a) => a.size_req(),
            Type::Struct(s) => s.size_req(),
        }
    }

    fn align_req(&self) -> Option<u64> {
        match self {
            Type::Bool(b) => b.align_req(),
            Type::Int(i) => i.align_req(),
            Type::Float(f) => f.align_req(),
            Type::Ptr(p) => p.align_req(),
            Type::Array(a) => a.align_req(),
            Type::Struct(s) => s.align_req(),
        }
    }
}

macro_rules! compare_against_variant {
    ($ty:ident, $var:ident) => {
        impl PartialEq<$ty> for Type {
            fn eq(&self, other: &$ty) -> bool {
                match self {
                    Type::$var(x) => x == other,
                    _ => false,
                }
            }
        }
    };
}

compare_against_variant!(IntType, Int);
compare_against_variant!(FloatType, Float);
compare_against_variant!(BoolType, Bool);
compare_against_variant!(PtrType, Ptr);
compare_against_variant!(ArrayType, Array);
compare_against_variant!(StructType, Struct);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_layout_methods() {
        let empty = Type::empty_struct().layout();
        let equal_align_size = Type::i64().layout();
        let unequal_align_size = Type::array(Type::i32(), 16).layout();

        assert_eq!(empty, None);
        assert!(equal_align_size.is_some());
        assert!(unequal_align_size.is_some());

        let equal_align_size = equal_align_size.unwrap();
        let unequal_align_size = unequal_align_size.unwrap();

        assert_eq!(equal_align_size.size(), equal_align_size.align());
        assert_ne!(unequal_align_size.size(), unequal_align_size.align());

        assert_eq!(equal_align_size.size(), 8);
        assert_eq!(equal_align_size.align(), 8);

        assert_eq!(unequal_align_size.size(), 4 * 16);
        assert_eq!(unequal_align_size.align(), 4);
    }

    #[test]
    fn type_layout_constructor() {
        let layout = TypeLayout::new(16, 8);

        assert_eq!(layout.size(), 16);
        assert_eq!(layout.align(), 8);
    }

    #[test]
    #[should_panic]
    fn type_layout_constructor_fail() {
        let _ = TypeLayout::new(8, 16);
    }

    #[test]
    fn int_type_constructors() {
        let i8_1 = IntType::new(8);
        let i16_1 = IntType::new(16);
        let i32_1 = IntType::new(32);
        let i64_1 = IntType::new(64);
        let i8_2 = IntType::i8();
        let i16_2 = IntType::i16();
        let i32_2 = IntType::i32();
        let i64_2 = IntType::i64();

        assert_eq!(i8_1, i8_2);
        assert_eq!(i16_1, i16_2);
        assert_eq!(i32_1, i32_2);
        assert_eq!(i64_1, i64_2);

        assert_ne!(i8_1, i64_1);

        let i32_3 = i32_2;
        #[allow(clippy::clone_on_copy)]
        let i32_4 = i32_2.clone();

        assert_eq!(i32_2, i32_3);
        assert_eq!(i32_2, i32_4);

        assert!(i8_1.is_i8());
        assert!(i16_1.is_i16());
        assert!(i32_1.is_i32());
        assert!(i64_1.is_i64());
    }

    #[test]
    #[should_panic]
    fn int_type_constructors_fail() {
        let _ = IntType::new(9);
    }

    #[test]
    fn int_type_sign_bit() {
        let i8 = IntType::i8();
        let i16 = IntType::i16();
        let i32 = IntType::i32();
        let i64 = IntType::i64();

        assert_eq!(i8.sign_bit(), 0x80);
        assert_eq!(i16.sign_bit(), 0x8000);
        assert_eq!(i32.sign_bit(), 0x8000_0000);
        assert_eq!(i64.sign_bit(), 0x8000_0000_0000_0000);
    }

    #[test]
    fn int_type_mask() {
        let i8 = IntType::i8();
        let i16 = IntType::i16();
        let i32 = IntType::i32();
        let i64 = IntType::i64();

        assert_eq!(i8.mask(), 0xFF);
        assert_eq!(i16.mask(), 0xFFFF);
        assert_eq!(i32.mask(), 0xFFFF_FFFF);
        assert_eq!(i64.mask(), 0xFFFF_FFFF_FFFF_FFFF);
    }

    #[test]
    fn int_type_layout() {
        let i8 = IntType::i8();
        let i16 = IntType::i16();
        let i32 = IntType::i32();
        let i64 = IntType::i64();

        assert_eq!(i8.size_req(), Some(1));
        assert_eq!(i16.size_req(), Some(2));
        assert_eq!(i32.size_req(), Some(4));
        assert_eq!(i64.size_req(), Some(8));

        assert_eq!(i8.align_req(), Some(1));
        assert_eq!(i16.align_req(), Some(2));
        assert_eq!(i32.align_req(), Some(4));
        assert_eq!(i64.align_req(), Some(8));
    }

    #[test]
    fn float_type() {
        let f32 = FloatType::f32();
        let f32_2 = FloatType::new(IEEEFloat::Single);
        let f64 = FloatType::f64();
        let f64_2 = FloatType::new(IEEEFloat::Double);
        let f32_layout = f32.layout().unwrap();
        let f64_layout = f64.layout().unwrap();

        assert_ne!(f32, f64);
        assert_eq!(f32, f32_2);
        assert_eq!(f64, f64_2);
        assert_eq!(f32_layout.size(), f32_layout.align());
        assert_eq!(f64_layout.size(), f64_layout.align());
        assert_eq!(f32_layout.size(), 4);
        assert_eq!(f64_layout.size(), 8);
    }

    #[test]
    fn bool_type() {
        let bool = BoolType::new();
        let bool2 = bool;
        #[allow(clippy::clone_on_copy)]
        let bool3 = bool.clone();
        let bool_layout = bool.layout().unwrap();

        assert_eq!(bool, bool2);
        assert_eq!(bool2, bool3);

        assert_eq!(bool_layout, Type::i8().layout().unwrap());
    }

    #[test]
    fn ptr_type() {
        let ptr = PtrType::new();
        let ptr2 = ptr;
        #[allow(clippy::clone_on_copy)]
        let ptr3 = ptr.clone();
        let ptr_layout = ptr.layout().unwrap();

        assert_eq!(ptr, ptr2);
        assert_eq!(ptr2, ptr3);

        assert_eq!(ptr_layout, Type::i64().layout().unwrap());
    }

    #[test]
    fn array_type_normal() {
        let t1 = ArrayType::new(Type::i8(), 16);
        let t2 = t1.clone();
        let t1_layout = t1.layout().unwrap();

        assert_eq!(t1, t2);
        assert_eq!(*t1.element_type(), Type::i8());
        assert_eq!(t1.len(), 16);
        assert!(!t1.is_empty());
        assert_eq!(t1_layout.size(), 16);
        assert_eq!(t1_layout.align(), 1);
    }

    #[test]
    fn array_type_one() {
        let ty = ArrayType::new(Type::i64(), 1);
        let layout = ty.layout();

        assert_eq!(ty.len(), 1);
        assert!(!ty.is_empty());
        assert_eq!(layout, Type::i64().layout());
    }

    #[test]
    fn array_type_empty_len() {
        let ty = ArrayType::new(Type::i64(), 0);
        let layout = ty.layout();

        assert_eq!(ty.len(), 0);
        assert!(ty.is_empty());
        assert_eq!(layout, None);
        assert_eq!(layout, Type::empty_struct().layout());
    }

    #[test]
    fn array_type_empty_type() {
        let ty = ArrayType::new(Type::empty_struct(), 1);
        let ty2 = ty.clone();
        let layout = ty.layout();

        assert_eq!(ty, ty2);
        assert_eq!(ty.len(), 1);
        assert!(!ty.is_empty());
        assert_eq!(layout, None);
        assert_eq!(layout, Type::empty_struct().layout());
    }

    #[test]
    fn struct_type_methods() {
        let ty = StructType::new([Type::f32(), Type::i8(), Type::array(Type::i64(), 512)]);

        assert_eq!(
            ty.members(),
            [Type::f32(), Type::i8(), Type::array(Type::i64(), 512)]
        );
        assert_eq!(ty.len(), 3);
        assert!(!ty.is_empty());
    }

    #[test]
    fn struct_type_no_padding() {
        let ty = StructType::new([Type::i64(), Type::ptr()]);
        let layout = ty.layout().unwrap();

        assert_eq!(layout.size(), 16);
        assert_eq!(layout.align(), 8);
    }

    #[test]
    fn struct_type_empty() {
        let t1 = StructType::new([]);
        let t2 = StructType::new([
            Type::empty_struct(),
            Type::array(Type::i64(), 0),
            Type::array(Type::empty_struct(), 512),
        ]);

        assert_eq!(t1.layout(), None);
        assert_eq!(t2.layout(), None);
    }

    #[test]
    fn struct_type_padded() {
        // struct {
        //   int32
        //   int16
        //   [ 2 byte padding ]
        //   ptr
        // }
        let t1 = StructType::new([Type::i32(), Type::i16(), Type::ptr()]);
        let t1_layout = t1.layout().unwrap();

        assert_eq!(t1_layout.size(), 16);
        assert_eq!(t1_layout.align(), 8);

        // struct {
        //   int64
        //   int8
        //   [ 7 byte padding ]
        //   ptr
        // }
        let t2 = StructType::new([Type::i64(), Type::i8(), Type::ptr()]);
        let t2_layout = t2.layout().unwrap();

        assert_eq!(t2_layout.size(), 24);
        assert_eq!(t2_layout.align(), 8);

        // struct {
        //   int16
        //   [ 2 byte padding ]
        //   int32
        //   int8
        //   [ 7 byte padding ]
        //   int64
        //   int8
        //   [ 7 byte padding ]
        // }
        let t3 = StructType::new([
            Type::i16(),
            Type::i32(),
            Type::i8(),
            Type::i64(),
            Type::i8(),
        ]);
        let t3_layout = t3.layout().unwrap();

        assert_eq!(t3_layout.size(), 32);
        assert_eq!(t3_layout.align(), 8);

        // struct {
        //   int32
        //   int8
        //   [ 3 byte padding ]
        //   int32
        //   int16
        //   [ 2 byte padding ]
        // }
        let t4 = StructType::new([Type::i32(), Type::i8(), Type::i32(), Type::i16()]);
        let t4_layout = t4.layout().unwrap();

        assert_eq!(t4_layout.size(), 16);
        assert_eq!(t4_layout.align(), 4);
    }

    #[test]
    fn type_equality() {
        assert_eq!(Type::i8(), IntType::i8());
        assert_eq!(Type::int(32), IntType::i32());
        assert_eq!(Type::f32(), FloatType::f32());
        assert_eq!(Type::float(IEEEFloat::Double), FloatType::f64());
        assert_eq!(Type::bool(), BoolType::new());
        assert_eq!(Type::ptr(), PtrType::new());
        assert_eq!(Type::array(Type::i8(), 2), ArrayType::new(Type::i8(), 2));
        assert_eq!(
            Type::structure([Type::ptr(), Type::ptr()]),
            StructType::new([Type::ptr(), Type::ptr()])
        );
    }
}
