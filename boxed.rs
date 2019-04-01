//! A pointer type for heap allocation.
//!
//! `Box<T>`, casually referred to as a 'box', provides the simplest form of
//! heap allocation in Rust. Boxes provide ownership for this allocation, and
//! drop their contents when they go out of scope.
//!
//! For non-zero-sized values, a [`Box`] will use the [`Global`] allocator for
//! its allocation. It is valid to convert both ways between a [`Box`] and a
//! raw pointer allocated with the [`Global`] allocator, given that the
//! [`Layout`] used with the allocator is correct for the type. More precisely,
//! a `value: *mut T` that has been allocated with the [`Global`] allocator
//! with `Layout::for_value(&*value)` may be converted into a box using
//! `Box::<T>::from_raw(value)`. Conversely, the memory backing a `value: *mut
//! T` obtained from `Box::<T>::into_raw` may be deallocated using the
//! [`Global`] allocator with `Layout::for_value(&*value)`.
//!
//! # Examples
//!
//! Move a value from the stack to the heap by creating a [`Box`]:
//!
//! ```
//! let val: u8 = 5;
//! let boxed: Box<u8> = Box::new(val);
//! ```
//!
//! Move a value from a [`Box`] back to the stack by [dereferencing]:
//!
//! ```
//! let boxed: Box<u8> = Box::new(5);
//! let val: u8 = *boxed;
//! ```
//!
//! Creating a recursive data structure:
//!
//! ```
//! #[derive(Debug)]
//! enum List<T> {
//!     Cons(T, Box<List<T>>),
//!     Nil,
//! }
//!
//! fn main() {
//!     let list: List<i32> = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
//!     println!("{:?}", list);
//! }
//! ```
//!
//! This will print `Cons(1, Cons(2, Nil))`.
//!
//! Recursive structures must be boxed, because if the definition of `Cons`
//! looked like this:
//!
//! ```compile_fail,E0072
//! # enum List<T> {
//! Cons(T, List<T>),
//! # }
//! ```
//!
//! It wouldn't work. This is because the size of a `List` depends on how many
//! elements are in the list, and so we don't know how much memory to allocate
//! for a `Cons`. By introducing a `Box`, which has a defined size, we know how
//! big `Cons` needs to be.
//!
//! [dereferencing]: ../../std/ops/trait.Deref.html
//! [`Box`]: struct.Box.html

#![stable(feature = "rust1", since = "1.0.0")]

use core::any::Any;
use core::borrow;
use core::cmp::Ordering;
use core::convert::From;
use core::fmt;
use core::future::Future;
use core::hash::{Hash, Hasher};
use core::iter::{Iterator, FromIterator, FusedIterator};
use core::marker::{Unpin, Unsize};
use core::mem;
use core::ops::{
    CoerceUnsized, DispatchFromDyn, Deref, DerefMut, Receiver, Generator, GeneratorState
};
use core::ptr::{self, NonNull, Unique};
use core::task::{Waker, Poll};

/// A pointer type for heap allocation.
///
/// See the [module-level documentation](../../std/boxed/index.html) for more.
#[lang = "owned_box"]
#[fundamental]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct Box<T: ?Sized>(Unique<T>);

impl<T> Box<T> {
    /// Allocates memory on the heap and then places `x` into it.
    ///
    /// This doesn't actually allocate if `T` is zero-sized.
    ///
    /// # Examples
    ///
    /// ```
    /// let five = Box::new(5);
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline(always)]
    pub fn new(x: T) -> Box<T> {
        box x
    }
}

impl<T: ?Sized> Box<T> {
    /// Constructs a box from a raw pointer.
    ///
    /// After calling this function, the raw pointer is owned by the
    /// resulting `Box`. Specifically, the `Box` destructor will call
    /// the destructor of `T` and free the allocated memory. Since the
    /// way `Box` allocates and releases memory is unspecified, the
    /// only valid pointer to pass to this function is the one taken
    /// from another `Box` via the [`Box::into_raw`] function.
    ///
    /// This function is unsafe because improper use may lead to
    /// memory problems. For example, a double-free may occur if the
    /// function is called twice on the same raw pointer.
    ///
    /// [`Box::into_raw`]: struct.Box.html#method.into_raw
    ///
    /// # Examples
    ///
    /// ```
    /// let x = Box::new(5);
    /// let ptr = Box::into_raw(x);
    /// let x = unsafe { Box::from_raw(ptr) };
    /// ```
    #[stable(feature = "box_raw", since = "1.4.0")]
    #[inline]
    pub unsafe fn from_raw(raw: *mut T) -> Self {
        Box(Unique::new_unchecked(raw))
    }

    /// Consumes the `Box`, returning a wrapped raw pointer.
    ///
    /// The pointer will be properly aligned and non-null.
    ///
    /// After calling this function, the caller is responsible for the
    /// memory previously managed by the `Box`. In particular, the
    /// caller should properly destroy `T` and release the memory. The
    /// proper way to do so is to convert the raw pointer back into a
    /// `Box` with the [`Box::from_raw`] function.
    ///
    /// Note: this is an associated function, which means that you have
    /// to call it as `Box::into_raw(b)` instead of `b.into_raw()`. This
    /// is so that there is no conflict with a method on the inner type.
    ///
    /// [`Box::from_raw`]: struct.Box.html#method.from_raw
    ///
    /// # Examples
    ///
    /// ```
    /// let x = Box::new(5);
    /// let ptr = Box::into_raw(x);
    /// ```
    #[stable(feature = "box_raw", since = "1.4.0")]
    #[inline]
    pub fn into_raw(b: Box<T>) -> *mut T {
        Box::into_raw_non_null(b).as_ptr()
    }

    /// Consumes the `Box`, returning the wrapped pointer as `NonNull<T>`.
    ///
    /// After calling this function, the caller is responsible for the
    /// memory previously managed by the `Box`. In particular, the
    /// caller should properly destroy `T` and release the memory. The
    /// proper way to do so is to convert the `NonNull<T>` pointer
    /// into a raw pointer and back into a `Box` with the [`Box::from_raw`]
    /// function.
    ///
    /// Note: this is an associated function, which means that you have
    /// to call it as `Box::into_raw_non_null(b)`
    /// instead of `b.into_raw_non_null()`. This
    /// is so that there is no conflict with a method on the inner type.
    ///
    /// [`Box::from_raw`]: struct.Box.html#method.from_raw
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(box_into_raw_non_null)]
    ///
    /// fn main() {
    ///     let x = Box::new(5);
    ///     let ptr = Box::into_raw_non_null(x);
    /// }
    /// ```
    #[unstable(feature = "box_into_raw_non_null", issue = "47336")]
    #[inline]
    pub fn into_raw_non_null(b: Box<T>) -> NonNull<T> {
        Box::into_unique(b).into()
    }

    #[unstable(feature = "ptr_internals", issue = "0", reason = "use into_raw_non_null instead")]
    #[inline]
    #[doc(hidden)]
    pub fn into_unique(mut b: Box<T>) -> Unique<T> {
        // Box is kind-of a library type, but recognized as a "unique pointer" by
        // Stacked Borrows.  This function here corresponds to "reborrowing to
        // a raw pointer", but there is no actual reborrow here -- so
        // without some care, the pointer we are returning here still carries
        // the `Uniq` tag.  We round-trip through a mutable reference to avoid that.
        let unique = unsafe { b.0.as_mut() as *mut T };
        mem::forget(b);
        unsafe { Unique::new_unchecked(unique) }
    }

    /// Consumes and leaks the `Box`, returning a mutable reference,
    /// `&'a mut T`. Note that the type `T` must outlive the chosen lifetime
    /// `'a`. If the type has only static references, or none at all, then this
    /// may be chosen to be `'static`.
    ///
    /// This function is mainly useful for data that lives for the remainder of
    /// the program's life. Dropping the returned reference will cause a memory
    /// leak. If this is not acceptable, the reference should first be wrapped
    /// with the [`Box::from_raw`] function producing a `Box`. This `Box` can
    /// then be dropped which will properly destroy `T` and release the
    /// allocated memory.
    ///
    /// Note: this is an associated function, which means that you have
    /// to call it as `Box::leak(b)` instead of `b.leak()`. This
    /// is so that there is no conflict with a method on the inner type.
    ///
    /// [`Box::from_raw`]: struct.Box.html#method.from_raw
    ///
    /// # Examples
    ///
    /// Simple usage:
    ///
    /// ```
    /// fn main() {
    ///     let x = Box::new(41);
    ///     let static_ref: &'static mut usize = Box::leak(x);
    ///     *static_ref += 1;
    ///     assert_eq!(*static_ref, 42);
    /// }
    /// ```
    ///
    /// Unsized data:
    ///
    /// ```
    /// fn main() {
    ///     let x = vec![1, 2, 3].into_boxed_slice();
    ///     let static_ref = Box::leak(x);
    ///     static_ref[0] = 4;
    ///     assert_eq!(*static_ref, [4, 2, 3]);
    /// }
    /// ```
    #[stable(feature = "box_leak", since = "1.26.0")]
    #[inline]
    pub fn leak<'a>(b: Box<T>) -> &'a mut T
    where
        T: 'a // Technically not needed, but kept to be explicit.
    {
        unsafe { &mut *Box::into_raw(b) }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
unsafe impl<#[may_dangle] T: ?Sized> Drop for Box<T> {
    fn drop(&mut self) {
        // FIXME: Do nothing, drop is currently performed by compiler.
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Default> Default for Box<T> {
    /// Creates a `Box<T>`, with the `Default` value for T.
    fn default() -> Box<T> {
        box Default::default()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Clone> Clone for Box<T> {
    /// Returns a new box with a `clone()` of this box's contents.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = Box::new(5);
    /// let y = x.clone();
    /// ```
    #[rustfmt::skip]
    #[inline]
    fn clone(&self) -> Box<T> {
        box { (**self).clone() }
    }
    /// Copies `source`'s contents into `self` without creating a new allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = Box::new(5);
    /// let mut y = Box::new(10);
    ///
    /// y.clone_from(&x);
    ///
    /// assert_eq!(*y, 5);
    /// ```
    #[inline]
    fn clone_from(&mut self, source: &Box<T>) {
        (**self).clone_from(&(**source));
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized + PartialEq> PartialEq for Box<T> {
    #[inline]
    fn eq(&self, other: &Box<T>) -> bool {
        PartialEq::eq(&**self, &**other)
    }
    #[inline]
    fn ne(&self, other: &Box<T>) -> bool {
        PartialEq::ne(&**self, &**other)
    }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized + PartialOrd> PartialOrd for Box<T> {
    #[inline]
    fn partial_cmp(&self, other: &Box<T>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
    #[inline]
    fn lt(&self, other: &Box<T>) -> bool {
        PartialOrd::lt(&**self, &**other)
    }
    #[inline]
    fn le(&self, other: &Box<T>) -> bool {
        PartialOrd::le(&**self, &**other)
    }
    #[inline]
    fn ge(&self, other: &Box<T>) -> bool {
        PartialOrd::ge(&**self, &**other)
    }
    #[inline]
    fn gt(&self, other: &Box<T>) -> bool {
        PartialOrd::gt(&**self, &**other)
    }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized + Ord> Ord for Box<T> {
    #[inline]
    fn cmp(&self, other: &Box<T>) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized + Eq> Eq for Box<T> {}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized + Hash> Hash for Box<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

#[stable(feature = "indirect_hasher_impl", since = "1.22.0")]
impl<T: ?Sized + Hasher> Hasher for Box<T> {
    fn finish(&self) -> u64 {
        (**self).finish()
    }
    fn write(&mut self, bytes: &[u8]) {
        (**self).write(bytes)
    }
    fn write_u8(&mut self, i: u8) {
        (**self).write_u8(i)
    }
    fn write_u16(&mut self, i: u16) {
        (**self).write_u16(i)
    }
    fn write_u32(&mut self, i: u32) {
        (**self).write_u32(i)
    }
    fn write_u64(&mut self, i: u64) {
        (**self).write_u64(i)
    }
    fn write_u128(&mut self, i: u128) {
        (**self).write_u128(i)
    }
    fn write_usize(&mut self, i: usize) {
        (**self).write_usize(i)
    }
    fn write_i8(&mut self, i: i8) {
        (**self).write_i8(i)
    }
    fn write_i16(&mut self, i: i16) {
        (**self).write_i16(i)
    }
    fn write_i32(&mut self, i: i32) {
        (**self).write_i32(i)
    }
    fn write_i64(&mut self, i: i64) {
        (**self).write_i64(i)
    }
    fn write_i128(&mut self, i: i128) {
        (**self).write_i128(i)
    }
    fn write_isize(&mut self, i: isize) {
        (**self).write_isize(i)
    }
}

#[stable(feature = "from_for_ptrs", since = "1.6.0")]
impl<T> From<T> for Box<T> {
    /// Converts a generic type `T` into a `Box<T>`
    ///
    /// The conversion allocates on the heap and moves `t`
    /// from the stack into it.
    ///
    /// # Examples
    /// ```rust
    /// let x = 5;
    /// let boxed = Box::new(5);
    ///
    /// assert_eq!(Box::from(x), boxed);
    /// ```
    fn from(t: T) -> Self {
        Box::new(t)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: fmt::Display + ?Sized> fmt::Display for Box<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: fmt::Debug + ?Sized> fmt::Debug for Box<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> fmt::Pointer for Box<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // It's not possible to extract the inner Uniq directly from the Box,
        // instead we cast it to a *const which aliases the Unique
        let ptr: *const T = &**self;
        fmt::Pointer::fmt(&ptr, f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> Deref for Box<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &**self
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> DerefMut for Box<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut **self
    }
}

#[unstable(feature = "receiver_trait", issue = "0")]
impl<T: ?Sized> Receiver for Box<T> {}

#[stable(feature = "rust1", since = "1.0.0")]
impl<I: Iterator + ?Sized> Iterator for Box<I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        (**self).next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (**self).size_hint()
    }
    fn nth(&mut self, n: usize) -> Option<I::Item> {
        (**self).nth(n)
    }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl<I: DoubleEndedIterator + ?Sized> DoubleEndedIterator for Box<I> {
    fn next_back(&mut self) -> Option<I::Item> {
        (**self).next_back()
    }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl<I: ExactSizeIterator + ?Sized> ExactSizeIterator for Box<I> {
    fn len(&self) -> usize {
        (**self).len()
    }
    fn is_empty(&self) -> bool {
        (**self).is_empty()
    }
}

#[stable(feature = "fused", since = "1.26.0")]
impl<I: FusedIterator + ?Sized> FusedIterator for Box<I> {}

#[stable(feature = "box_borrow", since = "1.1.0")]
impl<T: ?Sized> borrow::Borrow<T> for Box<T> {
    fn borrow(&self) -> &T {
        &**self
    }
}

#[stable(feature = "box_borrow", since = "1.1.0")]
impl<T: ?Sized> borrow::BorrowMut<T> for Box<T> {
    fn borrow_mut(&mut self) -> &mut T {
        &mut **self
    }
}

#[stable(since = "1.5.0", feature = "smart_ptr_as_ref")]
impl<T: ?Sized> AsRef<T> for Box<T> {
    fn as_ref(&self) -> &T {
        &**self
    }
}

#[stable(since = "1.5.0", feature = "smart_ptr_as_ref")]
impl<T: ?Sized> AsMut<T> for Box<T> {
    fn as_mut(&mut self) -> &mut T {
        &mut **self
    }
}
