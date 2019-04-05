//! A UTF-8 encoded, growable string.
//!
//! This module contains the [`String`] type, a trait for converting
//! [`ToString`]s, and several error types that may result from working with
//! [`String`]s.
//!
//! [`ToString`]: trait.ToString.html
//!
//! # Examples
//!
//! There are multiple ways to create a new [`String`] from a string literal:
//!
//! ```
//! let s = "Hello".to_string();
//!
//! let s = String::from("world");
//! let s: String = "also this".into();
//! ```
//!
//! You can create a new [`String`] from an existing one by concatenating with
//! `+`:
//!
//! [`String`]: struct.String.html
//!
//! ```
//! let s = "Hello".to_string();
//!
//! let message = s + " world!";
//! ```
//!
//! If you have a vector of valid UTF-8 bytes, you can make a [`String`] out of
//! it. You can do the reverse too.
//!
//! ```
//! let sparkle_heart = vec![240, 159, 146, 150];
//!
//! // We know these bytes are valid, so we'll use `unwrap()`.
//! let sparkle_heart = String::from_utf8(sparkle_heart).unwrap();
//!
//! assert_eq!("💖", sparkle_heart);
//!
//! let bytes = sparkle_heart.into_bytes();
//!
//! assert_eq!(bytes, [240, 159, 146, 150]);
//! ```

#![stable(feature = "rust1", since = "1.0.0")]

use core::char::{decode_utf16, REPLACEMENT_CHARACTER};
use core::fmt;
use core::hash;
use core::iter::{FromIterator, FusedIterator};
use core::ops::{self, Add, AddAssign, Index, IndexMut, RangeBounds};
use core::ops::Bound::{Excluded, Included, Unbounded};
use core::ptr;
use core::str::{self, pattern::Pattern, lossy};

use crate::boxed::Box;
use crate::vec::Vec;

/// A UTF-8 encoded, growable string.
///
/// The `String` type is the most common string type that has ownership over the
/// contents of the string. It has a close relationship with its borrowed
/// counterpart, the primitive [`str`].
///
/// [`str`]: ../../std/primitive.str.html
///
/// # Examples
///
/// You can create a `String` from a literal string with [`String::from`]:
///
/// ```
/// let hello = String::from("Hello, world!");
/// ```
///
/// You can append a [`char`] to a `String` with the [`push`] method, and
/// append a [`&str`] with the [`push_str`] method:
///
/// ```
/// let mut hello = String::from("Hello, ");
///
/// hello.push('w');
/// hello.push_str("orld!");
/// ```
///
/// [`String::from`]: #method.from
/// [`char`]: ../../std/primitive.char.html
/// [`push`]: #method.push
/// [`push_str`]: #method.push_str
///
/// If you have a vector of UTF-8 bytes, you can create a `String` from it with
/// the [`from_utf8`] method:
///
/// ```
/// // some bytes, in a vector
/// let sparkle_heart = vec![240, 159, 146, 150];
///
/// // We know these bytes are valid, so we'll use `unwrap()`.
/// let sparkle_heart = String::from_utf8(sparkle_heart).unwrap();
///
/// assert_eq!("💖", sparkle_heart);
/// ```
///
/// [`from_utf8`]: #method.from_utf8
///
/// # UTF-8
///
/// `String`s are always valid UTF-8. This has a few implications, the first of
/// which is that if you need a non-UTF-8 string, consider [`OsString`]. It is
/// similar, but without the UTF-8 constraint. The second implication is that
/// you cannot index into a `String`:
///
/// ```compile_fail,E0277
/// let s = "hello";
///
/// println!("The first letter of s is {}", s[0]); // ERROR!!!
/// ```
///
/// [`OsString`]: ../../std/ffi/struct.OsString.html
///
/// Indexing is intended to be a constant-time operation, but UTF-8 encoding
/// does not allow us to do this. Furthermore, it's not clear what sort of
/// thing the index should return: a byte, a codepoint, or a grapheme cluster.
/// The [`bytes`] and [`chars`] methods return iterators over the first
/// two, respectively.
///
/// [`bytes`]: #method.bytes
/// [`chars`]: #method.chars
///
/// # Deref
///
/// `String`s implement [`Deref`]`<Target=str>`, and so inherit all of [`str`]'s
/// methods. In addition, this means that you can pass a `String` to a
/// function which takes a [`&str`] by using an ampersand (`&`):
///
/// ```
/// fn takes_str(s: &str) { }
///
/// let s = String::from("Hello");
///
/// takes_str(&s);
/// ```
///
/// This will create a [`&str`] from the `String` and pass it in. This
/// conversion is very inexpensive, and so generally, functions will accept
/// [`&str`]s as arguments unless they need a `String` for some specific
/// reason.
///
/// In certain cases Rust doesn't have enough information to make this
/// conversion, known as [`Deref`] coercion. In the following example a string
/// slice [`&'a str`][`&str`] implements the trait `TraitExample`, and the function
/// `example_func` takes anything that implements the trait. In this case Rust
/// would need to make two implicit conversions, which Rust doesn't have the
/// means to do. For that reason, the following example will not compile.
///
/// ```compile_fail,E0277
/// trait TraitExample {}
///
/// impl<'a> TraitExample for &'a str {}
///
/// fn example_func<A: TraitExample>(example_arg: A) {}
///
/// fn main() {
///     let example_string = String::from("example_string");
///     example_func(&example_string);
/// }
/// ```
///
/// There are two options that would work instead. The first would be to
/// change the line `example_func(&example_string);` to
/// `example_func(example_string.as_str());`, using the method [`as_str()`]
/// to explicitly extract the string slice containing the string. The second
/// way changes `example_func(&example_string);` to
/// `example_func(&*example_string);`. In this case we are dereferencing a
/// `String` to a [`str`][`&str`], then referencing the [`str`][`&str`] back to
/// [`&str`]. The second way is more idiomatic, however both work to do the
/// conversion explicitly rather than relying on the implicit conversion.
///
/// # Representation
///
/// A `String` is made up of three components: a pointer to some bytes, a
/// length, and a capacity. The pointer points to an internal buffer `String`
/// uses to store its data. The length is the number of bytes currently stored
/// in the buffer, and the capacity is the size of the buffer in bytes. As such,
/// the length will always be less than or equal to the capacity.
///
/// This buffer is always stored on the heap.
///
/// You can look at these with the [`as_ptr`], [`len`], and [`capacity`]
/// methods:
///
/// ```
/// use std::mem;
///
/// let story = String::from("Once upon a time...");
///
/// let ptr = story.as_ptr();
/// let len = story.len();
/// let capacity = story.capacity();
///
/// // story has nineteen bytes
/// assert_eq!(19, len);
///
/// // Now that we have our parts, we throw the story away.
/// mem::forget(story);
///
/// // We can re-build a String out of ptr, len, and capacity. This is all
/// // unsafe because we are responsible for making sure the components are
/// // valid:
/// let s = unsafe { String::from_raw_parts(ptr as *mut _, len, capacity) } ;
///
/// assert_eq!(String::from("Once upon a time..."), s);
/// ```
///
/// [`as_ptr`]: #method.as_ptr
/// [`len`]: #method.len
/// [`capacity`]: #method.capacity
///
/// If a `String` has enough capacity, adding elements to it will not
/// re-allocate. For example, consider this program:
///
/// ```
/// let mut s = String::new();
///
/// println!("{}", s.capacity());
///
/// for _ in 0..5 {
///     s.push_str("hello");
///     println!("{}", s.capacity());
/// }
/// ```
///
/// This will output the following:
///
/// ```text
/// 0
/// 5
/// 10
/// 20
/// 20
/// 40
/// ```
///
/// At first, we have no memory allocated at all, but as we append to the
/// string, it increases its capacity appropriately. If we instead use the
/// [`with_capacity`] method to allocate the correct capacity initially:
///
/// ```
/// let mut s = String::with_capacity(25);
///
/// println!("{}", s.capacity());
///
/// for _ in 0..5 {
///     s.push_str("hello");
///     println!("{}", s.capacity());
/// }
/// ```
///
/// [`with_capacity`]: #method.with_capacity
///
/// We end up with a different output:
///
/// ```text
/// 25
/// 25
/// 25
/// 25
/// 25
/// 25
/// ```
///
/// Here, there's no need to allocate more memory inside the loop.
///
/// [`&str`]: ../../std/primitive.str.html
/// [`Deref`]: ../../std/ops/trait.Deref.html
/// [`as_str()`]: struct.String.html#method.as_str
#[derive(PartialOrd, Eq, Ord)]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct String {
    vec: Vec<u8>,
}

/// A possible error value when converting a `String` from a UTF-16 byte slice.
///
/// This type is the error type for the [`from_utf16`] method on [`String`].
///
/// [`from_utf16`]: struct.String.html#method.from_utf16
/// [`String`]: struct.String.html
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// // 𝄞mu<invalid>ic
/// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
///           0xD800, 0x0069, 0x0063];
///
/// assert!(String::from_utf16(v).is_err());
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
#[derive(Debug)]
pub struct FromUtf16Error(());

impl String {
    /// Creates a new empty `String`.
    ///
    /// Given that the `String` is empty, this will not allocate any initial
    /// buffer. While that means that this initial operation is very
    /// inexpensive, it may cause excessive allocation later when you add
    /// data. If you have an idea of how much data the `String` will hold,
    /// consider the [`with_capacity`] method to prevent excessive
    /// re-allocation.
    ///
    /// [`with_capacity`]: #method.with_capacity
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let s = String::new();
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_const_unstable(feature = "const_string_new")]
    pub const fn new() -> String {
        String { vec: Vec::new() }
    }

    /// Creates a new empty `String` with a particular capacity.
    ///
    /// `String`s have an internal buffer to hold their data. The capacity is
    /// the length of that buffer, and can be queried with the [`capacity`]
    /// method. This method creates an empty `String`, but one with an initial
    /// buffer that can hold `capacity` bytes. This is useful when you may be
    /// appending a bunch of data to the `String`, reducing the number of
    /// reallocations it needs to do.
    ///
    /// [`capacity`]: #method.capacity
    ///
    /// If the given capacity is `0`, no allocation will occur, and this method
    /// is identical to the [`new`] method.
    ///
    /// [`new`]: #method.new
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::with_capacity(10);
    ///
    /// // The String contains no chars, even though it has capacity for more
    /// assert_eq!(s.len(), 0);
    ///
    /// // These are all done without reallocating...
    /// let cap = s.capacity();
    /// for _ in 0..10 {
    ///     s.push('a');
    /// }
    ///
    /// assert_eq!(s.capacity(), cap);
    ///
    /// // ...but this may make the vector reallocate
    /// s.push('a');
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn with_capacity(capacity: usize) -> String {
        String { vec: Vec::with_capacity(capacity) }
    }

    // HACK(japaric): with cfg(test) the inherent `[T]::to_vec` method, which is
    // required for this method definition, is not available. Since we don't
    // require this method for testing purposes, I'll just stub it
    // NB see the slice::hack module in slice.rs for more information
    #[inline]
    #[cfg(test)]
    pub fn from_str(_: &str) -> String {
        panic!("not available with cfg(test)");
    }

    /// Decode a UTF-16 encoded vector `v` into a `String`, returning [`Err`]
    /// if `v` contains any invalid data.
    ///
    /// [`Err`]: ../../std/result/enum.Result.html#variant.Err
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // 𝄞music
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
    ///           0x0073, 0x0069, 0x0063];
    /// assert_eq!(String::from("𝄞music"),
    ///            String::from_utf16(v).unwrap());
    ///
    /// // 𝄞mu<invalid>ic
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
    ///           0xD800, 0x0069, 0x0063];
    /// assert!(String::from_utf16(v).is_err());
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn from_utf16(v: &[u16]) -> Result<String, FromUtf16Error> {
        // This isn't done via collect::<Result<_, _>>() for performance reasons.
        // FIXME: the function can be simplified again when #48994 is closed.
        let mut ret = String::with_capacity(v.len());
        for c in decode_utf16(v.iter().cloned()) {
            if let Ok(c) = c {
                ret.push(c);
            } else {
                return Err(FromUtf16Error(()));
            }
        }
        Ok(ret)
    }

    /// Decode a UTF-16 encoded slice `v` into a `String`, replacing
    /// invalid data with [the replacement character (`U+FFFD`)][U+FFFD].
    ///
    /// Unlike [`from_utf8_lossy`] which returns a [`Cow<'a, str>`],
    /// `from_utf16_lossy` returns a `String` since the UTF-16 to UTF-8
    /// conversion requires a memory allocation.
    ///
    /// [`from_utf8_lossy`]: #method.from_utf8_lossy
    /// [`Cow<'a, str>`]: ../borrow/enum.Cow.html
    /// [U+FFFD]: ../char/constant.REPLACEMENT_CHARACTER.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // 𝄞mus<invalid>ic<invalid>
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
    ///           0x0073, 0xDD1E, 0x0069, 0x0063,
    ///           0xD834];
    ///
    /// assert_eq!(String::from("𝄞mus\u{FFFD}ic\u{FFFD}"),
    ///            String::from_utf16_lossy(v));
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn from_utf16_lossy(v: &[u16]) -> String {
        decode_utf16(v.iter().cloned()).map(|r| r.unwrap_or(REPLACEMENT_CHARACTER)).collect()
    }

    /// Creates a new `String` from a length, capacity, and pointer.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked:
    ///
    /// * The memory at `ptr` needs to have been previously allocated by the
    ///   same allocator the standard library uses.
    /// * `length` needs to be less than or equal to `capacity`.
    /// * `capacity` needs to be the correct value.
    ///
    /// Violating these may cause problems like corrupting the allocator's
    /// internal data structures.
    ///
    /// The ownership of `ptr` is effectively transferred to the
    /// `String` which may then deallocate, reallocate or change the
    /// contents of memory pointed to by the pointer at will. Ensure
    /// that nothing else uses the pointer after calling this
    /// function.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::mem;
    ///
    /// unsafe {
    ///     let s = String::from("hello");
    ///     let ptr = s.as_ptr();
    ///     let len = s.len();
    ///     let capacity = s.capacity();
    ///
    ///     mem::forget(s);
    ///
    ///     let s = String::from_raw_parts(ptr as *mut _, len, capacity);
    ///
    ///     assert_eq!(String::from("hello"), s);
    /// }
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub unsafe fn from_raw_parts(buf: *mut u8, length: usize, capacity: usize) -> String {
        String { vec: Vec::from_raw_parts(buf, length, capacity) }
    }

    /// Converts a vector of bytes to a `String` without checking that the
    /// string contains valid UTF-8.
    ///
    /// See the safe version, [`from_utf8`], for more details.
    ///
    /// [`from_utf8`]: struct.String.html#method.from_utf8
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the bytes passed
    /// to it are valid UTF-8. If this constraint is violated, it may cause
    /// memory unsafety issues with future users of the `String`, as the rest of
    /// the standard library assumes that `String`s are valid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // some bytes, in a vector
    /// let sparkle_heart = vec![240, 159, 146, 150];
    ///
    /// let sparkle_heart = unsafe {
    ///     String::from_utf8_unchecked(sparkle_heart)
    /// };
    ///
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub unsafe fn from_utf8_unchecked(bytes: Vec<u8>) -> String {
        String { vec: bytes }
    }

    /// Converts a `String` into a byte vector.
    ///
    /// This consumes the `String`, so we do not need to copy its contents.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let s = String::from("hello");
    /// let bytes = s.into_bytes();
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111][..], &bytes[..]);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn into_bytes(self) -> Vec<u8> {
        self.vec
    }

    /// Extracts a string slice containing the entire `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let s = String::from("foo");
    ///
    /// assert_eq!("foo", s.as_str());
    /// ```
    #[inline]
    #[stable(feature = "string_as_str", since = "1.7.0")]
    pub fn as_str(&self) -> &str {
        self
    }

    /// Converts a `String` into a mutable string slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::from("foobar");
    /// let s_mut_str = s.as_mut_str();
    ///
    /// s_mut_str.make_ascii_uppercase();
    ///
    /// assert_eq!("FOOBAR", s_mut_str);
    /// ```
    #[inline]
    #[stable(feature = "string_as_str", since = "1.7.0")]
    pub fn as_mut_str(&mut self) -> &mut str {
        self
    }

    /// Appends a given string slice onto the end of this `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::from("foo");
    ///
    /// s.push_str("bar");
    ///
    /// assert_eq!("foobar", s);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn push_str(&mut self, string: &str) {
        self.vec.extend_from_slice(string.as_bytes())
    }

    /// Returns this `String`'s capacity, in bytes.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let s = String::with_capacity(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn capacity(&self) -> usize {
        self.vec.capacity()
    }

    /// Ensures that this `String`'s capacity is at least `additional` bytes
    /// larger than its length.
    ///
    /// The capacity may be increased by more than `additional` bytes if it
    /// chooses, to prevent frequent reallocations.
    ///
    /// If you do not want this "at least" behavior, see the [`reserve_exact`]
    /// method.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows [`usize`].
    ///
    /// [`reserve_exact`]: struct.String.html#method.reserve_exact
    /// [`usize`]: ../../std/primitive.usize.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::new();
    ///
    /// s.reserve(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    ///
    /// This may not actually increase the capacity:
    ///
    /// ```
    /// let mut s = String::with_capacity(10);
    /// s.push('a');
    /// s.push('b');
    ///
    /// // s now has a length of 2 and a capacity of 10
    /// assert_eq!(2, s.len());
    /// assert_eq!(10, s.capacity());
    ///
    /// // Since we already have an extra 8 capacity, calling this...
    /// s.reserve(8);
    ///
    /// // ... doesn't actually increase.
    /// assert_eq!(10, s.capacity());
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn reserve(&mut self, additional: usize) {
        self.vec.reserve(additional)
    }

    /// Ensures that this `String`'s capacity is `additional` bytes
    /// larger than its length.
    ///
    /// Consider using the [`reserve`] method unless you absolutely know
    /// better than the allocator.
    ///
    /// [`reserve`]: #method.reserve
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::new();
    ///
    /// s.reserve_exact(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    ///
    /// This may not actually increase the capacity:
    ///
    /// ```
    /// let mut s = String::with_capacity(10);
    /// s.push('a');
    /// s.push('b');
    ///
    /// // s now has a length of 2 and a capacity of 10
    /// assert_eq!(2, s.len());
    /// assert_eq!(10, s.capacity());
    ///
    /// // Since we already have an extra 8 capacity, calling this...
    /// s.reserve_exact(8);
    ///
    /// // ... doesn't actually increase.
    /// assert_eq!(10, s.capacity());
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.vec.reserve_exact(additional)
    }

    /// Shrinks the capacity of this `String` to match its length.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::from("foo");
    ///
    /// s.reserve(100);
    /// assert!(s.capacity() >= 100);
    ///
    /// s.shrink_to_fit();
    /// assert_eq!(3, s.capacity());
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn shrink_to_fit(&mut self) {
        self.vec.shrink_to_fit()
    }

    /// Shrinks the capacity of this `String` with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length
    /// and the supplied value.
    ///
    /// Panics if the current capacity is smaller than the supplied
    /// minimum capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(shrink_to)]
    /// let mut s = String::from("foo");
    ///
    /// s.reserve(100);
    /// assert!(s.capacity() >= 100);
    ///
    /// s.shrink_to(10);
    /// assert!(s.capacity() >= 10);
    /// s.shrink_to(0);
    /// assert!(s.capacity() >= 3);
    /// ```
    #[inline]
    #[unstable(feature = "shrink_to", reason = "new API", issue="56431")]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.vec.shrink_to(min_capacity)
    }

    /// Appends the given [`char`] to the end of this `String`.
    ///
    /// [`char`]: ../../std/primitive.char.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::from("abc");
    ///
    /// s.push('1');
    /// s.push('2');
    /// s.push('3');
    ///
    /// assert_eq!("abc123", s);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn push(&mut self, ch: char) {
        match ch.len_utf8() {
            1 => self.vec.push(ch as u8),
            _ => self.vec.extend_from_slice(ch.encode_utf8(&mut [0; 4]).as_bytes()),
        }
    }

    /// Returns a byte slice of this `String`'s contents.
    ///
    /// The inverse of this method is [`from_utf8`].
    ///
    /// [`from_utf8`]: #method.from_utf8
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let s = String::from("hello");
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn as_bytes(&self) -> &[u8] {
        &self.vec
    }

    /// Shortens this `String` to the specified length.
    ///
    /// If `new_len` is greater than the string's current length, this has no
    /// effect.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the string
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a [`char`] boundary.
    ///
    /// [`char`]: ../../std/primitive.char.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::from("hello");
    ///
    /// s.truncate(2);
    ///
    /// assert_eq!("he", s);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len));
            self.vec.truncate(new_len)
        }
    }

    /// Removes the last character from the string buffer and returns it.
    ///
    /// Returns [`None`] if this `String` is empty.
    ///
    /// [`None`]: ../../std/option/enum.Option.html#variant.None
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::from("foo");
    ///
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('f'));
    ///
    /// assert_eq!(s.pop(), None);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().rev().next()?;
        let newlen = self.len() - ch.len_utf8();
        unsafe {
            self.vec.set_len(newlen);
        }
        Some(ch)
    }

    /// Removes a [`char`] from this `String` at a byte position and returns it.
    ///
    /// This is an `O(n)` operation, as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than or equal to the `String`'s length,
    /// or if it does not lie on a [`char`] boundary.
    ///
    /// [`char`]: ../../std/primitive.char.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::from("foo");
    ///
    /// assert_eq!(s.remove(0), 'f');
    /// assert_eq!(s.remove(1), 'o');
    /// assert_eq!(s.remove(0), 'o');
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn remove(&mut self, idx: usize) -> char {
        let ch = match self[idx..].chars().next() {
            Some(ch) => ch,
            None => panic!("cannot remove a char from the end of a string"),
        };

        let next = idx + ch.len_utf8();
        let len = self.len();
        unsafe {
            ptr::copy(self.vec.as_ptr().add(next),
                      self.vec.as_mut_ptr().add(idx),
                      len - next);
            self.vec.set_len(len - (next - idx));
        }
        ch
    }

    /// Retains only the characters specified by the predicate.
    ///
    /// In other words, remove all characters `c` such that `f(c)` returns `false`.
    /// This method operates in place and preserves the order of the retained
    /// characters.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("f_o_ob_ar");
    ///
    /// s.retain(|c| c != '_');
    ///
    /// assert_eq!(s, "foobar");
    /// ```
    #[inline]
    #[stable(feature = "string_retain", since = "1.26.0")]
    pub fn retain<F>(&mut self, mut f: F)
        where F: FnMut(char) -> bool
    {
        let len = self.len();
        let mut del_bytes = 0;
        let mut idx = 0;

        while idx < len {
            let ch = unsafe {
                self.get_unchecked(idx..len).chars().next().unwrap()
            };
            let ch_len = ch.len_utf8();

            if !f(ch) {
                del_bytes += ch_len;
            } else if del_bytes > 0 {
                unsafe {
                    ptr::copy(self.vec.as_ptr().add(idx),
                              self.vec.as_mut_ptr().add(idx - del_bytes),
                              ch_len);
                }
            }

            // Point idx to the next char
            idx += ch_len;
        }

        if del_bytes > 0 {
            unsafe { self.vec.set_len(len - del_bytes); }
        }
    }

    /// Inserts a character into this `String` at a byte position.
    ///
    /// This is an `O(n)` operation as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `String`'s length, or if it does not
    /// lie on a [`char`] boundary.
    ///
    /// [`char`]: ../../std/primitive.char.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::with_capacity(3);
    ///
    /// s.insert(0, 'f');
    /// s.insert(1, 'o');
    /// s.insert(2, 'o');
    ///
    /// assert_eq!("foo", s);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn insert(&mut self, idx: usize, ch: char) {
        assert!(self.is_char_boundary(idx));
        let mut bits = [0; 4];
        let bits = ch.encode_utf8(&mut bits).as_bytes();

        unsafe {
            self.insert_bytes(idx, bits);
        }
    }

    unsafe fn insert_bytes(&mut self, idx: usize, bytes: &[u8]) {
        let len = self.len();
        let amt = bytes.len();
        self.vec.reserve(amt);

        ptr::copy(self.vec.as_ptr().add(idx),
                  self.vec.as_mut_ptr().add(idx + amt),
                  len - idx);
        ptr::copy(bytes.as_ptr(),
                  self.vec.as_mut_ptr().add(idx),
                  amt);
        self.vec.set_len(len + amt);
    }

    /// Inserts a string slice into this `String` at a byte position.
    ///
    /// This is an `O(n)` operation as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `String`'s length, or if it does not
    /// lie on a [`char`] boundary.
    ///
    /// [`char`]: ../../std/primitive.char.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::from("bar");
    ///
    /// s.insert_str(0, "foo");
    ///
    /// assert_eq!("foobar", s);
    /// ```
    #[inline]
    #[stable(feature = "insert_str", since = "1.16.0")]
    pub fn insert_str(&mut self, idx: usize, string: &str) {
        assert!(self.is_char_boundary(idx));

        unsafe {
            self.insert_bytes(idx, string.as_bytes());
        }
    }

    /// Returns a mutable reference to the contents of this `String`.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the bytes passed
    /// to it are valid UTF-8. If this constraint is violated, it may cause
    /// memory unsafety issues with future users of the `String`, as the rest of
    /// the standard library assumes that `String`s are valid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::from("hello");
    ///
    /// unsafe {
    ///     let vec = s.as_mut_vec();
    ///     assert_eq!(&[104, 101, 108, 108, 111][..], &vec[..]);
    ///
    ///     vec.reverse();
    /// }
    /// assert_eq!(s, "olleh");
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub unsafe fn as_mut_vec(&mut self) -> &mut Vec<u8> {
        &mut self.vec
    }

    /// Returns the length of this `String`, in bytes.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let a = String::from("foo");
    ///
    /// assert_eq!(a.len(), 3);
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn len(&self) -> usize {
        self.vec.len()
    }

    /// Returns `true` if this `String` has a length of zero, and `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut v = String::new();
    /// assert!(v.is_empty());
    ///
    /// v.push('a');
    /// assert!(!v.is_empty());
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Splits the string into two at the given index.
    ///
    /// Returns a newly allocated `String`. `self` contains bytes `[0, at)`, and
    /// the returned `String` contains bytes `[at, len)`. `at` must be on the
    /// boundary of a UTF-8 code point.
    ///
    /// Note that the capacity of `self` does not change.
    ///
    /// # Panics
    ///
    /// Panics if `at` is not on a `UTF-8` code point boundary, or if it is beyond the last
    /// code point of the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() {
    /// let mut hello = String::from("Hello, World!");
    /// let world = hello.split_off(7);
    /// assert_eq!(hello, "Hello, ");
    /// assert_eq!(world, "World!");
    /// # }
    /// ```
    #[inline]
    #[stable(feature = "string_split_off", since = "1.16.0")]
    pub fn split_off(&mut self, at: usize) -> String {
        assert!(self.is_char_boundary(at));
        let other = self.vec.split_off(at);
        unsafe { String::from_utf8_unchecked(other) }
    }

    /// Truncates this `String`, removing all contents.
    ///
    /// While this means the `String` will have a length of zero, it does not
    /// touch its capacity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::from("foo");
    ///
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(0, s.len());
    /// assert_eq!(3, s.capacity());
    /// ```
    #[inline]
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn clear(&mut self) {
        self.vec.clear()
    }

    /// Removes the specified range in the string,
    /// and replaces it with the given string.
    /// The given string doesn't need to be the same length as the range.
    ///
    /// # Panics
    ///
    /// Panics if the starting point or end point do not lie on a [`char`]
    /// boundary, or if they're out of bounds.
    ///
    /// [`char`]: ../../std/primitive.char.html
    /// [`Vec::splice`]: ../../std/vec/struct.Vec.html#method.splice
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::from("α is alpha, β is beta");
    /// let beta_offset = s.find('β').unwrap_or(s.len());
    ///
    /// // Replace the range up until the β from the string
    /// s.replace_range(..beta_offset, "Α is capital alpha; ");
    /// assert_eq!(s, "Α is capital alpha; β is beta");
    /// ```
    #[stable(feature = "splice", since = "1.27.0")]
    pub fn replace_range<R>(&mut self, range: R, replace_with: &str)
        where R: RangeBounds<usize>
    {
        // Memory safety
        //
        // Replace_range does not have the memory safety issues of a vector Splice.
        // of the vector version. The data is just plain bytes.

        match range.start_bound() {
             Included(&n) => assert!(self.is_char_boundary(n)),
             Excluded(&n) => assert!(self.is_char_boundary(n + 1)),
             Unbounded => {},
        };
        match range.end_bound() {
             Included(&n) => assert!(self.is_char_boundary(n + 1)),
             Excluded(&n) => assert!(self.is_char_boundary(n)),
             Unbounded => {},
        };

        unsafe {
            self.as_mut_vec()
        }.splice(range, replace_with.bytes());
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl fmt::Display for FromUtf16Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt("invalid utf-16: lone surrogate found", f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl FromIterator<char> for String {
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> String {
        let mut buf = String::new();
        buf.extend(iter);
        buf
    }
}

#[stable(feature = "string_from_iter_by_ref", since = "1.17.0")]
impl<'a> FromIterator<&'a char> for String {
    fn from_iter<I: IntoIterator<Item = &'a char>>(iter: I) -> String {
        let mut buf = String::new();
        buf.extend(iter);
        buf
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a> FromIterator<&'a str> for String {
    fn from_iter<I: IntoIterator<Item = &'a str>>(iter: I) -> String {
        let mut buf = String::new();
        buf.extend(iter);
        buf
    }
}

#[stable(feature = "extend_string", since = "1.4.0")]
impl FromIterator<String> for String {
    fn from_iter<I: IntoIterator<Item = String>>(iter: I) -> String {
        let mut iterator = iter.into_iter();

        // Because we're iterating over `String`s, we can avoid at least
        // one allocation by getting the first string from the iterator
        // and appending to it all the subsequent strings.
        match iterator.next() {
            None => String::new(),
            Some(mut buf) => {
                buf.extend(iterator);
                buf
            }
        }
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl Extend<char> for String {
    fn extend<I: IntoIterator<Item = char>>(&mut self, iter: I) {
        let iterator = iter.into_iter();
        let (lower_bound, _) = iterator.size_hint();
        self.reserve(lower_bound);
        iterator.for_each(move |c| self.push(c));
    }
}

#[stable(feature = "extend_ref", since = "1.2.0")]
impl<'a> Extend<&'a char> for String {
    fn extend<I: IntoIterator<Item = &'a char>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<'a> Extend<&'a str> for String {
    fn extend<I: IntoIterator<Item = &'a str>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(s));
    }
}

#[stable(feature = "extend_string", since = "1.4.0")]
impl Extend<String> for String {
    fn extend<I: IntoIterator<Item = String>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }
}

/// A convenience impl that delegates to the impl for `&str`
#[unstable(feature = "pattern",
           reason = "API not fully fleshed out and ready to be stabilized",
           issue = "27721")]
impl<'a, 'b> Pattern<'a> for &'b String {
    type Searcher = <&'b str as Pattern<'a>>::Searcher;

    fn into_searcher(self, haystack: &'a str) -> <&'b str as Pattern<'a>>::Searcher {
        self[..].into_searcher(haystack)
    }

    #[inline]
    fn is_contained_in(self, haystack: &'a str) -> bool {
        self[..].is_contained_in(haystack)
    }

    #[inline]
    fn is_prefix_of(self, haystack: &'a str) -> bool {
        self[..].is_prefix_of(haystack)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl PartialEq for String {
    #[inline]
    fn eq(&self, other: &String) -> bool {
        PartialEq::eq(&self[..], &other[..])
    }
    #[inline]
    fn ne(&self, other: &String) -> bool {
        PartialEq::ne(&self[..], &other[..])
    }
}

macro_rules! impl_eq {
    ($lhs:ty, $rhs: ty) => {
        #[stable(feature = "rust1", since = "1.0.0")]
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool { PartialEq::eq(&self[..], &other[..]) }
            #[inline]
            fn ne(&self, other: &$rhs) -> bool { PartialEq::ne(&self[..], &other[..]) }
        }

        #[stable(feature = "rust1", since = "1.0.0")]
        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool { PartialEq::eq(&self[..], &other[..]) }
            #[inline]
            fn ne(&self, other: &$lhs) -> bool { PartialEq::ne(&self[..], &other[..]) }
        }

    }
}

impl_eq! { String, str }
impl_eq! { String, &'a str }

#[stable(feature = "rust1", since = "1.0.0")]
impl Default for String {
    /// Creates an empty `String`.
    #[inline]
    fn default() -> String {
        String::new()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl fmt::Display for String {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl fmt::Debug for String {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl hash::Hash for String {
    #[inline]
    fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
        (**self).hash(hasher)
    }
}

/// Implements the `+` operator for concatenating two strings.
///
/// This consumes the `String` on the left-hand side and re-uses its buffer (growing it if
/// necessary). This is done to avoid allocating a new `String` and copying the entire contents on
/// every operation, which would lead to `O(n^2)` running time when building an `n`-byte string by
/// repeated concatenation.
///
/// The string on the right-hand side is only borrowed; its contents are copied into the returned
/// `String`.
///
/// # Examples
///
/// Concatenating two `String`s takes the first by value and borrows the second:
///
/// ```
/// let a = String::from("hello");
/// let b = String::from(" world");
/// let c = a + &b;
/// // `a` is moved and can no longer be used here.
/// ```
///
/// If you want to keep using the first `String`, you can clone it and append to the clone instead:
///
/// ```
/// let a = String::from("hello");
/// let b = String::from(" world");
/// let c = a.clone() + &b;
/// // `a` is still valid here.
/// ```
///
/// Concatenating `&str` slices can be done by converting the first to a `String`:
///
/// ```
/// let a = "hello";
/// let b = " world";
/// let c = a.to_string() + b;
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
impl Add<&str> for String {
    type Output = String;

    #[inline]
    fn add(mut self, other: &str) -> String {
        self.push_str(other);
        self
    }
}

/// Implements the `+=` operator for appending to a `String`.
///
/// This has the same behavior as the [`push_str`][String::push_str] method.
#[stable(feature = "stringaddassign", since = "1.12.0")]
impl AddAssign<&str> for String {
    #[inline]
    fn add_assign(&mut self, other: &str) {
        self.push_str(other);
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl ops::Index<ops::Range<usize>> for String {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::Range<usize>) -> &str {
        &self[..][index]
    }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl ops::Index<ops::RangeTo<usize>> for String {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeTo<usize>) -> &str {
        &self[..][index]
    }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl ops::Index<ops::RangeFrom<usize>> for String {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeFrom<usize>) -> &str {
        &self[..][index]
    }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl ops::Index<ops::RangeFull> for String {
    type Output = str;

    #[inline]
    fn index(&self, _index: ops::RangeFull) -> &str {
        unsafe { str::from_utf8_unchecked(&self.vec) }
    }
}
#[stable(feature = "inclusive_range", since = "1.26.0")]
impl ops::Index<ops::RangeInclusive<usize>> for String {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeInclusive<usize>) -> &str {
        Index::index(&**self, index)
    }
}
#[stable(feature = "inclusive_range", since = "1.26.0")]
impl ops::Index<ops::RangeToInclusive<usize>> for String {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeToInclusive<usize>) -> &str {
        Index::index(&**self, index)
    }
}

#[stable(feature = "derefmut_for_string", since = "1.3.0")]
impl ops::IndexMut<ops::Range<usize>> for String {
    #[inline]
    fn index_mut(&mut self, index: ops::Range<usize>) -> &mut str {
        &mut self[..][index]
    }
}
#[stable(feature = "derefmut_for_string", since = "1.3.0")]
impl ops::IndexMut<ops::RangeTo<usize>> for String {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeTo<usize>) -> &mut str {
        &mut self[..][index]
    }
}
#[stable(feature = "derefmut_for_string", since = "1.3.0")]
impl ops::IndexMut<ops::RangeFrom<usize>> for String {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeFrom<usize>) -> &mut str {
        &mut self[..][index]
    }
}
#[stable(feature = "derefmut_for_string", since = "1.3.0")]
impl ops::IndexMut<ops::RangeFull> for String {
    #[inline]
    fn index_mut(&mut self, _index: ops::RangeFull) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(&mut *self.vec) }
    }
}
#[stable(feature = "inclusive_range", since = "1.26.0")]
impl ops::IndexMut<ops::RangeInclusive<usize>> for String {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeInclusive<usize>) -> &mut str {
        IndexMut::index_mut(&mut **self, index)
    }
}
#[stable(feature = "inclusive_range", since = "1.26.0")]
impl ops::IndexMut<ops::RangeToInclusive<usize>> for String {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeToInclusive<usize>) -> &mut str {
        IndexMut::index_mut(&mut **self, index)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl ops::Deref for String {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        unsafe { str::from_utf8_unchecked(&self.vec) }
    }
}

#[stable(feature = "derefmut_for_string", since = "1.3.0")]
impl ops::DerefMut for String {
    #[inline]
    fn deref_mut(&mut self) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(&mut *self.vec) }
    }
}

/// An error when parsing a `String`.
///
/// This `enum` is slightly awkward: it will never actually exist. This error is
/// part of the type signature of the implementation of [`FromStr`] on
/// [`String`]. The return type of [`from_str`], requires that an error be
/// defined, but, given that a [`String`] can always be made into a new
/// [`String`] without error, this type will never actually be returned. As
/// such, it is only here to satisfy said signature, and is useless otherwise.
///
/// [`FromStr`]: ../../std/str/trait.FromStr.html
/// [`String`]: struct.String.html
/// [`from_str`]: ../../std/str/trait.FromStr.html#tymethod.from_str
#[stable(feature = "str_parse_error", since = "1.5.0")]
pub type ParseError = core::convert::Infallible;


/// A trait for converting a value to a `String`.
///
/// This trait is automatically implemented for any type which implements the
/// [`Display`] trait. As such, `ToString` shouldn't be implemented directly:
/// [`Display`] should be implemented instead, and you get the `ToString`
/// implementation for free.
///
/// [`Display`]: ../../std/fmt/trait.Display.html
#[stable(feature = "rust1", since = "1.0.0")]
pub trait ToString {
    /// Converts the given value to a `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let i = 5;
    /// let five = String::from("5");
    ///
    /// assert_eq!(five, i.to_string());
    /// ```
    #[rustc_conversion_suggestion]
    #[stable(feature = "rust1", since = "1.0.0")]
    fn to_string(&self) -> String;
}

/// # Panics
///
/// In this implementation, the `to_string` method panics
/// if the `Display` implementation returns an error.
/// This indicates an incorrect `Display` implementation
/// since `fmt::Write for String` never returns an error itself.
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: fmt::Display + ?Sized> ToString for T {
    #[inline]
    default fn to_string(&self) -> String {
        use fmt::Write;
        let mut buf = String::new();
        buf.write_fmt(format_args!("{}", self))
           .expect("a Display implementation returned an error unexpectedly");
        buf.shrink_to_fit();
        buf
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl AsRef<str> for String {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl AsRef<[u8]> for String {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

#[stable(feature = "from_string_for_vec_u8", since = "1.14.0")]
impl From<String> for Vec<u8> {
    /// Converts the given `String` to a vector `Vec` that holds values of type `u8`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let s1 = String::from("hello world");
    /// let v1 = Vec::from(s1);
    ///
    /// for b in v1 {
    ///     println!("{}", b);
    /// }
    /// ```
    fn from(string: String) -> Vec<u8> {
        string.into_bytes()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl fmt::Write for String {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.push_str(s);
        Ok(())
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
        self.push(c);
        Ok(())
    }
}
