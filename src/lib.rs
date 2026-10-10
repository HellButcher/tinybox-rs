#![no_std]
#![doc = include_str!("../README.md")]
#![cfg_attr(feature = "unstable", feature(set_ptr_value, unsize))]
#![cfg_attr(all(test, feature = "unstable"), feature(ptr_metadata))]

extern crate alloc;

#[cfg(test)]
extern crate std;

use core::{
    alloc::Layout,
    any, borrow, cmp,
    error::Error,
    fmt, hash,
    mem::{self, MaybeUninit},
    ops, pin, ptr, task,
};

/// A [`Box`]-Like type that stores values inline when they fit, and in a heap allocation otherwise.
///
/// `TinyBoxSized` is a generic smart pointer that embeds a configurable amount of inline
/// storage. The effective capacity is `(S + 1) * sizeof(usize)` bytes — the `[usize; S]`
/// buffer plus one word used for the address/data portion of the pointer itself when the
/// value is small enough to fit inline. Values whose size and alignment fit within that
/// buffer are stored directly inside the struct with no heap allocation. Larger values are
/// allocated on the heap behind a fat pointer, while the struct still contains only the
/// data pointer and metadata.
///
/// The const generic `S` controls the inline storage capacity (in additional pointer-sized
/// words beyond the one consumed by the pointer's address bits). Use [`TinyBox`] for zero
/// inline space (`S=0`), or pick a larger `S` to favour slightly bigger types that still fit inline.
pub struct TinyBoxSized<T: ?Sized, const S: usize>([usize; S], *mut T);

/// A [`TinyBoxSized`] with zero inline storage (`S=0`).
pub type TinyBox<T> = TinyBoxSized<T, 0>;

const PTR_SIZE: usize = size_of::<*mut usize>();
const PTR_ALIGN: usize = align_of::<*mut usize>();

#[doc(hidden)]
pub use core::mem::forget as __forget;

#[inline]
fn ptr_with_metadata_of<T: ?Sized, U: ?Sized>(ptr: *const T, meta: *const U) -> *const U {
    #[cfg(not(feature = "unstable"))]
    {
        // workaround for missing `with_metadata_of` in stable Rust
        #[repr(C)]
        union PtrMetaHack<U: ?Sized> {
            thin: *const (),
            fat: *const U,
        }
        // initialize the fat pointer (but with wrong provenance)
        let mut tmp = PtrMetaHack {
            fat: meta.with_addr(ptr.addr()),
        };
        // override the thin pointer part (incuding the correct provenance)
        tmp.thin = ptr.cast();
        // return the fat pointer (now with correct provenance)
        // SAFETY: The fat pointer is initialized with the correct metadata and provenance, so it is safe to return it.
        unsafe { tmp.fat }
    }
    #[cfg(feature = "unstable")]
    {
        ptr.with_metadata_of(meta)
    }
}
#[inline]
fn ptr_mut_with_metadata_of<T: ?Sized, U: ?Sized>(ptr: *mut T, meta: *mut U) -> *mut U {
    #[cfg(not(feature = "unstable"))]
    {
        // workaround for missing `with_metadata_of` in stable Rust
        #[repr(C)]
        union PtrMetaHack<U: ?Sized> {
            thin: *mut (),
            fat: *mut U,
        }
        // initialize the fat pointer (but with wrong provenance)
        let mut tmp = PtrMetaHack {
            fat: meta.with_addr(ptr.addr()),
        };
        // override the thin pointer part (incuding the correct provenance)
        tmp.thin = ptr.cast();
        // return the fat pointer (now with correct provenance)
        // SAFETY: The fat pointer is initialized with the correct metadata and provenance, so it is safe to return it.
        unsafe { tmp.fat }
    }
    #[cfg(feature = "unstable")]
    {
        ptr.with_metadata_of(meta)
    }
}

/// Creates a [`TinyBox`] or [`TinyBoxSized`] from an expression, optionally casting/coercing the inner type.
///
/// This is a convenience macro for constructing tiny boxes and coercing, primarily used with trait
/// objects (e.g. `dyn Any`).
///
/// # Syntax
///
/// - `tinybox!(expr)` — default [`TinyBox`] (zero inline space).
/// - `tinybox!(Type => expr)` — casts the inner pointer to `Type`.
/// - `tinybox!(Type, S => expr)` — full form with explicit type and additional inline size `S`.
///
/// # Example
///
/// ```
/// # use tinybox::tinybox;
/// let boxed = tinybox!(123usize);
/// assert_eq!(*boxed, 123);
///
/// let any_box: tinybox::TinyBox<dyn core::any::Any> = tinybox!(dyn core::any::Any => 42i32);
/// assert!(any_box.is::<i32>());
/// ```
#[macro_export]
macro_rules! tinybox {
    ($t:ty, $s:expr => $e:expr) => {{
        let mut __val = $crate::TinyBoxSized::<_,  $s>::new($e);
        // SAFETY: This only used regular pointer coercion.
        unsafe {
            __val.__map_ptr_unchecked(|ptr| {
                let coerced: *mut $t = ptr;
                coerced
            })
        }
    }};
    ($t:ty => $e:expr; $s:expr) => {
        // old syntax, kept for backwards compatibility
        tinybox!($t, $s => $e)
    };
    ($t:ty => $e:expr) => {
        tinybox!($t, 0 => $e)
    };
    ($e:expr; $s:expr) => {
        // old syntax, kept for backwards compatibility
        tinybox!(_, $s => $e)
    };
    ($e:expr) => {
        tinybox!(_, 0 => $e)
    };
}

impl<T: ?Sized, const S: usize> TinyBoxSized<T, S> {
    /// # Safety
    /// Behavior is undefined if any of the following conditions are violated:
    /// * `src` must be [valid] for reads.
    /// * `src` must be properly aligned.
    /// * `src` must point to a properly initialized value of type `T`.
    /// * the value at `src` must not be used or dropped after `read_raw` is called.
    ///
    /// Like [`ptr::read`], `read_raw` creates a bitwise copy of `T`, regardless of
    /// whether `T` is [`Copy`]. If `T` is not [`Copy`], using the value at
    /// `*src` after calling `read_raw` can violate memory safety. This also
    /// applies for dropping dte value at `src`. It is recommended, that
    /// [`mem::forget`] is called on the value at `src`.
    ///
    /// Note that even if `T` has size `0`, the pointer must be non-null and properly aligned.
    ///
    /// [`ptr::read`]: std::ptr::read
    /// [`mem::forget`]: std::mem::forget
    /// [valid]: std::ptr#safety
    pub unsafe fn read_raw(src: *mut T) -> Self
    where
        T: 'static,
    {
        // SAFETY: `src` is guaranteed to be a valid, properly aligned pointer to a value of type `T`
        // by the caller-contract documented in this function's Safety section.
        let layout = unsafe { Layout::for_value_raw::<T>(src) };

        if Self::is_tiny_by_layout(layout) {
            // Tiny
            // initialize dest with source (for retaining vtable in fat-pointer)
            let mut dest: MaybeUninit<Self> = MaybeUninit::zeroed();

            let dest_buf = dest.as_mut_ptr();
            // SAFETY: `dest_buf` points to a fully uninitialized `MaybeUninit<Self>` which is valid
            // for reads/writes of any size up to `mem::size_of::<Self>()`. The source pointer `src`
            // is guaranteed valid and properly aligned by the caller contract. `layout.size()` equals
            // `mem::size_of::<T>()` which is ≤ `mem::size_of::<Self>()` because `is_tiny_by_layout`
            // returned true.
            unsafe {
                dest_buf
                    .cast::<u8>()
                    .copy_from(src as *const u8, layout.size()); // copy the value to the buffer
                // set the pointer metadata and provenance
                // Note: we use the address-bits for data.
                // The data might be overlapped with the data written above (we need to keep this data).
                // we only replace the metadata (&provenance).
                //
                // WARNING: We assume that the address-bits of the (fat-)pointer come before the
                // metadata-bits in memory-layout.
                // When this assumption is not true, this will be undefined behavior (UB) and the data will be corrupted.
                let payload_in_ptr = dest_buf.cast::<usize>().add(S).read();
                let dest_ptr: *mut *mut T = &raw mut (*dest.as_mut_ptr()).1;
                ptr::write(dest_ptr, src.with_addr(payload_in_ptr));
                #[cfg(debug_assertions)]
                {
                    let new_payload = dest.as_ptr().cast::<usize>().add(S).read();
                    debug_assert_eq!(payload_in_ptr, new_payload);
                }
                dest.assume_init()
            }
        } else {
            // Alloc
            // SAFETY: `layout` is computed from a valid pointer `src` via `Layout::for_value_raw`,
            // so it has the correct size and alignment for `T`. `alloc::alloc::alloc(layout)` returns
            // a block of memory with at least `layout.size()` bytes and `layout.align()` alignment,
            // which is valid for writes. The value is copied from the valid source `src` into the
            // newly allocated heap memory.
            unsafe {
                let heap_ptr = alloc::alloc::alloc(layout);
                heap_ptr.copy_from(src as *const u8, layout.size()); // copy the value to the heap-location
                let heap_ptr = ptr_mut_with_metadata_of(heap_ptr, src); // convert to a fat-pointer

                Self([0; S], heap_ptr)
            }
        }
    }

    #[inline]
    fn is_tiny(&self) -> bool {
        // SAFETY: If T is Sized, `is_tiny_ptr` is always safe. If T is unsized, the total size
        // fits in `isize` because this `TinyBoxSized` was constructed with a valid value of type T
        // whose metadata we already read successfully during construction.
        unsafe { Self::is_tiny_ptr(self.1) }
    }

    #[inline]
    const fn is_tiny_sized() -> bool
    where
        T: Sized,
    {
        Self::is_tiny_by_layout(Layout::new::<T>())
    }

    /// # Safety
    /// Same requirements as [`Layout::for_value_raw`]:
    /// * If `T` is `Sized`, this is always safe to call.
    /// * If the unsized tail of `T` is a slice `[U]`, `str`, or `dyn Trait`, then the size of
    ///   the entire value (dynamic tail length + statically sized prefix) must fit in `isize`.
    ///   (For the special case where the dynamic tail length is `0`, this is always safe.)
    ///
    /// [`Layout::for_value_raw`]: core::alloc::Layout::for_value_raw
    #[inline]
    unsafe fn is_tiny_ptr(v: *const T) -> bool {
        // SAFETY: caller guarantees that if `T` is unsized the total size fits in `isize`,
        // exactly matching the contract of `Layout::for_value_raw`.
        Self::is_tiny_by_layout(unsafe { Layout::for_value_raw(v) })
    }

    #[inline]
    const fn is_tiny_by_layout(layout: Layout) -> bool {
        layout.size() <= (S + 1) * PTR_SIZE && layout.align() <= PTR_ALIGN
    }

    #[inline]
    fn as_ptr(&self) -> *const T {
        if self.is_tiny() {
            ptr_with_metadata_of(self, self.1)
        } else {
            self.1
        }
    }

    #[inline]
    fn as_ptr_mut(&mut self) -> *mut T {
        if self.is_tiny() {
            ptr_mut_with_metadata_of(self, self.1)
        } else {
            self.1
        }
    }

    #[inline]
    unsafe fn cast_unchecked<U>(self) -> TinyBoxSized<U, S> {
        let Self(buf, ptr) = self;
        mem::forget(self);
        TinyBoxSized::<U, S>(buf, ptr.cast::<U>())
    }

    /// Casts the Tiny-Box in a different type by mapping pointer to a different type.
    /// Returns a new tiny-box with the same inline storage, but replaced pointer metadata.
    ///
    /// # Safety
    ///
    /// The pointer might not be a valid pointer. It is only used to map the metadata of the pointer to a different type.
    /// It should not be accessed an only be used to map the metadata of the pointer to a different valid type.
    /// (for example regular coercing of a pointer to a trait object is valid, or downcasting, if you know the type of the pointer is correct)
    #[doc(hidden)]
    #[inline]
    pub unsafe fn __map_ptr_unchecked<U: ?Sized>(
        self,
        mapper: impl FnOnce(*mut T) -> *mut U,
    ) -> TinyBoxSized<U, S> {
        let Self(buf, ptr) = self;
        mem::forget(self);
        TinyBoxSized::<U, S>(buf, mapper(ptr))
    }

    /// Coerces the inner pointer to a different type, returning a new tiny-box with the same inline storage.
    #[cfg(feature = "unstable")]
    #[inline]
    pub fn coerce<U: ?Sized>(self) -> TinyBoxSized<U, S>
    where
        T: core::marker::Unsize<U>,
    {
        // SAFETY: `T: Unsize<U>` guarantees that the pointer can be safely coerced to `*mut U`.
        unsafe { self.__map_ptr_unchecked(|ptr| ptr) }
    }
}

impl<T: Sized, const S: usize> TinyBoxSized<T, S> {
    /// Creates a new tiny-box, storing `v` inline if it fits or on the heap otherwise.
    ///
    /// A value is considered "tiny" and stored inline when both its size and alignment
    /// satisfy `size <= (S + 1) * sizeof(usize)` and `align <= sizeof(usize)`. In that case
    /// no heap allocation occurs. Otherwise the value is heap-allocated and the struct
    /// holds a pointer to it (then it is similar to [`Box`]).
    #[inline]
    pub fn new(v: T) -> Self {
        let layout = Layout::new::<T>();
        if Self::is_tiny_by_layout(layout) {
            let mut dest: MaybeUninit<Self> = MaybeUninit::zeroed();
            let dest_buf = dest.as_mut_ptr().cast::<T>();
            // SAFETY: `dest_buf` points to a fully uninitialized `MaybeUninit<Self>` which is valid
            // for writing `size_of::<T>()` bytes because `is_tiny_by_layout` guarantees that
            // `T`'s size and alignment fit within the struct's inline storage. `assume_init()` is
            // safe because we just wrote a fully initialized value of type `T` into the first
            // `size_of::<T>()` bytes, and `Self` is a struct of `usize` words that are now fully
            // initialized (the value occupies the first word(s), plus the pointer field is set to
            // the address-bits encoding the inline data).
            unsafe {
                dest_buf.write(v); // copy the value to the buffer
                dest.assume_init()
            }
        } else {
            // SAFETY: `layout` has the correct size and alignment for `T` (computed via
            // `Layout::new::<T>()`). `alloc::alloc::alloc(layout)` returns a block with at least
            // `layout.size()` bytes and `layout.align()` alignment, which is valid for writes.
            // The pointer is then cast to `*mut T` (address-only cast, alignment preserved since
            // allocation aligns to at least `align_of::<T>()`).
            unsafe {
                let ptr = alloc::alloc::alloc(layout).cast::<T>();
                ptr.write(v);
                Self([0; S], ptr)
            }
        }
    }

    /// Consumes the tiny-box, returning the inner value.
    ///
    /// If the value is stored on the heap, the heap allocation is deallocated as part of
    /// this operation. If the value is stored inline, no allocation is involved and the
    /// value is moved directly from the struct's buffer.
    #[must_use]
    pub fn into_inner(boxed: Self) -> T {
        if Self::is_tiny_sized() {
            // SAFETY: `boxed.0` is the inline storage buffer, and `is_tiny_sized()` guarantees
            // the value of type `T` is stored there (first `size_of::<T>()` bytes). `ptr::read`
            // creates a bitwise copy; `mem::forget` prevents double-free.
            unsafe {
                let src_ptr = boxed.0.as_ptr().cast::<T>();
                let result = ptr::read(src_ptr);
                mem::forget(boxed);
                result
            }
        } else {
            // SAFETY: `boxed.1` points to a heap-allocated value of type `T` that was allocated
            // with `layout`. We read it (bitwise copy), deallocate the heap block, and forget the
            // struct to prevent double-free in Drop.
            unsafe {
                // deallocate heap
                let ptr = boxed.1;
                let layout = Layout::new::<T>();
                let result = ptr::read(ptr);
                alloc::alloc::dealloc(ptr.cast::<u8>(), layout);
                mem::forget(boxed);
                result
            }
        }
    }
}

impl<T: ?Sized, const S: usize> ops::Deref for TinyBoxSized<T, S> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        // SAFETY: `as_ptr()` returns a pointer that is valid for reads and properly aligned.
        // When stored inline, the pointer points into the struct's own storage (valid because
        // `&self` keeps the struct alive). When heap-allocated, it points to a valid heap value.
        unsafe { self.as_ptr().as_ref_unchecked() }
    }
}

impl<T: ?Sized, const S: usize> ops::DerefMut for TinyBoxSized<T, S> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: `as_ptr_mut()` returns a pointer that is valid for reads and writes and
        // properly aligned. When stored inline, the pointer points into the struct's own storage
        // (valid because `&mut self` keeps the struct alive and exclusive). When heap-allocated,
        // it points to a valid heap value. No aliases exist because we hold `&mut self`.
        unsafe { self.as_ptr_mut().as_mut_unchecked() }
    }
}

impl<T: ?Sized, const S: usize> borrow::Borrow<T> for TinyBoxSized<T, S> {
    fn borrow(&self) -> &T {
        self
    }
}

impl<T: ?Sized, const S: usize> borrow::BorrowMut<T> for TinyBoxSized<T, S> {
    fn borrow_mut(&mut self) -> &mut T {
        self
    }
}

impl<T: ?Sized, const S: usize> AsRef<T> for TinyBoxSized<T, S> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T: ?Sized, const S: usize> AsMut<T> for TinyBoxSized<T, S> {
    fn as_mut(&mut self) -> &mut T {
        self
    }
}

impl<T: ?Sized, const S: usize> Drop for TinyBoxSized<T, S> {
    fn drop(&mut self) {
        // SAFETY: When stored inline, `as_ptr_mut()` points to the value in our own storage
        // (valid because `&mut self` keeps us alive). When heap-allocated, `self.1` points to
        // a valid heap allocation with the correct layout for `T`. We drop the value first,
        // then free the heap block. The struct's fields are dropped by the compiler after this
        // function returns, but since we only hold a `*mut T` and `[usize; S]` buffer, there's
        // nothing extra to clean up — the buffer is just plain data.
        unsafe {
            if self.is_tiny() {
                let ptr = self.as_ptr_mut();
                ptr::drop_in_place(ptr);
            } else {
                let ptr = self.1;
                let layout = Layout::for_value_raw(ptr);
                ptr::drop_in_place(ptr);
                alloc::alloc::dealloc(ptr.cast(), layout);
            }
        }
    }
}

impl<T: Default + Sized, const S: usize> Default for TinyBoxSized<T, S> {
    #[inline]
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T: Clone + Sized, const S: usize> Clone for TinyBoxSized<T, S> {
    #[inline]
    fn clone(&self) -> Self {
        Self::new(T::clone(self))
    }
}

impl<T: ?Sized + fmt::Display, const S: usize> fmt::Display for TinyBoxSized<T, S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        T::fmt(self, f)
    }
}

impl<T: ?Sized + fmt::Debug, const S: usize> fmt::Debug for TinyBoxSized<T, S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        T::fmt(self, f)
    }
}

impl<T: ?Sized, const S: usize> fmt::Pointer for TinyBoxSized<T, S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ptr: *const T = self.as_ptr();
        fmt::Pointer::fmt(&ptr, f)
    }
}

impl<T: ?Sized + PartialEq<Rhs::Target>, Rhs: ops::Deref, const S: usize> PartialEq<Rhs>
    for TinyBoxSized<T, S>
{
    #[inline]
    fn eq(&self, other: &Rhs) -> bool {
        T::eq(self, other)
    }
}

impl<T: ?Sized + PartialOrd<Rhs::Target>, Rhs: ops::Deref, const S: usize> PartialOrd<Rhs>
    for TinyBoxSized<T, S>
{
    #[inline]
    fn partial_cmp(&self, other: &Rhs) -> Option<cmp::Ordering> {
        T::partial_cmp(self, other)
    }
    #[inline]
    fn lt(&self, other: &Rhs) -> bool {
        T::lt(self, other)
    }
    #[inline]
    fn le(&self, other: &Rhs) -> bool {
        T::le(self, other)
    }
    #[inline]
    fn ge(&self, other: &Rhs) -> bool {
        T::ge(self, other)
    }
    #[inline]
    fn gt(&self, other: &Rhs) -> bool {
        T::gt(self, other)
    }
}

impl<T: ?Sized + Ord, const S: usize> Ord for TinyBoxSized<T, S> {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        T::cmp(self, other)
    }
}

impl<T: ?Sized + Eq, const S: usize> Eq for TinyBoxSized<T, S> {}

impl<T: ?Sized + hash::Hash, const S: usize> hash::Hash for TinyBoxSized<T, S> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        T::hash(self, state);
    }
}

impl<T: ?Sized + hash::Hasher, const S: usize> hash::Hasher for TinyBoxSized<T, S> {
    fn finish(&self) -> u64 {
        (**self).finish()
    }
    fn write(&mut self, bytes: &[u8]) {
        (**self).write(bytes);
    }
    fn write_u8(&mut self, i: u8) {
        (**self).write_u8(i);
    }
    fn write_u16(&mut self, i: u16) {
        (**self).write_u16(i);
    }
    fn write_u32(&mut self, i: u32) {
        (**self).write_u32(i);
    }
    fn write_u64(&mut self, i: u64) {
        (**self).write_u64(i);
    }
    fn write_u128(&mut self, i: u128) {
        (**self).write_u128(i);
    }
    fn write_usize(&mut self, i: usize) {
        (**self).write_usize(i);
    }
    fn write_i8(&mut self, i: i8) {
        (**self).write_i8(i);
    }
    fn write_i16(&mut self, i: i16) {
        (**self).write_i16(i);
    }
    fn write_i32(&mut self, i: i32) {
        (**self).write_i32(i);
    }
    fn write_i64(&mut self, i: i64) {
        (**self).write_i64(i);
    }
    fn write_i128(&mut self, i: i128) {
        (**self).write_i128(i);
    }
    fn write_isize(&mut self, i: isize) {
        (**self).write_isize(i);
    }
}

impl<E: Error, const S: usize> Error for TinyBoxSized<E, S> {
    #[allow(
        deprecated,
        reason = "implementing deprecated method for compatibility"
    )]
    fn cause(&self) -> Option<&dyn Error> {
        Error::cause(&**self)
    }

    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Error::source(&**self)
    }
}

impl<F: ?Sized + Future + Unpin, const S: usize> Future for TinyBoxSized<F, S> {
    type Output = F::Output;

    #[inline]
    fn poll(mut self: pin::Pin<&mut Self>, cx: &mut task::Context<'_>) -> task::Poll<Self::Output> {
        F::poll(pin::Pin::new(&mut *self), cx)
    }
}

// SAFETY: `TinyBoxSized<T, S>` wraps a pointer to `T` (heap) or inline storage containing `T`
// (inline). In both cases, accessing the inner `T` through `&T` or `&mut T` is equivalent to
// accessing it directly — there are no interior mutability or synchronization primitives that
// would restrict cross-thread access. Since `T: Send`, all data inside the box can be safely
// transferred to another thread.
unsafe impl<T: ?Sized + Send, const S: usize> Send for TinyBoxSized<T, S> {}

// SAFETY: Same reasoning as `Send`. The inner `T` is accessed through a pointer (heap) or inline
// storage (inline). There are no unsafe interior mutability primitives. Since `T: Sync`, all data
// inside the box can be safely shared between threads via `&T`.
unsafe impl<T: ?Sized + Sync, const S: usize> Sync for TinyBoxSized<T, S> {}

impl<const S: usize> TinyBoxSized<dyn any::Any, S> {
    /// Attempts to downcast this tiny-box to a concrete type.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if the inner value is not of type `T`.
    #[inline]
    pub fn downcast<U: any::Any>(self) -> Result<TinyBoxSized<U, S>, Self> {
        if self.is::<U>() {
            // SAFETY: `self.is::<U>()` verified that the inner value is indeed of type `U`.
            // `cast_unchecked` consumes `self` (no aliasing) and casts the pointer to `*mut U`,
            // which is valid since the value is guaranteed to be of type `U`.
            unsafe { Ok(self.cast_unchecked()) }
        } else {
            Err(self)
        }
    }
}

impl<const S: usize> TinyBoxSized<dyn any::Any + Send, S> {
    /// Attempts to downcast this tiny-box to a concrete type.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if the inner value is not of type `T`.
    #[inline]
    pub fn downcast<U: any::Any>(self) -> Result<TinyBoxSized<U, S>, Self> {
        if self.is::<U>() {
            // SAFETY: `self.is::<U>()` verified that the inner value is indeed of type `U`.
            // `cast_unchecked` consumes `self` (no aliasing) and casts the pointer to `*mut U`,
            // which is valid since the value is guaranteed to be of type `U`.
            unsafe { Ok(self.cast_unchecked()) }
        } else {
            Err(self)
        }
    }
}

impl<const S: usize> TinyBoxSized<dyn any::Any + Send + Sync, S> {
    /// Attempts to downcast this tiny-box to a concrete type.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if the inner value is not of type `T`.
    #[inline]
    pub fn downcast<U: any::Any>(self) -> Result<TinyBoxSized<U, S>, Self> {
        if self.is::<U>() {
            // SAFETY: `self.is::<U>()` verified that the inner value is indeed of type `U`.
            // `cast_unchecked` consumes `self` (no aliasing) and casts the pointer to `*mut U`,
            // which is valid since the value is guaranteed to be of type `U`.
            unsafe { Ok(self.cast_unchecked()) }
        } else {
            Err(self)
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::rc::Rc;
    use core::{any::Any, cell::Cell, mem, ptr};

    use crate::{TinyBox, TinyBoxSized};
    #[allow(
        clippy::undocumented_unsafe_blocks,
        reason = "for the transmute blocks in the trests"
    )]
    #[test]
    fn test_assumptions() {
        let ptr_size = size_of::<usize>();

        let value_zero = ();
        let value_tiny = 123u32;
        let value_big = [123u64; 4];

        let dyn_zero: &dyn Any = &value_zero;
        let dyn_tiny: &dyn Any = &value_tiny;
        let dyn_big: &dyn Any = &value_big;

        let ptr_zero: *const _ = &raw const value_zero;
        let ptr_tiny: *const _ = &raw const value_tiny;
        let ptr_big: *const _ = &raw const value_big;

        let dynptr_zero: *const dyn Any = dyn_zero;
        let dynptr_tiny: *const dyn Any = dyn_tiny;
        let dynptr_big: *const dyn Any = dyn_big;

        // normal references are not "fat", and size_of_val returns their "normal" size
        assert_eq!(0, size_of_val(&value_zero));
        assert_eq!(4, size_of_val(&value_tiny));
        assert_eq!(32, size_of_val(&value_big));

        // even for fat-pointers (dyn), size_of_val returns their "normal" size (without vtable)
        assert_eq!(0, size_of_val(dyn_zero));
        assert_eq!(4, size_of_val(dyn_tiny));
        assert_eq!(32, size_of_val(dyn_big));

        // check normal pointer sizes (sizeof<usize>)
        assert_eq!(ptr_size, size_of_val(&ptr_zero));
        assert_eq!(ptr_size, size_of_val(&ptr_tiny));
        assert_eq!(ptr_size, size_of_val(&ptr_big));

        // fat-pointers (dyn) are twice as big as a normal pointer (includes vtable reference)
        assert_eq!(2 * ptr_size, size_of_val(&dynptr_zero));
        assert_eq!(2 * ptr_size, size_of_val(&dynptr_tiny));
        assert_eq!(2 * ptr_size, size_of_val(&dynptr_big));

        // pointers to ZST are not null
        assert_ne!(ptr::null(), ptr_zero);
        assert_ne!(ptr::null(), dynptr_zero.cast::<()>());

        let dyncomponents_zero: [usize; 2] = unsafe { mem::transmute(dynptr_zero) };
        let dyncomponents_tiny: [usize; 2] = unsafe { mem::transmute(dynptr_tiny) };
        let dyncomponents_big: [usize; 2] = unsafe { mem::transmute(dynptr_big) };

        // the first component of a fat-pointer is the pointer to the value
        assert_eq!(ptr_zero.addr(), dyncomponents_zero[0]);
        assert_eq!(ptr_tiny.addr(), dyncomponents_tiny[0]);
        assert_eq!(ptr_big.addr(), dyncomponents_big[0]);

        // .. and it is not null
        assert_ne!(0, dyncomponents_zero[0]);
        assert_ne!(0, dyncomponents_tiny[0]);
        assert_ne!(0, dyncomponents_big[0]);
        // .. and the metadata is also not null
        assert_ne!(0, dyncomponents_zero[1]);
        assert_ne!(0, dyncomponents_tiny[1]);
        assert_ne!(0, dyncomponents_big[1]);

        #[cfg(feature = "unstable")]
        {
            // the second component of a fat-pointer is the vtable pointer
            let md_zero: usize = unsafe { mem::transmute(ptr::metadata(dynptr_zero)) };
            let md_tiny: usize = unsafe { mem::transmute(ptr::metadata(dynptr_tiny)) };
            let md_big: usize = unsafe { mem::transmute(ptr::metadata(dynptr_big)) };

            assert_eq!(md_zero, dyncomponents_zero[1]);
            assert_eq!(md_tiny, dyncomponents_tiny[1]);
            assert_eq!(md_big, dyncomponents_big[1]);
        }
    }

    #[test]
    fn test_simple() {
        let tiny = TinyBox::new(12345usize);
        assert_eq!(12345, *tiny);
        assert!(tiny.is_tiny());
        let tiny_addr: *const TinyBox<_> = ptr::addr_of!(tiny);
        let tiny_ptr: *const usize = &raw const *tiny;
        assert_eq!(tiny_addr.cast(), tiny_ptr);

        let big = TinyBox::new([12345usize, 5678]);
        assert_eq!([12345usize, 5678], *big);
        assert!(!big.is_tiny());
        let big_addr: *const TinyBox<_> = ptr::addr_of!(big);
        let big_ptr: *const [usize; 2] = &raw const *big;
        assert_ne!(big_addr.cast(), big_ptr);

        let tiny_sized: TinyBoxSized<_, 1> = TinyBoxSized::new([12345usize, 5678]);
        assert_eq!([12345usize, 5678], *tiny_sized);
        assert!(tiny_sized.is_tiny());
        let tiny_sized_addr: *const TinyBoxSized<_, 1> = ptr::addr_of!(tiny_sized);
        let tiny_sized_ptr: *const [usize; 2] = &raw const *tiny_sized;
        assert_eq!(tiny_sized_addr.cast(), tiny_sized_ptr);

        let big_sized: TinyBoxSized<_, 1> = TinyBoxSized::new([12345usize, 5678, 4567]);
        assert_eq!([12345usize, 5678, 4567], *big_sized);
        assert!(!big_sized.is_tiny());
        let big_sized_addr: *const TinyBoxSized<_, 1> = ptr::addr_of!(big_sized);
        let big_sized_ptr: *const [usize; 3] = &raw const *big_sized;
        assert_ne!(big_sized_addr.cast(), big_sized_ptr);
    }

    #[test]
    fn test_any() {
        let tiny = tinybox!(dyn Any => 12345usize);
        assert!(tiny.is_tiny());
        assert!(tiny.is::<usize>());
        assert_eq!(12345, *tiny.downcast::<usize>().unwrap());

        let big: TinyBox<dyn Any> = tinybox!(dyn Any => [12345usize, 5678]);
        assert!(!big.is_tiny());
        assert!(big.is::<[usize; 2]>());
        assert_eq!([12345, 5678], *big.downcast::<[usize; 2]>().unwrap());

        let tiny_sized: TinyBoxSized<dyn Any, 1> = tinybox!(dyn Any => [12345usize, 5678]; 1);
        assert!(tiny_sized.is_tiny());
        assert!(tiny_sized.is::<[usize; 2]>());
        assert_eq!([12345, 5678], *tiny_sized.downcast::<[usize; 2]>().unwrap());

        let big_sized: TinyBoxSized<dyn Any, 1> = tinybox!(dyn Any => [12345usize, 5678, 4567]; 1);
        assert!(!big_sized.is_tiny());
        assert!(big_sized.is::<[usize; 3]>());
        assert_eq!(
            [12345, 5678, 4567],
            *big_sized.downcast::<[usize; 3]>().unwrap()
        );

        let tiny = tinybox!(dyn Any => 12345usize);
        assert!(tiny.is_tiny());
        assert!(tiny.is::<usize>());
        assert!(tiny.downcast::<u8>().is_err());

        let big: TinyBox<dyn Any> = tinybox!(dyn Any => [12345usize, 5678]);
        assert!(!big.is_tiny());
        assert!(big.downcast::<u8>().is_err());

        let tiny_sized: TinyBoxSized<dyn Any, 1> = tinybox!(dyn Any => [12345usize, 5678]; 1);
        assert!(tiny_sized.is_tiny());
        assert!(tiny_sized.downcast::<usize>().is_err());

        let big_sized: TinyBoxSized<dyn Any, 1> = tinybox!(dyn Any => [12345usize, 5678, 4567]; 1);
        assert!(!big_sized.is_tiny());
        assert!(big_sized.downcast::<usize>().is_err());
    }

    #[cfg(feature = "unstable")]
    #[test]
    fn test_any_coerce() {
        let tiny: TinyBox<dyn Any> = TinyBox::new(12345usize).coerce();
        assert!(tiny.is_tiny());
        assert!(tiny.is::<usize>());
        assert_eq!(12345, *tiny.downcast::<usize>().unwrap());

        let big: TinyBox<dyn Any> = TinyBox::new([12345usize, 5678]).coerce();
        assert!(!big.is_tiny());
        assert!(big.is::<[usize; 2]>());
        assert_eq!([12345, 5678], *big.downcast::<[usize; 2]>().unwrap());
    }

    #[test]
    fn test_drop() {
        struct DropCount(Rc<Cell<usize>>);
        impl DropCount {
            fn new(counter: Rc<Cell<usize>>) -> Self {
                Self(counter)
            }
        }
        impl Drop for DropCount {
            fn drop(&mut self) {
                let v = self.0.get();
                self.0.set(v + 1);
            }
        }

        let counter = Rc::new(Cell::new(0usize));

        counter.set(0);
        let tiny = TinyBox::new(DropCount::new(counter.clone()));
        assert!(tiny.is_tiny());
        assert_eq!(0, counter.get());
        drop(tiny);
        assert_eq!(1, counter.get());

        counter.set(0);
        let big = TinyBox::new((12345usize, DropCount::new(counter.clone())));
        assert!(!big.is_tiny());
        assert_eq!(0, counter.get());
        drop(big);
        assert_eq!(1, counter.get());

        counter.set(0);
        let big2 = TinyBox::new((
            DropCount::new(counter.clone()),
            DropCount::new(counter.clone()),
        ));
        assert!(!big2.is_tiny());
        assert_eq!(0, counter.get());
        drop(big2);
        assert_eq!(2, counter.get());

        counter.set(0);
        let tiny_sized: TinyBoxSized<_, 1> =
            TinyBoxSized::new((12345usize, DropCount::new(counter.clone())));
        assert!(tiny_sized.is_tiny());
        assert_eq!(12345, (*tiny_sized).0);
        assert_eq!(0, counter.get());
        drop(tiny_sized);
        assert_eq!(1, counter.get());

        counter.set(0);
        let big_sized: TinyBoxSized<_, 1> = TinyBoxSized::new((
            12345usize,
            DropCount::new(counter.clone()),
            DropCount::new(counter.clone()),
        ));
        assert!(!big_sized.is_tiny());
        assert_eq!(12345, (*big_sized).0);
        assert_eq!(0, counter.get());
        drop(big_sized);
        assert_eq!(2, counter.get());

        counter.set(0);
        let tiny_dyn = tinybox!(dyn Any => DropCount::new(counter.clone()));
        assert!(tiny_dyn.is_tiny());
        assert!(tiny_dyn.is::<DropCount>());
        assert_eq!(0, counter.get());
        drop(tiny_dyn);
        assert_eq!(1, counter.get());

        counter.set(0);
        let big_dyn = tinybox!(dyn Any => (12345usize, DropCount::new(counter.clone())));
        assert!(!big_dyn.is_tiny());
        assert!(big_dyn.is::<(usize, DropCount)>());
        assert_eq!(0, counter.get());
        drop(big_dyn);
        assert_eq!(1, counter.get());
    }
}
