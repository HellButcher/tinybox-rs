#![warn(
    // missing_docs,
    // rustdoc::missing_doc_code_examples,
    future_incompatible,
    rust_2018_idioms,
    unused,
    trivial_casts,
    trivial_numeric_casts,
    unused_lifetimes,
    unused_qualifications,
    unused_crate_dependencies,
    clippy::cargo,
    clippy::multiple_crate_versions,
    clippy::empty_line_after_outer_attr,
    clippy::fallible_impl_from,
    clippy::redundant_pub_crate,
    clippy::use_self,
    clippy::suspicious_operation_groupings,
    clippy::useless_let_if_seq,
    // clippy::missing_errors_doc,
    // clippy::missing_panics_doc,
    clippy::wildcard_imports
)]
#![doc(html_no_source)]
#![no_std]
#![doc = include_str!("../README.md")]
#![cfg_attr(feature = "unstable", feature(set_ptr_value))]
#![cfg_attr(all(test, feature = "unstable"), feature(ptr_metadata))]

extern crate alloc;

#[cfg(test)]
extern crate std;

use core::{
    alloc::Layout,
    any, borrow, cmp, fmt, future, hash,
    mem::{self, MaybeUninit},
    ops, pin, ptr, task,
};

#[repr(C)]
pub struct TinyBoxSized<T: ?Sized, const S: usize>([usize; S], *mut T);

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
        unsafe { tmp.fat }
    }
    #[cfg(feature = "unstable")]
    {
        ptr.with_metadata_of(meta)
    }
}

#[macro_export]
macro_rules! tinybox {
    ($t:ty, $s:expr => $e:expr) => {{
        let mut __val = $crate::TinyBoxSized::<_,  $s>::new($e);
        #[allow(unsafe_code, forgetting_copy_types)]
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
        let layout = Layout::for_value_raw::<T>(src);

        if Self::is_tiny_by_layout(layout) {
            // Tiny
            // initialize dest with source (for retaining vtable in fat-pointer)
            let mut dest: MaybeUninit<Self> = MaybeUninit::zeroed();

            let dest_buf = dest.as_mut_ptr().cast::<u8>();
            dest_buf.copy_from(src as *const u8, layout.size()); // copy the value to the buffer

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

            #[cfg(test)]
            std::println!("created raw: {:p}", dest.as_ptr(),);

            dest.assume_init()
        } else {
            // Alloc
            let heap_ptr = alloc::alloc::alloc(layout);
            heap_ptr.copy_from(src as *const u8, layout.size()); // copy the value to the heap-location
            let heap_ptr = ptr_mut_with_metadata_of(heap_ptr, src); // convert to a fat-pointer

            Self([0; S], heap_ptr)
        }
    }

    #[inline(always)]
    fn is_tiny(&self) -> bool {
        unsafe { Self::is_tiny_ptr(self.1) }
    }

    #[inline(always)]
    const fn is_tiny_sized() -> bool
    where
        T: Sized,
    {
        Self::is_tiny_by_layout(Layout::new::<T>())
    }

    #[inline(always)]
    unsafe fn is_tiny_ptr(v: *const T) -> bool {
        Self::is_tiny_by_layout(Layout::for_value_raw(v))
    }

    #[inline(always)]
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
}

impl<T: Sized, const S: usize> TinyBoxSized<T, S> {
    #[inline]
    pub fn new(v: T) -> Self {
        let layout = Layout::new::<T>();
        if Self::is_tiny_by_layout(layout) {
            let mut dest: MaybeUninit<Self> = MaybeUninit::zeroed();
            let dest_buf = dest.as_mut_ptr().cast::<T>();
            unsafe {
                dest_buf.write(v); // copy the value to the buffer

                #[cfg(test)]
                std::println!("created new in place: {:p}", dest_buf);

                dest.assume_init()
            }
        } else {
            unsafe {
                let ptr = alloc::alloc::alloc(layout).cast::<T>();
                ptr.write(v);

                #[cfg(test)]
                std::println!("created new alloc: {:p} heap ptr", ptr);

                Self([0; S], ptr)
            }
        }
    }

    pub fn into_inner(boxed: Self) -> T {
        if Self::is_tiny_sized() {
            unsafe {
                let src_ptr = boxed.0.as_ptr() as *const T;
                let result = ptr::read(src_ptr);
                mem::forget(boxed);
                result
            }
        } else {
            unsafe {
                // deallocate heap
                let ptr = boxed.1;
                let layout = Layout::new::<T>();
                let result = ptr::read(ptr);
                alloc::alloc::dealloc(ptr as *mut u8, layout);
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
        unsafe { self.as_ptr().as_ref_unchecked() }
    }
}

impl<T: ?Sized, const S: usize> ops::DerefMut for TinyBoxSized<T, S> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
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
        unsafe {
            if self.is_tiny() {
                let ptr = self.as_ptr_mut();
                #[cfg(test)]
                std::println!("Dropping In In Place: {:p}", ptr);
                ptr::drop_in_place(ptr);
                #[cfg(test)]
                std::println!("Done");
            } else {
                let ptr = self.1;
                let layout = Layout::for_value_raw(ptr);
                #[cfg(test)]
                std::println!("Dropping In Heap: {:p}", ptr);
                ptr::drop_in_place(ptr);
                #[cfg(test)]
                std::println!("Free: {:p}", ptr);
                alloc::alloc::dealloc(ptr as *mut u8, layout);
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
        let ptr: *const T = ops::Deref::deref(self);
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
        T::hash(self, state)
    }
}

impl<T: ?Sized + future::Future, const S: usize> future::Future for TinyBoxSized<T, S> {
    type Output = T::Output;

    #[inline]
    fn poll(self: pin::Pin<&mut Self>, cx: &mut task::Context<'_>) -> task::Poll<Self::Output> {
        let fut: pin::Pin<&mut T> = unsafe { self.map_unchecked_mut(ops::DerefMut::deref_mut) };
        fut.poll(cx)
    }
}

unsafe impl<T: ?Sized + Send, const S: usize> Send for TinyBoxSized<T, S> {}

unsafe impl<T: ?Sized + Sync, const S: usize> Sync for TinyBoxSized<T, S> {}

impl<const S: usize> TinyBoxSized<dyn any::Any, S> {
    #[inline]
    pub fn downcast<T: any::Any>(self) -> Result<TinyBoxSized<T, S>, Self> {
        if self.is::<T>() {
            unsafe { Ok(self.cast_unchecked()) }
        } else {
            Err(self)
        }
    }
}

impl<const S: usize> TinyBoxSized<dyn any::Any + Send, S> {
    #[inline]
    pub fn downcast<T: any::Any>(self) -> Result<TinyBoxSized<T, S>, Self> {
        if self.is::<T>() {
            unsafe { Ok(self.cast_unchecked()) }
        } else {
            Err(self)
        }
    }
}

impl<const S: usize> TinyBoxSized<dyn any::Any + Send + Sync, S> {
    #[inline]
    pub fn downcast<T: any::Any>(self) -> Result<TinyBoxSized<T, S>, Self> {
        if self.is::<T>() {
            unsafe { Ok(self.cast_unchecked()) }
        } else {
            Err(self)
        }
    }
}

#[cfg(test)]
mod tests {
    use core::{any::Any, cell::Cell, mem, ops::Deref, ptr};
    use std::io::Write;

    use alloc::rc::Rc;

    use crate::{TinyBox, TinyBoxSized};
    #[test]
    fn test_assumptions() {
        let ptr_size = size_of::<usize>();

        #[allow(clippy::let_unit_value)]
        let value_zero = ();
        let value_tiny = 123u32;
        let value_big = [123u64; 4];

        let dyn_zero: &dyn Any = &value_zero;
        let dyn_tiny: &dyn Any = &value_tiny;
        let dyn_big: &dyn Any = &value_big;

        let ptr_zero: *const _ = &value_zero;
        let ptr_tiny: *const _ = &value_tiny;
        let ptr_big: *const _ = &value_big;

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
        assert_ne!(ptr::null(), dynptr_zero as *const usize);

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
        let tiny_ptr: *const usize = tiny.deref();
        assert_eq!(tiny_addr as *const usize, tiny_ptr);

        let big = TinyBox::new([12345usize, 5678]);
        assert_eq!([12345usize, 5678], *big);
        assert!(!big.is_tiny());
        let big_addr: *const TinyBox<_> = ptr::addr_of!(big);
        let big_ptr: *const [usize; 2] = big.deref();
        assert_ne!(big_addr as *const [usize; 2], big_ptr);

        let tiny_sized: TinyBoxSized<_, 1> = TinyBoxSized::new([12345usize, 5678]);
        assert_eq!([12345usize, 5678], *tiny_sized);
        assert!(tiny_sized.is_tiny());
        let tiny_sized_addr: *const TinyBoxSized<_, 1> = ptr::addr_of!(tiny_sized);
        let tiny_sized_ptr: *const [usize; 2] = tiny_sized.deref();
        assert_eq!(tiny_sized_addr as *const [usize; 2], tiny_sized_ptr);

        let big_sized: TinyBoxSized<_, 1> = TinyBoxSized::new([12345usize, 5678, 4567]);
        assert_eq!([12345usize, 5678, 4567], *big_sized);
        assert!(!big_sized.is_tiny());
        let big_sized_addr: *const TinyBoxSized<_, 1> = ptr::addr_of!(big_sized);
        let big_sized_ptr: *const [usize; 3] = big_sized.deref();
        assert_ne!(big_sized_addr as *const [usize; 3], big_sized_ptr);
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

    #[test]
    fn test_drop() {
        let counter = Rc::new(Cell::new(0usize));

        struct DropCount(Rc<Cell<usize>>);
        impl DropCount {
            fn new(counter: Rc<Cell<usize>>) -> Self {
                let v = counter.get();
                std::println!(
                    "DropCount::new() called, counter = {v}, {:p}",
                    &raw const counter
                );
                std::io::stdout().flush().unwrap();
                Self(counter)
            }
        }
        impl Drop for DropCount {
            fn drop(&mut self) {
                std::println!("DropCount::drop() called; {:p}", self);
                let v = self.0.get();
                std::io::stdout().flush().unwrap();
                self.0.set(v + 1);
            }
        }

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

        std::println!("RC1: {:?}", Rc::strong_count(&counter));

        std::println!("Test 2");
        counter.set(0);
        let tiny_dyn = tinybox!(dyn Any => DropCount::new(counter.clone()));
        assert!(tiny_dyn.is_tiny());
        assert!(tiny_dyn.is::<DropCount>());
        assert_eq!(0, counter.get());
        std::println!("RC2: {:?}", Rc::strong_count(&counter));
        drop(tiny_dyn);
        std::println!("Test 2.4");
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
