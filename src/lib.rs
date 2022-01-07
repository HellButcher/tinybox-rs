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

extern crate alloc;

use core::{
    any, borrow, cmp, fmt, future, hash,
    mem::{self, ManuallyDrop, MaybeUninit},
    ops, pin, ptr, task,
};

#[repr(C)]
pub struct TinyBoxSized<T: ?Sized, const S: usize>([usize; S], *mut T);

pub type TinyBox<T> = TinyBoxSized<T, 0>;

const PTR_SIZE: usize = mem::size_of::<*mut usize>();
const PTR_ALIGN: usize = mem::align_of::<*mut usize>();

#[doc(hidden)]
pub use core::mem::forget as __forget;

#[macro_export]
macro_rules! tinybox {
    ($e:expr) => {
        tinybox!(_ = $e; 0)
    };
    ($e:expr; $s:expr) => {
        tinybox!(_ = $e; $s)
    };
    ($t:ty = $e:expr) => {
        tinybox!($t = $e; 0)
    };
    ($t:ty = $e:expr; $s:expr) => {{
        let mut val = $e;
        let ptr: *mut _ = &mut val;
        #[allow(unsafe_code)]
        unsafe {
            let boxed: $crate::TinyBoxSized<$t, $s> = $crate::TinyBoxSized::read_raw(ptr);
            $crate::__forget(val);
            boxed
        }
    }};
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
    pub unsafe fn read_raw(src: *mut T) -> Self {
        let size = mem::size_of_val::<T>(&*src);
        let align = mem::align_of_val::<T>(&*src);

        // initialize dest with source (for retaining vtable in fat-pointer)
        let mut dest: ManuallyDrop<Self> = ManuallyDrop::new(Self([0; S], src));
        let dest_ptr = ptr::addr_of_mut!(dest.1) as *mut usize;

        let copy_ptr = if size <= (S + 1) * PTR_SIZE && align <= PTR_ALIGN {
            // Tiny
            ptr::write(dest_ptr, 0usize); // initialize pointer with zero
            dest.0.as_mut_ptr() as *mut u8 // place value as inside the space of the pointer
        } else {
            // Alloc
            let layout = alloc::alloc::Layout::for_value::<T>(&*src);
            let heap_ptr = alloc::alloc::alloc(layout);
            ptr::write(dest_ptr, heap_ptr as usize); // set pointer to the heap-location
            heap_ptr
        };
        ptr::copy_nonoverlapping(src as *const u8, copy_ptr, size);

        ManuallyDrop::into_inner(dest)
    }

    #[inline(always)]
    fn is_tiny(&self) -> bool {
        unsafe { Self::is_tiny_ptr(self.1) }
    }

    #[inline(always)]
    fn is_tiny_ref(v: &T) -> bool {
        mem::size_of_val(v) <= (S + 1) * PTR_SIZE && mem::align_of_val(v) <= PTR_ALIGN
    }

    #[inline(always)]
    unsafe fn is_tiny_ptr(v: *const T) -> bool {
        Self::is_tiny_ref(&*v)
    }

    unsafe fn tiny_as_ptr(&self) -> *mut T {
        let mut dest = self.1; // initialize dest with original value (initializes fat-pointer)
        let dest_ptr: *mut _ = &mut dest;
        let dest_ptr = dest_ptr as *mut usize;
        ptr::write(dest_ptr, self.0.as_ptr() as usize); // replace pointer
        dest
    }

    #[inline]
    pub fn as_ptr(&self) -> *mut T {
        if self.is_tiny() {
            unsafe { self.tiny_as_ptr() }
        } else {
            self.1
        }
    }

    unsafe fn downcast_unchecked<U: any::Any>(self) -> TinyBoxSized<U, S> {
        let size = mem::size_of::<TinyBoxSized<U, S>>();
        let mut result = MaybeUninit::<TinyBoxSized<U, S>>::uninit();
        ptr::copy_nonoverlapping(
            self.0.as_ptr() as *const u8,
            result.as_mut_ptr() as *mut u8,
            size,
        );
        mem::forget(self);
        result.assume_init()
    }
}

impl<T: Sized, const S: usize> TinyBoxSized<T, S> {
    #[inline(always)]
    pub fn new(v: T) -> Self
    where
        T: Sized,
    {
        tinybox!(v;S)
    }

    pub fn into_inner(boxed: Self) -> T {
        unsafe {
            let result;
            if boxed.is_tiny() {
                let ptr = boxed.tiny_as_ptr();
                result = ptr::read(ptr);
            } else {
                // deallocate heap
                let ptr = boxed.1;
                let layout = alloc::alloc::Layout::for_value::<T>(&*ptr);
                result = ptr::read(ptr);
                alloc::alloc::dealloc(ptr as *mut u8, layout);
            }
            core::mem::forget(boxed);
            result
        }
    }
}

impl<T: ?Sized, const S: usize> ops::Deref for TinyBoxSized<T, S> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        unsafe {
            let ptr = self.as_ptr();
            &*ptr
        }
    }
}

impl<T: ?Sized, const S: usize> ops::DerefMut for TinyBoxSized<T, S> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        unsafe {
            let ptr = self.as_ptr();
            &mut *ptr
        }
    }
}

impl<T: ?Sized, const S: usize> borrow::Borrow<T> for TinyBoxSized<T, S> {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized, const S: usize> borrow::BorrowMut<T> for TinyBoxSized<T, S> {
    fn borrow_mut(&mut self) -> &mut T {
        &mut **self
    }
}

impl<T: ?Sized, const S: usize> AsRef<T> for TinyBoxSized<T, S> {
    fn as_ref(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized, const S: usize> AsMut<T> for TinyBoxSized<T, S> {
    fn as_mut(&mut self) -> &mut T {
        &mut **self
    }
}

impl<T: ?Sized, const S: usize> Drop for TinyBoxSized<T, S> {
    fn drop(&mut self) {
        unsafe {
            if self.is_tiny() {
                let ptr = self.tiny_as_ptr();
                ptr::drop_in_place::<T>(ptr);
            } else {
                let ptr = self.1;
                let layout = alloc::alloc::Layout::for_value::<T>(&*ptr);
                ptr::drop_in_place::<T>(ptr);
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
        T::hash(self, state)
    }
}

impl<T: ?Sized + future::Future, const S: usize> future::Future for TinyBoxSized<T, S> {
    type Output = T::Output;

    #[inline]
    fn poll(mut self: pin::Pin<&mut Self>, cx: &mut task::Context<'_>) -> task::Poll<Self::Output> {
        self.as_mut().poll(cx)
    }
}

unsafe impl<T: ?Sized + Send, const S: usize> Send for TinyBoxSized<T, S> {}

unsafe impl<T: ?Sized + Sync, const S: usize> Sync for TinyBoxSized<T, S> {}

impl<const S: usize> TinyBoxSized<dyn any::Any, S> {
    #[inline]
    pub fn downcast<T: any::Any>(self) -> Result<TinyBoxSized<T, S>, Self> {
        if self.is::<T>() {
            unsafe { Ok(self.downcast_unchecked()) }
        } else {
            Err(self)
        }
    }
}

impl<const S: usize> TinyBoxSized<dyn any::Any + Send, S> {
    #[inline]
    pub fn downcast<T: any::Any>(self) -> Result<TinyBoxSized<T, S>, Self> {
        if self.is::<T>() {
            unsafe { Ok(self.downcast_unchecked()) }
        } else {
            Err(self)
        }
    }
}

#[cfg(test)]
mod tests {
    use core::{any::Any, cell::Cell, mem, ops::Deref, ptr};

    use crate::{TinyBox, TinyBoxSized};
    #[test]
    fn test_assumptions() {
        let ptr_size = mem::size_of::<usize>();

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
        assert_eq!(0, mem::size_of_val(&value_zero));
        assert_eq!(4, mem::size_of_val(&value_tiny));
        assert_eq!(32, mem::size_of_val(&value_big));

        // even for fat-pointers (dyn), size_of_val returns their "normal" size (without vtable)
        assert_eq!(0, mem::size_of_val(dyn_zero));
        assert_eq!(4, mem::size_of_val(dyn_tiny));
        assert_eq!(32, mem::size_of_val(dyn_big));

        // check normal pointer sizes (sizeof<usize>)
        assert_eq!(ptr_size, mem::size_of_val(&ptr_zero));
        assert_eq!(ptr_size, mem::size_of_val(&ptr_tiny));
        assert_eq!(ptr_size, mem::size_of_val(&ptr_big));

        // fat-pointers (dyn) are twice as big as a normal pointer (includes vtable reference)
        assert_eq!(2 * ptr_size, mem::size_of_val(&dynptr_zero));
        assert_eq!(2 * ptr_size, mem::size_of_val(&dynptr_tiny));
        assert_eq!(2 * ptr_size, mem::size_of_val(&dynptr_big));

        // pointers to ZST are not null
        assert_ne!(ptr::null(), ptr_zero);
        assert_ne!(ptr::null(), dynptr_zero as *const usize);

        let dyncomponents_zero: [usize; 2] = unsafe { mem::transmute(dynptr_zero) };
        let dyncomponents_tiny: [usize; 2] = unsafe { mem::transmute(dynptr_tiny) };
        let dyncomponents_big: [usize; 2] = unsafe { mem::transmute(dynptr_big) };

        // the first component of a fat-pointer is the pointer to the value
        assert_eq!(ptr_zero as usize, dyncomponents_zero[0]);
        assert_eq!(ptr_tiny as usize, dyncomponents_tiny[0]);
        assert_eq!(ptr_big as usize, dyncomponents_big[0]);

        // .. and it is not null
        assert_ne!(0, dyncomponents_zero[0]);
        assert_ne!(0, dyncomponents_tiny[0]);
        assert_ne!(0, dyncomponents_big[0]);
        // .. and the vtable is also not null
        assert_ne!(0, dyncomponents_zero[1]);
        assert_ne!(0, dyncomponents_tiny[1]);
        assert_ne!(0, dyncomponents_big[1]);
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
        let tiny = tinybox!(dyn Any = 12345usize);
        assert!(tiny.is_tiny());
        assert_eq!(12345, *tiny.downcast::<usize>().unwrap());

        let big: TinyBox<dyn Any> = tinybox!(dyn Any = [12345usize, 5678]);
        assert!(!big.is_tiny());
        assert_eq!([12345, 5678], *big.downcast::<[usize; 2]>().unwrap());

        let tiny_sized: TinyBoxSized<dyn Any, 1> = tinybox!(dyn Any = [12345usize, 5678]; 1);
        assert!(tiny_sized.is_tiny());
        assert_eq!([12345, 5678], *tiny_sized.downcast::<[usize; 2]>().unwrap());

        let big_sized: TinyBoxSized<dyn Any, 1> = tinybox!(dyn Any = [12345usize, 5678, 4567]; 1);
        assert!(!big_sized.is_tiny());
        assert_eq!(
            [12345, 5678, 4567],
            *big_sized.downcast::<[usize; 3]>().unwrap()
        );

        let tiny = tinybox!(dyn Any = 12345usize);
        assert!(tiny.is_tiny());
        assert!(tiny.downcast::<u8>().is_err());

        let big: TinyBox<dyn Any> = tinybox!(dyn Any = [12345usize, 5678]);
        assert!(!big.is_tiny());
        assert!(big.downcast::<u8>().is_err());

        let tiny_sized: TinyBoxSized<dyn Any, 1> = tinybox!(dyn Any = [12345usize, 5678]; 1);
        assert!(tiny_sized.is_tiny());
        assert!(tiny_sized.downcast::<usize>().is_err());

        let big_sized: TinyBoxSized<dyn Any, 1> = tinybox!(dyn Any = [12345usize, 5678, 4567]; 1);
        assert!(!big_sized.is_tiny());
        assert!(big_sized.downcast::<usize>().is_err());
    }

    #[test]
    fn test_drop() {
        let counter = Cell::new(0usize);

        struct DropCount<'l>(&'l Cell<usize>);
        impl Drop for DropCount<'_> {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }

        counter.set(0);
        let tiny = TinyBox::new(DropCount(&counter));
        assert!(tiny.is_tiny());
        assert_eq!(0, counter.get());
        drop(tiny);
        assert_eq!(1, counter.get());

        counter.set(0);
        let big = TinyBox::new((12345usize, DropCount(&counter)));
        assert!(!big.is_tiny());
        assert_eq!(0, counter.get());
        drop(big);
        assert_eq!(1, counter.get());

        counter.set(0);
        let big2 = TinyBox::new((DropCount(&counter), DropCount(&counter)));
        assert!(!big2.is_tiny());
        assert_eq!(0, counter.get());
        drop(big2);
        assert_eq!(2, counter.get());

        counter.set(0);
        let tiny_sized: TinyBoxSized<_, 1> = TinyBoxSized::new((12345usize, DropCount(&counter)));
        assert!(tiny_sized.is_tiny());
        assert_eq!(12345, (*tiny_sized).0);
        assert_eq!(0, counter.get());
        drop(tiny_sized);
        assert_eq!(1, counter.get());

        counter.set(0);
        let big_sized: TinyBoxSized<_, 1> =
            TinyBoxSized::new((12345usize, DropCount(&counter), DropCount(&counter)));
        assert!(!big_sized.is_tiny());
        assert_eq!(12345, (*big_sized).0);
        assert_eq!(0, counter.get());
        drop(big_sized);
        assert_eq!(2, counter.get());
    }
}
