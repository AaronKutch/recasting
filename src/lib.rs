//! Note that there are "alloc" and "std" feature flags that can be turned off

#![cfg_attr(not(feature = "std"), no_std)]

use core::{
    marker::PhantomData,
    num::{
        NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize, NonZeroU128,
        NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize,
    },
};

#[cfg(feature = "alloc")]
extern crate alloc;

/// A trait implemented for structures that have `Item`s that should be
/// `Recast`ed by a `Recaster`.
///
/// `Recast` was designed for structures with their own virtual address spaces,
/// with the `Item`s being virtual addresses. For example, arenas from the
/// `triple_arena` crate have entries that can be referenced by `Ptr`s. The
/// `Ptr`s are indexes that must remain stable, otherwise copies of them will
/// become invalid. The arenas from `triple_arena` have a problem where they
/// should be compressed before being serialized, or else unused interior
/// capacity will be forced upon the deserialized arenas in order to keep stable
/// `Ptr`s. If the plain `compress_and_shrink` function is used, for example,
/// the `Ptr` indexes are translated each to a new value, but all external
/// `Ptr`s and the `Ptr`s in the entries would remain untranslated to the new
/// mapping.
///
/// ```
/// use triple_arena::{ptr_struct, Arena, Ptr};
/// // the `P0` `Ptr` type
/// ptr_struct!(P0);
///
/// let mut a: Arena<P0, (u64, Option<P0>)> = Arena::new();
/// let p_1 = a.insert((1, None));
/// let p_2 = a.insert((2, None));
/// let p_7 = a.insert((7, None));
/// let p_42 = a.insert((42, Some(p_7)));
/// // create some unallocated internal entries
/// a.remove(p_1).unwrap();
/// a.remove(p_2).unwrap();
///
/// assert_eq!(a.get(p_7), Some(&(7, None)));
/// assert_eq!(a.get(p_42), Some(&(42, Some(p_7))));
///
/// // translate all the entries and their `Ptr` keys to new locations
/// a.compress_and_shrink();
///
/// // the external copies `p_7` and `p_42` no longer work
/// assert_eq!(a.get(p_7), None);
/// assert_eq!(a.get(p_42), None);
///
/// // manually get the entry where 42 ends up
/// let entry42: (u64, Option<P0>) = *a.vals().nth(1).unwrap();
/// // the copy of `p_7` also was not changed even though it was inside
/// // the arena, only the `Ptr`s by which entries are referenced has
/// // changed, and anything inside the values is left unchanged
/// assert_eq!(a.get(entry42.1.unwrap()), None);
/// ```
///
/// We could use `compress_and_shrink_with` and correctly recast all `Ptr`s
/// inside and outside the arena, but this quickly gets untenable as the
/// complexity of the datastructure increases. Here is a version with `Recast`
///
/// ```
/// use triple_arena::{ptr_struct, Arena, Ptr, Recaster, Recast};
/// ptr_struct!(P0);
///
/// // the structs from `ptr_struct` automatically have `Recast<Self>`
/// // implemented, which looks like:
/// //
/// //impl Recast<Self> for P0 {
/// //    #[inline]
/// //    fn recast<R: Recaster<Item = P0>>(&mut self, recaster: &R)
/// //        -> Result<(), <R as Recaster>::Item> {
/// //        recaster.recast_item(self)
/// //    }
/// //}
///
/// impl Recast<P0> for (u64, Option<P0>) {
///     fn recast<R: Recaster<Item = P0>>(&mut self, recaster: &R)
///         -> Result<(), <R as Recaster>::Item> {
///         // this calls the impl of `Recast` for `Option<T>`, which calls
///         // `Recast<Self> for P0`
///         self.1.recast(recaster)?;
///         // `self.0` does not have any `P0`s inside of it, but if there
///         // are any fields with `P0`s they should also have `recast`
///         // called
///         Ok(())
///     }
/// }
///
/// let mut a: Arena<P0, (u64, Option<P0>)> = Arena::new();
/// let p_1 = a.insert((1, None));
/// let p_2 = a.insert((2, None));
/// let mut p_7 = a.insert((7, None));
/// let mut p_42 = a.insert((42, Some(p_7)));
/// // create some unallocated internal entries
/// a.remove(p_1).unwrap();
/// a.remove(p_2).unwrap();
///
/// assert_eq!(a.get(p_7), Some(&(7, None)));
/// assert_eq!(a.get(p_42), Some(&(42, Some(p_7))));
///
/// let old_p_7 = p_7;
///
/// // translate all the entries and their `Ptr` keys to new locations,
/// // this time with `compress_and_shrink_recaster` which returns an
/// // `Arena<P0, P0>` that implements `Recaster`. This recaster maps
/// // old `Ptr`s to their new indexes.
/// let recaster = a.compress_and_shrink_recaster();
///
/// p_7.recast(&recaster).unwrap();
/// p_42.recast(&recaster).unwrap();
///
/// // now `p_7` and `p_42` work again, however note that we forgot
/// // to recast the arena itself, this is very important to remember
/// // if the entries in the arena or whatever map we are using has
/// // `Item`s in it
/// assert_eq!(a.get(p_7), Some(&(7, None)));
/// assert_eq!(a.get(p_42), Some(&(42, Some(old_p_7))));
///
/// a.recast(&recaster).unwrap();
///
/// assert_eq!(a.get(p_42), Some(&(42, Some(p_7))));
/// ```
///
/// Now for a more advanced example with multiple `Item` types
///
/// ```
/// use triple_arena::{Arena, Ptr, ptr_struct, Recaster, Recast};
///
/// // Multiple `Ptr` types. Usually, there needs to be one `Item`
/// // type per address space that can be recast.
/// ptr_struct!(P0; Q1);
///
/// // An example user structure. Preferably, these things should be
/// // designed so that all the `Ptr`s are self contained, which
/// // means that only one top level recast call needs to be made
/// // to map them all.
/// #[derive(Debug, PartialEq, Eq)]
/// struct Entry(u64, Vec<P0>, Q1);
/// struct Structure {
///     p0_arena: Arena<P0, Entry>,
///     // some `P0`s that are stored externally to the arena
///     external: Vec<P0>,
///     // An arena that is keyed by `Q1` instead of `P0`. If there are
///     // multiple arenas, `HashMap`s, `BTreeMap`s, or any kind of
///     // virtual-address-space capable types within the same structure,
///     // they should each have their own wrapper `Item`s implementing
///     // `Recast<Self>`. If for some reason there is a need for address
///     // space duplication, e.g. a `HashSet<P0>` companion to a
///     // `Arena<P0, ...>`, then the hash set needs to be emptied into a
///     // new one, with each `P0` recast with the recaster for the
///     // principle address space.
///     q1_arena: Arena<Q1, i32>,
/// }
///
/// impl Recast<P0> for Entry {
///     fn recast<R: Recaster<Item = P0>>(&mut self, recaster: &R)
///         -> Result<(), <R as Recaster>::Item> {
///         // we can do this because of the `impl` of `Recast` for `Vec`, which
///         // recasts all the entries
///         self.1.recast(recaster)?;
///         // the `.0` and `.1` fields are left untouched, since they
///         // do not have `P0` values that would need to be recast
///         Ok(())
///     }
/// }
///
/// // Because we used an external associated type for the `Recast` trait,
/// // we can `impl` multiple times to be able to recast the same struct
/// // with recasters of different `Item`s.
/// impl Recast<Q1> for Entry {
///     fn recast<R: Recaster<Item = Q1>>(&mut self, recaster: &R)
///         -> Result<(), <R as Recaster>::Item> {
///         // recast the `Q1`
///         self.2.recast(recaster)?;
///         Ok(())
///     }
/// }
///
/// impl Recast<P0> for Structure {
///     fn recast<R: Recaster<Item = P0>>(&mut self, recaster: &R)
///         -> Result<(), <R as Recaster>::Item> {
///         self.p0_arena.recast(recaster)?;
///         // `external` has some `P0`s we need to recast so that they
///         // agree with elsewhere in the structure.
///         self.external.recast(recaster)?;
///         Ok(())
///     }
/// }
///
/// impl Recast<Q1> for Structure {
///     fn recast<R: Recaster<Item = Q1>>(&mut self, recaster: &R)
///         -> Result<(), <R as Recaster>::Item> {
///         // the `Entry`s have `Q1` in them, this will delegate to the
///         // `Recast<Q1> for Entry` impl
///         self.p0_arena.recast(recaster)?;
///         Ok(())
///     }
/// }
///
/// impl Structure {
///     fn recast_q1(&mut self) -> Result<Arena<Q1, Q1>, Q1> {
///         let recaster = self.q1_arena.compress_and_shrink_recaster();
///         // Immediately afterwards, we need to recast all the values.
///         self.recast(&recaster)?;
///         // it is encouraged to have all the relevant `Item`s self
///         // contained within `Structure` so that only one call is
///         // needed at the user level, but if needed we could also
///         // return the `recaster` for recasting things external to
///         // the structure.
///         Ok(recaster)
///     }
///
///     fn recast_p0(&mut self) -> Result<Arena<P0, P0>, P0> {
///         // Note an `Err` gets returned by `recast` if it encounters
///         // a `P0` that was not contained as a key in the `p0_arena`
///         // upon the call to acquire a recaster. If `Structure` is
///         // using some kind of convention where invalid items could
///         // be kept, they need to be purged by some routine here before
///         // the `compress_and_shrink_recaster` call, or a custom
///         // `Recaster` could be defined to be a no-op on unkown keys.
///         let recaster = self.p0_arena.compress_and_shrink_recaster();
///         self.recast(&recaster)?;
///         Ok(recaster)
///     }
///
///     // for preparation before serialization or whatever purpose
///     // the recasting has
///     fn compress_and_shrink_all(&mut self) {
///         self.recast_q1().unwrap();
///         self.recast_p0().unwrap();
///     }
/// }
///
/// let mut structure = Structure {
///     p0_arena: Arena::new(),
///     external: vec![],
///     q1_arena: Arena::new()
/// };
/// // do some random inserts and removals
/// let q1_0 = structure.q1_arena.insert(-1);
/// let mut q1_1 = structure.q1_arena.insert(-2);
/// structure.q1_arena.remove(q1_0).unwrap();
/// let p0_0 = structure.p0_arena.insert(Entry(1, vec![], q1_1));
/// let mut p0_1 = structure.p0_arena.insert(Entry(2, vec![], q1_1));
/// let mut p0_2 = structure.p0_arena.insert(Entry(42, vec![p0_1], q1_1));
/// structure.p0_arena.remove(p0_0).unwrap();
///
/// let p0_recaster = structure.recast_p0().unwrap();
/// let q1_recaster = structure.recast_q1().unwrap();
///
/// // now everything within the `Structure` is recast, but note
/// // that the items we kept outside are invalid now and would
/// // need to be recast to be used for the new mapping
///
/// let old_q1_1 = q1_1;
/// q1_1.recast(&q1_recaster).unwrap();
///
/// assert!(structure.q1_arena.get(old_q1_1).is_none());
/// assert_eq!(structure.q1_arena.get(q1_1), Some(-2).as_ref());
///
/// let old_p0_1 = p0_1;
/// let old_p0_2 = p0_2;
/// p0_1.recast(&p0_recaster).unwrap();
/// p0_2.recast(&p0_recaster).unwrap();
///
/// // the complicated structure relations and `Ptr` validities
/// // are preserved despite the `Ptr`s all changing
/// assert_eq!(
///     *structure.p0_arena.get(p0_2).unwrap(),
///     Entry(42, vec![p0_1], q1_1)
/// );
/// assert_ne!(old_p0_1, p0_1);
/// assert_ne!(old_p0_2, p0_2);
/// assert_ne!(old_q1_1, q1_1);
/// ```
pub trait Recast<Item> {
    /// Rewrites all the `<R as Recaster>::Item`s of `self` according to the
    /// `<recaster as Recaster>::map`.
    ///
    /// # Errors
    ///
    /// If the recaster encounters an item it does not recognize, it returns
    /// that item. Note that the state of `self` from before the `recast` may be
    /// unrecoverable (the structure can remain partially recast), and errors
    /// should only be encountered if these traits were used wrongly.
    fn recast<R: Recaster<Item = Item>>(
        &mut self,
        recaster: &R,
    ) -> Result<(), <R as Recaster>::Item>;
}

// for working with `Result<(), E>` and such easier
impl<I> Recast<I> for () {
    #[inline]
    fn recast<R: Recaster<Item = I>>(
        &mut self,
        _recaster: &R,
    ) -> Result<(), <R as Recaster>::Item> {
        Ok(())
    }
}

impl<I, T> Recast<I> for PhantomData<T> {
    #[inline]
    fn recast<R: Recaster<Item = I>>(
        &mut self,
        _recaster: &R,
    ) -> Result<(), <R as Recaster>::Item> {
        Ok(())
    }
}

macro_rules! impl_self_recast {
    ($($t:ident)*) => {
        $(
            impl Recast<$t> for $t {
                #[inline]
                fn recast<R: Recaster<Item = $t>>(&mut self, recaster: &R)
                    -> Result<(), <R as Recaster>::Item> {
                    recaster.recast_item(self)
                }
            }
        )*
    };
}

impl_self_recast!(
    usize u8 u16 u32 u64 u128 NonZeroUsize NonZeroU8 NonZeroU16 NonZeroU32 NonZeroU64 NonZeroU128
    isize i8 i16 i32 i64 i128 NonZeroIsize NonZeroI8 NonZeroI16 NonZeroI32 NonZeroI64 NonZeroI128
    bool char f32 f64
);

impl<I, T: Recast<I>> Recast<I> for &mut T {
    #[inline]
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        Recast::recast(*self, recaster)?;
        Ok(())
    }
}

impl<I, T: Recast<I>> Recast<I> for core::cell::Cell<T> {
    #[inline]
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        Recast::recast(self.get_mut(), recaster)?;
        Ok(())
    }
}

impl<I, T: Recast<I>> Recast<I> for core::cell::RefCell<T> {
    #[inline]
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        Recast::recast(self.get_mut(), recaster)?;
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<I, T: Recast<I>> Recast<I> for alloc::boxed::Box<T> {
    #[inline]
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        self.as_mut().recast(recaster)?;
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<I, T: Recast<I>> Recast<I> for alloc::rc::Rc<T> {
    #[inline]
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        Recast::recast(&mut alloc::rc::Rc::get_mut(self), recaster)?;
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<I, T: Recast<I>> Recast<I> for alloc::sync::Arc<T> {
    #[inline]
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        Recast::recast(&mut alloc::sync::Arc::get_mut(self), recaster)?;
        Ok(())
    }
}

impl<I, T: Recast<I>> Recast<I> for Option<T> {
    #[inline]
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        if let Some(t) = self {
            t.recast(recaster)?;
        }
        Ok(())
    }
}

impl<I, T: Recast<I>, E: Recast<I>> Recast<I> for Result<T, E> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        match self {
            Ok(o) => o.recast(recaster)?,
            Err(e) => e.recast(recaster)?,
        }
        Ok(())
    }
}

macro_rules! tuple_recast {
    ($($i:tt $t:tt),+) => {
        impl<Z, $($t: Recast<Z>,)+> Recast<Z> for ($($t,)+) {
            #[inline]
            fn recast<R: Recaster<Item = Z>>(&mut self, recaster: &R)
                -> Result<(), <R as Recaster>::Item> {
                $(
                    self.$i.recast(recaster)?;
                )+
                Ok(())
            }
        }
    };
}

tuple_recast!(0 A);
tuple_recast!(0 A, 1 B);
tuple_recast!(0 A, 1 B, 2 C);
tuple_recast!(0 A, 1 B, 2 C, 3 D);
tuple_recast!(0 A, 1 B, 2 C, 3 D, 4 E);
tuple_recast!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F);
tuple_recast!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G);
tuple_recast!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H);
tuple_recast!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I);
tuple_recast!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J);
tuple_recast!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J, 10 K);
tuple_recast!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J, 10 K, 11 L);

impl<I, T: Recast<I>, const N: usize> Recast<I> for [T; N] {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for t in self {
            t.recast(recaster)?;
        }
        Ok(())
    }
}

impl<I, T: Recast<I>> Recast<I> for [T] {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for t in self {
            t.recast(recaster)?;
        }
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<I, T: Recast<I>> Recast<I> for alloc::vec::Vec<T> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for t in self {
            t.recast(recaster)?;
        }
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<I, T: Recast<I>> Recast<I> for alloc::collections::VecDeque<T> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for t in self {
            t.recast(recaster)?;
        }
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<I, T: Recast<I>> Recast<I> for alloc::collections::LinkedList<T> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for t in self {
            t.recast(recaster)?;
        }
        Ok(())
    }
}

#[cfg(feature = "std")]
impl<I, K, V: Recast<I>> Recast<I> for std::collections::HashMap<K, V> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for t in self.values_mut() {
            t.recast(recaster)?;
        }
        Ok(())
    }
}

#[cfg(feature = "std")]
impl<I, K, V: Recast<I>> Recast<I> for std::collections::BTreeMap<K, V> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for t in self.values_mut() {
            t.recast(recaster)?;
        }
        Ok(())
    }
}

/// A trait implemented for structures that can act as a `Recaster` in
/// `Recast`ing `Item`s.
///
/// Most end users will get a `Recaster` from some method on a collection or
/// some free function, see the `Recast` documentation for that. Here is
/// an example of actually implementing a `Recaster`.
///
/// ```
/// use std::collections::HashMap;
///
/// use recasting::{Recast, Recaster};
///
/// // there is an existing impl for `HashMap`, we will use a wrapper
/// struct MyRecaster(HashMap<i64, i64>);
///
/// impl Recaster for MyRecaster {
///     type Item = i64;
///
///     fn recast_item(&self, item: &mut Self::Item) -> Result<(), Self::Item> {
///         if let Some(res) = self.0.get(item) {
///             *item = *res;
///             Ok(())
///         } else {
///             // alternatively, we could make this a no-op or use
///             // other behavior depending on our intentions
///             Err(*item)
///         }
///     }
/// }
///
/// struct Structure {
///     keyed_map: HashMap<i64, String>,
/// }
///
/// impl Structure {
///     fn insert(&mut self, i: i64, s: &str) {
///         self.keyed_map.insert(i, s.to_owned());
///     }
///
///     fn get(&self, i: i64) -> Option<&str> {
///         self.keyed_map.get(&i).map(|s| s.as_str())
///     }
///
///     // some arbitrary key remapping we are choosing for an example
///     fn sub42<F: FnMut(i64, i64)>(&mut self, mut map: F) {
///         let mut new = HashMap::new();
///         for (key, val) in self.keyed_map.drain() {
///             new.insert(key - 42, val);
///             // closure through which we can
///             // see the old and new keys
///             map(key, key - 42);
///         }
///         self.keyed_map = new;
///     }
///
///     fn sub42_recaster(&mut self) -> MyRecaster {
///         let mut map = HashMap::new();
///         self.sub42(|old, new| {
///             map.insert(old, new);
///         });
///         MyRecaster(map)
///     }
/// }
///
/// let mut structure = Structure {
///     keyed_map: HashMap::new(),
/// };
///
/// let mut keys = vec![0, 1337, -10];
/// structure.insert(keys[0], "test");
/// structure.insert(keys[1], "hello");
/// structure.insert(keys[2], "world");
///
/// let recaster = structure.sub42_recaster();
/// // this goes through the `Recast` impl for `Vec` and calls
/// // `Recast<i64>` with `<MyRecaster as Recaster>::recast_item`
/// keys.recast(&recaster).unwrap();
///
/// assert_eq!(&keys, &[-42, 1295, -52]);
/// assert_eq!(structure.get(keys[0]).unwrap(), "test");
/// assert_eq!(structure.get(keys[1]).unwrap(), "hello");
/// assert_eq!(structure.get(keys[2]).unwrap(), "world");
/// ```
pub trait Recaster {
    type Item;

    /// Recasts an `item` based off of `self`. Returns an `Err` with `item` if
    /// it could not be handled.
    fn recast_item(&self, item: &mut Self::Item) -> Result<(), Self::Item>;
}

#[cfg(feature = "std")]
impl<K: PartialEq + Eq + core::hash::Hash + Clone> Recaster for std::collections::HashMap<K, K> {
    type Item = K;

    fn recast_item(&self, item: &mut Self::Item) -> Result<(), Self::Item> {
        if let Some(res) = self.get(item) {
            *item = res.clone();
            Ok(())
        } else {
            Err(item.clone())
        }
    }
}

#[cfg(feature = "std")]
impl<K: std::cmp::Ord + Clone> Recaster for std::collections::BTreeMap<K, K> {
    type Item = K;

    fn recast_item(&self, item: &mut Self::Item) -> Result<(), Self::Item> {
        if let Some(res) = self.get(item) {
            *item = res.clone();
            Ok(())
        } else {
            Err(item.clone())
        }
    }
}
