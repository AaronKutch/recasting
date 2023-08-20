//! Enable the "std" feature for some extra impls

#![cfg_attr(not(feature = "std"), no_std)]

use core::num::{
    NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize, NonZeroU128,
    NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize,
};
extern crate alloc;

/// A trait implemented for structures that have `Item`s that should be
/// `Recast`ed by a `Recaster`.
///
/// ```
/// // using `Recaster` and `Recast` on the
/// // `Arena` from the `triple_arena` crate
/// use recasting::{Recaster, Recast};
/// use triple_arena::{Arena, Ptr, ptr_struct};
///
/// ptr_struct!(P0; Q1);
///
/// // `triple_arena` defines `Ptr`s with `Ptr: Recast<Self>` and implements
/// // this in the `ptr_struct` macro
/// /*
/// impl $crate::Recast<Self> for $struct_name {
///     fn recast<R: $crate::Recaster<Item = Self>>(&mut self, recaster: &R)
///         -> Result<(), <R as $crate::Recaster>::Item> {
///         recaster.recast_item(self)
///     }
/// }
/// */
///
/// // An example some user structure. `Recast` was ultimately made for
/// // complicated structures that can have the `Item` in various fields.
/// // `Ptr`s are often used in structures that have references stored
/// // in arbitrary ways that aren't tree-like like in Rust's `&` and
/// // `&mut` references. This becomes a problem when we want to do
/// // something like serialize the structure, because the capacity
/// // of the `Arena`s would never decrease. Unless, we could
/// // ergonomically map all the `Ptr`s to new values from
/// // `Arena::compress_and_shrink`.
/// #[derive(Debug, PartialEq, Eq)]
/// struct Entry(u64, Vec<P0>, Q1);
/// struct Structure {
///     p0_arena: Arena<P0, Entry>,
///     // some `P0`s that are stored externally to the arena
///     external: Vec<P0>,
///     // an arena that is keyed by `Q1` instead of `P0`
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
/// // with recasters with different `Item`s.
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
///         // This line when uncommented results in an error because
///         // there is not a `impl Recast<P0> for i32`, and we don't
///         // need it because there are no `P0`s stored in `q1_arena`.
///         //self.q1_arena.recast(recaster)?;
///
///         // Note that if you have multiple collections with the same
///         // type of key, you should change it with wrappers to a
///         // different struct to prevent confusion (in `triple_arena`
///         // we can use `ptr_struct` to create multiple structs to
///         // represent different validity spaces of the different
///         // arenas within the same structure, or otherwise use
///         // generics to enforce a virtual difference).
///         // If for some reason the same item absolutely needs to be
///         // used in keys to more than one collection (e.x. we have
///         // an `Arena<P0, _>` and an external `HashSet<P0>` that is
///         // also keyed by `P0`), the recasting impl needs to empty
///         // all collections except for the collection that the
///         // `Recaster` is derived from. Then, the keys are recasted
///         // externally and reinserted, or otherwise regenerated.
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
///         // for this example we will use the recaster generated from
///         // `compress_and_shrink_recaster`. This function rekeys
///         // `q1_arena` and creates a mapping of the old keys to the
///         // new.
///         let recaster = self.q1_arena.compress_and_shrink_recaster();
///         // Immediately afterwards, we need to recast all the values.
///         // If we were to do anything else like call some function
///         // that tries to index `q1_arena`, the operations would fail
///         // because all other `Q1`s besides the keys (and just the
///         // keys, if `q1_arena` had values with `Q1`s in them, they
///         // would still reflect the old key mapping) are based on the
///         // old keying. Calling `recast` will fix all that if we
///         // implemented it correctly.
///         self.recast(&recaster)?;
///         // it is encouraged to have all the relevant `Q1`s self
///         // contained within `Structure`, but if needed we could also
///         // return the `recaster` for more external things.
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
/// assert!(structure.q1_arena.get(old_q1_1).is_none());
/// q1_1.recast(&q1_recaster).unwrap();
/// assert_eq!(structure.q1_arena.get(q1_1), Some(-2).as_ref());
///
/// let old_p0_1 = p0_1;
/// let old_p0_2 = p0_2;
/// p0_1.recast(&p0_recaster).unwrap();
/// p0_2.recast(&p0_recaster).unwrap();
///
/// assert_eq!(
///     *structure.p0_arena.get(p0_2).unwrap(),
///     Entry(42, vec![p0_1], q1_1)
/// );
/// // the structure relations are preserved despite the `Ptr`s
/// // changing
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

impl<I, T: Recast<I>> Recast<I> for alloc::boxed::Box<T> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        self.as_mut().recast(recaster)?;
        Ok(())
    }
}

impl<I, T: Recast<I>> Recast<I> for Option<T> {
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

impl<I, T: Recast<I>> Recast<I> for alloc::vec::Vec<T> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for t in self {
            t.recast(recaster)?;
        }
        Ok(())
    }
}

impl<I, T: Recast<I>> Recast<I> for alloc::collections::VecDeque<T> {
    fn recast<R: Recaster<Item = I>>(&mut self, recaster: &R) -> Result<(), <R as Recaster>::Item> {
        for t in self {
            t.recast(recaster)?;
        }
        Ok(())
    }
}

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
