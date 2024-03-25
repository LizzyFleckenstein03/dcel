#![allow(private_bounds)]
#![allow(clippy::type_complexity)]

pub use ghost_cell;
pub use typed_arena;

use core::ops::Deref;
use ghost_cell::{GhostCell, GhostToken};
use paste::paste;
use std::{
    collections::HashMap,
    convert::Infallible,
    fmt::{self, Debug, Display, Formatter},
    hash::{Hash, Hasher},
};
use thiserror::Error;
use typed_arena::Arena;

macro_rules! try_check {
    ($this:ident, $dcel:ident) => {
        match $this.check($dcel) {
            Ok(x) => x,
            Err(e) => return Err(OperatorErr::new($this, e)),
        }
    };
}

use crate as dcel;

#[macro_use]
mod entity;
use entity::*;

mod entity_iterator;
pub use entity_iterator::*;

#[cfg(feature = "img")]
mod img;

#[cfg(feature = "img")]
pub use img::*;

mod obj_export;
pub use obj_export::*;

#[cfg(feature = "obj_import")]
mod obj_import;

#[cfg(feature = "obj_import")]
pub use obj_import::*;

#[cfg(test)]
mod tests;

mod mevvlfs;
pub use mevvlfs::*;

mod mev;
pub use mev::*;

mod mve;
pub use mve::*;

mod melf;
pub use melf::*;

mod mekh;
pub use mekh::*;

mod msev;
pub use msev::*;

mod mpkh;
pub use mpkh::*;

/// A trait equivalent to [`AsRef`], except with a built-in [reflexivity](https://doc.rust-lang.org/stable/std/convert/trait.AsRef.html#reflexivity) rule.
pub trait ReflAsRef<T> {
    fn as_ref(&self) -> &T;
}

impl<T> ReflAsRef<T> for T {
    fn as_ref(&self) -> &T {
        self
    }
}

/// A trait equivalent to [`AsMut`], except with a built-in [reflexivity](https://doc.rust-lang.org/stable/std/convert/trait.AsMut.html#reflexivity) rule.
pub trait ReflAsMut<T>: ReflAsRef<T> {
    fn as_mut(&mut self) -> &mut T;
}

impl<T> ReflAsMut<T> for T {
    fn as_mut(&mut self) -> &mut T {
        self
    }
}

struct DisplayFn<F: Fn(&mut Formatter) -> fmt::Result>(F);
impl<F: Fn(&mut Formatter) -> fmt::Result> Display for DisplayFn<F> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.0(f)
    }
}
impl<F: Fn(&mut Formatter) -> fmt::Result> Debug for DisplayFn<F> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.0(f)
    }
}

/// Returns a [`Ptr`] type for a given type, using `'brand` and `'arena` lifetimes from the scope.
///
/// `ptr_!(T)` expands to `dcel::Ptr<'brand, 'arena, T>`
///
/// This macro is useful versus [`ptr!`] if you don't want to populate the vertex data `V`
/// parameter from the environment.
///
/// # Examples
///
/// ```
/// use dcel::{ptr_t, Dcel, Vertex};
///
/// fn vertex_len<'brand, 'arena>(
///     vert: ptr_t!(Vertex<'brand, 'arena, [f32; 2]>), //
///     dcel: &Dcel<'brand, 'arena, [f32; 2]>,
/// ) -> f32 {
///     let [x, y] = vert.data(dcel);
///     (x * x + y * y).sqrt()
/// }
/// ```
#[macro_export]
macro_rules! ptr_t {
	($T:ty) => {
		dcel::Ptr<'brand, 'arena, $T>
	}
}

/// Returns a [`Ptr`] type for a given type, using `'brand` and `'arena` lifetimes and the vertex data parameter `V` from the scope.
///
/// `ptr!(T)` expands to `dcel::Ptr<'brand, 'arena, T<'brand, 'arena, V>>`
///
/// # Examples
///
/// ```
/// use dcel::{ptr, Dcel, Vertex};
/// use std::ops::Add;
///
/// fn vertex_sum<'brand, 'arena, O, V>(verts: [ptr!(Vertex); 2], dcel: &Dcel<'brand, 'arena, V>) -> O
/// where
///     for<'a> &'a V: Add<Output = O>
/// {
///     verts[0].data(dcel) + verts[1].data(dcel)
/// }
/// ```
#[macro_export]
macro_rules! ptr {
	($T:ident) => {
		dcel::Ptr<'brand, 'arena, $T<'brand, 'arena, V>>
	};
}

/// Returns a [`Own`] type for a given type, using `'brand` and `'arena` lifetimes from the scope.
///
/// `own_t!(T)` expands to `dcel::Own<'brand, 'arena, T>`
///
/// This macro is useful versus [`own!`] if you don't want to populate the vertex data `V`
/// parameter from the environment.
///
/// # Examples
///
/// ```
/// use dcel::{own_t, Dcel, Vertex, Edge};
///
/// fn sum_kve<'brand, 'arena>(
///     ops: Vec<(own_t!(Vertex<'brand, 'arena, u32>), own_t!(Edge<'brand, 'arena, u32>))>,
///     dcel: &mut Dcel<'brand, 'arena, u32>,
/// ) -> u32 {
///     ops
///         .into_iter()
///         .map(|(vertex, edge)| dcel.kve(edge, vertex).unwrap().data)
///         .sum()
/// }
/// ```
#[macro_export]
macro_rules! own_t {
	($T:ty) => {
		dcel::Own<'brand, 'arena, $T>
	}
}

/// Returns a [`Own`] type for a given type, using `'brand` and `'arena` lifetimes and the vertex data parameter `V` from the scope.
///
/// `own!(T)` expands to `dcel::Own<'brand, 'arena, T<'brand, 'arena, V>>`
///
/// # Examples
///
/// ```
/// use dcel::{own, Dcel, Vertex, Edge};
///
/// fn sum_kve<'brand, 'arena, V: std::iter::Sum>(
///     ops: Vec<(own!(Vertex), own!(Edge))>,
///     dcel: &mut Dcel<'brand, 'arena, V>,
/// ) -> V {
///     ops
///         .into_iter()
///         .map(|(vertex, edge)| dcel.kve(edge, vertex).unwrap().data)
///         .sum()
/// }
/// ```
#[macro_export]
macro_rules! own {
	($T:ident) => {
		dcel::Own<'brand, 'arena, $T<'brand, 'arena, V>>
	};
}

/// Returns a [`Lens`] type for a given type, using `'tok`, `'brand` and `'arena` lifetimes from the scope.
///
/// `lens_t!(T)` expands to `dcel::Lens<'tok, 'brand, 'arena, T>`
///
/// This macro is useful versus [`lens!`] if you don't want to populate the vertex data `V`
/// parameter from the environment.
///
/// # Examples
///
/// ```
/// use dcel::{lens_t, Dcel, Vertex};
///
/// fn vertex_len<'tok, 'brand, 'arena>(
///     vert: lens_t!(Vertex<'brand, 'arena, [f32; 2]>),
/// ) -> f32 {
///     let [x, y] = vert.data();
///     (x * x + y * y).sqrt()
/// }
/// ```
#[macro_export]
macro_rules! lens_t {
	($T:ty) => {
		dcel::Lens<'tok, 'brand, 'arena, $T>
	}
}

/// Returns a [`Lens`] type for a given type, using `'tok`, `'brand` and `'arena` lifetimes and the vertex data parameter `V` from the scope.
///
/// `lens!(T)` expands to `dcel::Lens<'tok, 'brand, 'arena, T<'brand, 'arena, V>>`
///
/// # Examples
///
/// ```
/// use dcel::{lens, Dcel, Vertex};
/// use std::ops::Add;
///
/// fn vertex_sum<'tok, 'brand, 'arena, O, V>(verts: [lens!(Vertex); 2]) -> O
/// where
///     for<'a> &'a V: Add<Output = O>
/// {
///     verts[0].data() + verts[1].data()
/// }
/// ```
#[macro_export]
macro_rules! lens {
	($T:ident) => {
		dcel::Lens<'tok, 'brand, 'arena, $T<'brand, 'arena, V>>
	};
}

/// For each identifier passed in, introduces a new binding shadowing the old one
/// containing a lens to what was previously a pointer. Takes a token as first argument.
///
/// # Examples
/// ```
/// use dcel::{mklens, Dcel, Kevvlfs};
///
/// Dcel::new(|mut dcel| {
///     let body = dcel.new_body();
///     let Kevvlfs {
///         edge,
///         face,
///         loop_,
///         shell,
///         ..
///     } = dcel.mevvlfs(*body, [4, 5]).unwrap();
///
///     mklens!(&dcel, edge, face, loop_, shell);
///
///     assert_eq!(face.outer_loop(), loop_);
///     assert_eq!(face.shell(), shell);
///     assert_eq!(edge.half_edges()[0].loop_(), loop_);
///     assert_eq!(edge.half_edges()[1].loop_(), loop_);
/// })
#[macro_export]
macro_rules! mklens {
	($token: expr, $($name:ident),*) => {
		$( let $name = $name.lens($token); )*
	};
}

fn short_debug_(ty: &'static str, id: usize, f: &mut Formatter) -> fmt::Result {
    f.debug_tuple(ty).field(&id).finish()
}

fn short_debug<'tok, 'brand, 'arena, T: Entity<'brand, 'arena>>(
    x: lens_t!(T),
    f: &mut Formatter,
) -> fmt::Result {
    short_debug_(T::type_name(), x.id(), f)
}

fn short_debug_fn<'tok, 'brand, 'arena, T: Entity<'brand, 'arena>>(x: lens_t!(T)) -> impl Debug {
    let id = x.id();
    DisplayFn(move |f| short_debug_(T::type_name(), id, f))
}

/*
fn short_debug_list<'tok, 'brand, 'arena, T, I>(iter: I, f: &mut Formatter) -> fmt::Result
where
    'brand: 'tok + 'arena,
    T: Entity<'brand, 'arena> + 'arena,
    I: Iterator<Item = lens_t!(T)>,
{
    f.debug_list().entries(iter.map(short_debug_fn)).finish()
}
*/

fn or_err<T>(cond: bool, err: T) -> Result<(), T> {
    if cond {
        Ok(())
    } else {
        Err(err)
    }
}

/// A non-owning pointer to a topological entity like a Vertex or a HalfEdge.
///
/// Being a wrapper around [`GhostCell`], it requires a reference to a [`GhostToken`] to access or mutate its contents.
///
/// [`Ptr`]s to different kinds of entities have different methods available to access their
/// contents and this is the primary way to read out their data. [`Ptr`] is also the primary way
/// to pass around entities.
///
/// # Safety
/// Entities can be killed while pointers to them are held, but the integrity of [`Ptr`]s
/// is ensured using generational references. Trying to access a [`Ptr`] pointing to an item that has been killed
/// results in a use after free panic, even when its memory is being reused.
pub struct Ptr<'brand, 'arena, T> {
    cell: &'arena GhostCell<'brand, T>,
    id: usize,
}

impl<'brand, 'arena, T> Clone for ptr_t!(T) {
    fn clone(&self) -> Self {
        *self
    }
}
impl<'brand, 'arena, T> Copy for ptr_t!(T) {}

#[allow(unused)]
impl<'brand, 'arena, T: Entity<'brand, 'arena>> ptr_t!(T) {
    fn new(cell: &'arena GhostCell<'brand, T>, token: &impl ReflAsRef<GhostToken<'brand>>) -> Self {
        let id = cell.borrow(token.as_ref()).id();
        Self { id, cell }
    }

    fn clear(self, token: &mut impl ReflAsMut<GhostToken<'brand>>) {
        self.borrow_mut(token).clear()
    }

    pub fn borrow<'tok, 'out>(self, token: &'tok impl ReflAsRef<GhostToken<'brand>>) -> &'out T
    where
        'arena: 'out,
        'tok: 'out,
    {
        let borrow = self.cell.borrow(token.as_ref());
        assert_eq!(borrow.maybe_id(), Some(self.id), "use after free");
        borrow
    }

    pub fn borrow_mut<'tok, 'out>(
        self,
        token: &'tok mut impl ReflAsMut<GhostToken<'brand>>,
    ) -> &'out mut T
    where
        'arena: 'out,
        'tok: 'out,
    {
        let borrow = self.cell.borrow_mut(token.as_mut());
        assert_eq!(borrow.maybe_id(), Some(self.id), "use after free");
        borrow
    }

    /// Creates a Lens holding this pointer and the given token.
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::{Dcel, Kevvlfs};
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let Kevvlfs { edge, face, .. } = dcel.mevvlfs(*body, [4, 5]).unwrap();
    ///
    ///     // without .lens()
    ///     assert!(edge.half_edges(&dcel)[0].loop_(&dcel).face(&dcel).eq(*face, &dcel));
    ///
    ///     // with .lens()
    ///     assert!(edge.lens(&dcel).half_edges()[0].loop_().face().eq(*face));
    /// })
    pub fn lens<'tok>(self, token: &'tok impl ReflAsRef<GhostToken<'brand>>) -> lens_t!(T) {
        Lens::new(self, token)
    }

    /// A unique id for the item referenced by this pointer.
    /// The id is unique *only* for items of the same type.
    ///
    /// # Example
    ///
    /// ```
    /// use dcel::{Dcel, Kevvlfs};
    ///
    /// Dcel::new(|mut dcel| {
    ///	    let body = dcel.new_body();
    ///     let Kevvlfs { edge, vertices: [a, b], .. } = dcel.mevvlfs(*body, [4, 4]).unwrap();
    ///
    ///     assert_ne!(a.id(&dcel), b.id(&dcel)); // IDs of two distinct vertices must be different
    ///     // assert_ne!(a.id(&dcel), edge.id(&dcel)); // WRONG! may panic
    /// })
    /// ```
    pub fn id(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> usize {
        self.borrow(token).id()
    }
    fn maybe_id(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> Option<usize> {
        self.borrow(token).maybe_id()
    }
    fn alive(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> bool {
        self.borrow(token).alive()
    }

    /// Compares the pointer to `other` by-reference.
    ///
    /// # Example
    ///
    /// ```
    /// use dcel::Dcel;
    ///
    /// Dcel::new(|mut dcel| {
    ///	    let body = dcel.new_body();
    ///     let [a, b] = dcel.mevvlfs(*body, [4, 4]).unwrap().vertices;
    ///
    ///     assert!(a.eq(*a, &dcel));
    ///     assert!(!a.eq(*b, &dcel));
    /// })
    /// ```
    pub fn eq(self, other: Self, token: &impl ReflAsRef<GhostToken<'brand>>) -> bool {
        self.borrow(token) == other.borrow(token)
    }

    fn next(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> Self {
        self.borrow(token).next()
    }
    fn maybe_next(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> Option<Self> {
        self.borrow(token).maybe_next()
    }
    fn set_next(self, x: Self, token: &mut impl ReflAsMut<GhostToken<'brand>>) {
        self.borrow_mut(token).set_next(x)
    }
    fn set_next_opt(self, x: Option<Self>, token: &mut impl ReflAsMut<GhostToken<'brand>>) {
        self.borrow_mut(token).set_next_opt(x)
    }

    fn prev(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> Self {
        self.borrow(token).prev()
    }
    fn maybe_prev(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> Option<Self> {
        self.borrow(token).maybe_prev()
    }
    fn set_prev(self, x: Self, token: &mut impl ReflAsMut<GhostToken<'brand>>) {
        self.borrow_mut(token).set_prev(x)
    }
    fn set_prev_opt(self, x: Option<Self>, token: &mut impl ReflAsMut<GhostToken<'brand>>) {
        self.borrow_mut(token).set_prev_opt(x)
    }
}

/// A owning pointer to a topological entity like a Vertex or a HalfEdge.
///
/// Operators that create entities return [`Own`]ing pointers to them. Unlike [`Ptr`], [`Own`]
/// does not implement [`Copy`]/[`Clone`], meaning that only one instance to it exists for a given
/// item. Similarly, operators that kill entities require [`Own`]ing pointers, preventing
/// conceptual double-free bugs at compile time.
///
/// [`Own`] dereferences to [`Ptr`].
///
/// # Safety
/// Since it is not feasible to keep around [`Own`] pointers for every application (for example,
/// traversing a mesh and killing parts of it based on read data in the form of [`Ptr`]s),
/// [`Own::unsafe_make_owned`] is provided, which turns a [`Ptr`] into an `[Own]`. Trying to free
/// the same entity twice results in an use after free panic.
pub struct Own<'brand, 'arena, T>(ptr_t!(T));

impl<'brand, 'arena, T> Own<'brand, 'arena, T> {
    /// Turns an [`Own`] into an [`Ptr`]. This is fully sound, but may cause runtime crashes
    /// if an entity is killed twice.
    ///
    /// Avoid this unless it really makes sense in your application to use it.
    pub fn unsafe_make_owned(this: ptr_t!(T)) -> Self {
        Self(this)
    }
}

impl<'brand, 'arena, T> Deref for own_t!(T) {
    type Target = ptr_t!(T);

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A wrapper around a [`Ptr`] that also contains an immutable GhostToken reference.
///
/// A [`Lens`] has the same methods as a [`Ptr`] (minus methods that require mutability)
/// except it does not require a [`GhostToken`] as argument since that is already stored.
/// [`Lens`] methods also return [`Lens`]es instead of [`Ptr`]s, which allows convenient traversal.
///
/// This also allows [`Lens`] to implement [`PartialEq`], [`Hash`] and [`Debug`], which [`Ptr`]
/// can't.
///
/// For documentation of [`Lens`] methods, see the [`Ptr`] equivalents.
///
/// Since holding an immutable borrow to the GhostToken prevents mutation of the [`Dcel`], lenses
/// are best used for read-only (parts of) tasks.
///
/// A [`Lens`] can be created either by using the [`Lens::new`] method or the [`Ptr::lens`] method.
///
/// # Examples
///
/// ```
/// use dcel::{Dcel, Kevvlfs};
///
/// Dcel::new(|mut dcel| {
///     let body = dcel.new_body();
///     let Kevvlfs { edge, face, .. } = dcel.mevvlfs(*body, [4, 5]).unwrap();
///
///     // without using lens
///     assert!(edge.half_edges(&dcel)[0].loop_(&dcel).face(&dcel).eq(*face, &dcel));
///
///     // using lens
///     assert!(edge.lens(&dcel).half_edges()[0].loop_().face().eq(*face));
/// })
pub struct Lens<'tok, 'brand, 'arena, T> {
    pub item: ptr_t!(T),
    pub token: &'tok GhostToken<'brand>,
}

impl<'tok, 'brand, 'arena, T> Clone for lens_t!(T) {
    fn clone(&self) -> Self {
        *self
    }
}
impl<'tok, 'brand, 'arena, T> Copy for lens_t!(T) {}

impl<'tok, 'brand, 'arena, T: Entity<'brand, 'arena>> PartialEq for lens_t!(T) {
    fn eq(&self, other: &Self) -> bool {
        self.item.borrow(self.token) == other.item.borrow(other.token)
    }
}
impl<'tok, 'brand, 'arena, T: Entity<'brand, 'arena>> Eq for lens_t!(T) {}

impl<'tok, 'brand, 'arena, T: Entity<'brand, 'arena> + Hash> Hash for lens_t!(T) {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.item.borrow(self.token).hash(state);
    }
}

impl<'tok, 'brand, 'arena, T> ReflAsRef<GhostToken<'brand>> for lens_t!(T) {
    fn as_ref(&self) -> &GhostToken<'brand> {
        self.token
    }
}

impl<'tok, 'brand, 'arena, T> From<lens_t!(T)> for ptr_t!(T) {
    fn from(x: lens_t!(T)) -> Self {
        x.item
    }
}

#[allow(unused)]
impl<'tok, 'brand, 'arena, T: Entity<'brand, 'arena>> lens_t!(T) {
    pub fn new(item: ptr_t!(T), token: &'tok impl ReflAsRef<GhostToken<'brand>>) -> Self {
        Self {
            item,
            token: token.as_ref(),
        }
    }

    pub fn id(self) -> usize {
        self.item.id(&self)
    }
    fn maybe_id(self) -> Option<usize> {
        self.item.maybe_id(&self)
    }
    fn alive(self) -> bool {
        self.item.alive(&self)
    }

    pub fn eq(self, other: ptr_t!(T)) -> bool {
        self.item.eq(other, &self)
    }

    fn next(self) -> Self {
        self.item.next(&self).lens(self.token)
    }
    fn maybe_next(self) -> Option<Self> {
        self.item.maybe_next(&self).map(|x| x.lens(self.token))
    }

    fn prev(self) -> Self {
        self.item.prev(self.token).lens(self.token)
    }
    fn maybe_prev(self) -> Option<Self> {
        self.item.maybe_prev(&self).map(|x| x.lens(self.token))
    }
}

entity!(vertex: Vertex (init: V),
    data: Option<V> = Some(init);
    outgoing: HalfEdge
);

/// An iterator over the outgoing HalfEdges from a vertex.
///
/// See [ptr!(Vertex)::iter_outgoing] for details.
///
/// [ptr!(Vertex)::iter_outgoing]: dcel::Ptr#method.iter_outgoing
pub struct OutgoingIterator<'tok, 'brand, 'arena, V>(Option<(lens!(HalfEdge), lens!(HalfEdge))>);

impl<'tok, 'brand, 'arena, V> Clone for OutgoingIterator<'tok, 'brand, 'arena, V> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'tok, 'brand, 'arena, V> Copy for OutgoingIterator<'tok, 'brand, 'arena, V> {}

impl<'tok, 'brand, 'arena, V> OutgoingIterator<'tok, 'brand, 'arena, V> {
    fn new(start: Option<ptr!(HalfEdge)>, token: &'tok impl ReflAsRef<GhostToken<'brand>>) -> Self {
        Self(start.map(|s| {
            let l = Lens::new(s, token);
            (l, l)
        }))
    }
}

impl<'tok, 'brand, 'arena, V> Iterator for OutgoingIterator<'tok, 'brand, 'arena, V> {
    type Item = lens!(HalfEdge);

    fn next(&mut self) -> Option<Self::Item> {
        let range = self.0.as_mut()?;
        let ret = range.0;

        range.0 = range.0.twin().next();
        if range.0 == range.1 {
            self.0 = None;
        }

        Some(ret)
    }
}

impl<'brand, 'arena, V> own!(Vertex) {
    fn destroy(self, dcel: &mut Dcel<'brand, 'arena, V>) -> V {
        let data = self.borrow_mut(dcel).data.take().unwrap();
        self.free(dcel);
        data
    }
}

impl<'brand, 'arena, V> ptr!(Vertex) {
    /// Returns an immutable borrow to the user-data associated with the vertex.
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::Dcel;
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let [_, vertex] = dcel.mevvlfs(*body, [4, 5]).unwrap().vertices;
    ///
    ///     assert_eq!(*vertex.data(&dcel), 5);
    /// })
    pub fn data<'tok, 'out>(self, token: &'tok impl ReflAsRef<GhostToken<'brand>>) -> &'out V
    where
        'arena: 'out,
        'tok: 'out,
    {
        self.borrow(token).data.as_ref().unwrap()
    }

    /// Returns a mutable borrow to the user-data associated with the vertex.
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::Dcel;
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let [_, vertex] = dcel.mevvlfs(*body, [4, 5]).unwrap().vertices;
    ///
    ///     *vertex.mut_data(&mut dcel) = 10;
    ///     assert_eq!(*vertex.data(&dcel), 10);
    /// })
    pub fn mut_data<'tok, 'out>(
        self,
        token: &'tok mut impl ReflAsMut<GhostToken<'brand>>,
    ) -> &'out mut V
    where
        'arena: 'out,
        'tok: 'out,
    {
        self.borrow_mut(token).data.as_mut().unwrap()
    }

    /// Returns an iterator over lenses to all half-edges going out of this vertex
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::{Dcel, Kevvlfs};
    /// use std::iter::once;
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let Kevvlfs { edge, vertices: [vertex, _], .. } = dcel.mevvlfs(*body, [4, 5]).unwrap();
    ///     let [a, b] = edge.lens(&dcel).half_edges();
    ///     let outgoing = vertex.iter_outgoing(&dcel);
    ///
    ///     assert!(outgoing.eq(once(a)) || outgoing.eq(once(b)));
    /// })
    pub fn iter_outgoing<'tok>(
        self,
        token: &'tok impl ReflAsRef<GhostToken<'brand>>,
    ) -> OutgoingIterator<'tok, 'brand, 'arena, V> {
        // FIXME: maybe enforce at least one item by using Some(self.outgoing())
        // there should be no "standalone" vertices (?)
        OutgoingIterator::new(self.maybe_outgoing(token), token)
    }

    /// Returns a half-edge going out of this vertex belonging to a given loop, if one exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::{Dcel, Kevvlfs};
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let Kevvlfs { edge, vertices: [vertex, _], loop_, .. } = dcel.mevvlfs(*body, [4, 5]).unwrap();
    ///     let [a, b] = edge.lens(&dcel).half_edges();
    ///     let outgoing = vertex.find_outgoing(*loop_, &dcel).unwrap();
    ///
    ///     assert!(a.eq(outgoing) || b.eq(outgoing));
    /// })
    pub fn find_outgoing(
        self,
        loop_: ptr!(Loop),
        token: &impl ReflAsRef<GhostToken<'brand>>,
    ) -> Option<ptr!(HalfEdge)> {
        self.lens(token).find_outgoing(loop_).map(|x| x.item)
    }
}

impl<'tok, 'brand, 'arena, V> lens!(Vertex) {
    pub fn data(&self) -> &V {
        self.item.data(self)
    }

    pub fn iter_outgoing(self) -> OutgoingIterator<'tok, 'brand, 'arena, V> {
        self.item.iter_outgoing(self.token)
    }

    pub fn find_outgoing(self, loop_: ptr!(Loop)) -> Option<lens!(HalfEdge)> {
        self.iter_outgoing().find(|x| x.loop_().eq(loop_))
    }

    fn debug_data(self, f: &mut Formatter) -> fmt::Result
    where
        V: Debug,
    {
        self.data().fmt(f)
    }
}

entity!(half_edge: HalfEdge;
    /// Returns the Vertex this half-edge is anchored on (dual of target).
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::{mklens, Dcel, Kevvlfs};
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let Kevvlfs { edge, vertices: [v1, v2], .. } = dcel.mevvlfs(*body, [4, 5]).unwrap();
    ///     let [x1, x2] = edge.half_edges(&dcel).map(|x| x.origin(&dcel));
    ///     mklens!(&dcel, v1, v2, x1, x2);
    ///
    ///     assert!([x1, x2] == [v1, v2] || [x1, x2] == [v2, v1]);
    /// })
    pub origin: Vertex,
    /// Returns the twin of this HalfEdge.
    ///
    /// Twins have their target/origin swapped and face in opposite directions.
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::Dcel;
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let edge = dcel.mevvlfs(*body, [4, 5]).unwrap().edge;
    ///     let [a, b] = edge.half_edges(&dcel);
    ///
    ///     assert!(a.twin(&dcel).eq(b, &dcel));
    ///     assert!(b.twin(&dcel).eq(a, &dcel));
    /// })
    pub twin: HalfEdge,
    /// Returns a back pointer to the Loop this HalfEdge belongs is part of.
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::{Dcel, Kevvlfs};
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let Kevvlfs { edge, loop_, .. } = dcel.mevvlfs(*body, [4, 5]).unwrap();
    ///     let [a, b] = edge.half_edges(&dcel);
    ///
    ///     assert!(a.loop_(&dcel).eq(*loop_, &dcel));
    ///     assert!(b.loop_(&dcel).eq(*loop_, &dcel));
    /// })
    pub loop_: Loop,
    /// Returns a back pointer to the Edge (combination of both twins) this HalfEdge belongs to.
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::Dcel;
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let edge = dcel.mevvlfs(*body, [4, 5]).unwrap().edge;
    ///     let [a, b] = edge.half_edges(&dcel);
    ///
    ///     assert!(a.edge(&dcel).eq(*edge, &dcel));
    ///     assert!(b.edge(&dcel).eq(*edge, &dcel));
    /// })
    pub edge: Edge
);

impl<'brand, 'arena, V> ptr!(HalfEdge) {
    /// Returns the vertex this half-edge points to (dual of origin).
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::{Dcel, Kevvlfs};
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let Kevvlfs { edge, vertices: [mut v1, mut v2], .. } = dcel.mevvlfs(*body, [4, 5]).unwrap();
    ///     let [a, b] = edge.lens(&dcel).half_edges();
    ///
    ///     if a.origin().eq(*v2) {
    ///	        [v1, v2] = [v2, v1];
    ///     }
    ///
    ///     assert!(b.target().eq(*v1));
    ///     assert!(a.target().eq(*v2));
    /// })
    pub fn target(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> ptr!(Vertex) {
        self.twin(token).origin(token)
    }

    fn update_origin(self, v: ptr!(Vertex), token: &mut impl ReflAsMut<GhostToken<'brand>>) {
        self.set_origin(v, token);
        v.set_outgoing(self, token);
    }
}

impl<'tok, 'brand, 'arena, V> lens!(HalfEdge) {
    pub fn target(self) -> lens!(Vertex) {
        self.item.target(&self).lens(self.token)
    }
}

entity!(loop_: Loop;
    half_edges[
        /// Returns an iterator over the half-edges this loop is made of, starting with an arbitrary one.
        ///
        /// # Examples
        ///
        /// ```
        /// use dcel::{Dcel, Kevvlfs};
        ///
        /// Dcel::new(|mut dcel| {
        ///     let body = dcel.new_body();
        ///     let Kevvlfs { edge, loop_, .. } = dcel.mevvlfs(*body, [4, 5]).unwrap();
        ///     let [a, b] = edge.lens(&dcel).half_edges();
        ///     let half_edges = loop_.iter_half_edges(&dcel);
        ///
        ///     assert!(half_edges.eq([a, b]) || half_edges.eq([b, a]));
        /// })
        half_edge: half_edge back]: HalfEdge,
    /// Returns a back pointer to the Face this Loop belongs to.
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::{Dcel, Kevvlfs};
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let Kevvlfs { loop_, face, ..  } = dcel.mevvlfs(*body, [4, 5]).unwrap();
    ///
    ///     assert!(loop_.face(&dcel).eq(*face, &dcel));
    /// })
    pub face: Face
);

impl<'brand, 'arena, V> ptr!(Loop) {
    /// Returns true if this loop is the outer loop of its face.
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::Dcel;
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let loop_ = dcel.mevvlfs(*body, [4, 5]).unwrap().loop_;
    ///
    ///     assert!(loop_.is_outer(&dcel));
    /// })
    pub fn is_outer(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> bool {
        self.lens(token).is_outer()
    }

    fn update_connectivity(self, token: &mut impl ReflAsMut<GhostToken<'brand>>) {
        self.iter_mut_half_edges(token, |x, token| x.set_loop_(self, token));
    }
}

impl<'tok, 'brand, 'arena, V> lens!(Loop) {
    pub fn is_outer(self) -> bool {
        self.face().outer_loop() == self
    }
}

entity!(edge: Edge,
    half_edges: [Option<own!(HalfEdge)>; 2] = [None, None]
);

impl<'brand, 'arena, V> Edge<'brand, 'arena, V> {
    fn create(
        shell: ptr!(Shell),
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> (own!(Edge), [ptr!(HalfEdge); 2]) {
        let edge = shell.add_new_edge(dcel);

        let he1_own = HalfEdge::new(dcel);
        let he2_own = HalfEdge::new(dcel);

        let he1 = *he1_own;
        let he2 = *he2_own;

        edge.borrow_mut(dcel).half_edges = [Some(he1_own), Some(he2_own)];
        // edge.set_half_edges([he1_own, he2_own], dcel);

        he1.set_twin(he2, dcel);
        he2.set_twin(he1, dcel);
        he1.set_edge(*edge, dcel);
        he2.set_edge(*edge, dcel);

        (edge, [he1, he2])
    }
}

impl<'brand, 'arena, V> own!(Edge) {
    fn destroy(self, dcel: &mut Dcel<'brand, 'arena, V>) {
        for x in self
            .borrow_mut(dcel)
            .half_edges
            .each_mut()
            .map(Option::take)
            .into_iter()
            .flatten()
        {
            x.free(dcel);
        }
        self.free(dcel);
    }
}

impl<'brand, 'arena, V> ptr!(Edge) {
    /// Returns the two half-edges associated with this edge.
    ///
    /// The half edges are twins and facing in opposite directions.
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::Dcel;
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let edge = dcel.mevvlfs(*body, [4, 5]).unwrap().edge;
    ///     let [a, b] = edge.half_edges(&dcel);
    ///
    ///     assert!(a.twin(&dcel).eq(b, &dcel));
    ///     assert!(b.twin(&dcel).eq(a, &dcel));
    /// })
    pub fn half_edges(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> [ptr!(HalfEdge); 2] {
        self.borrow(token)
            .half_edges
            .each_ref()
            .map(|x| *x.as_deref().unwrap())
    }

    /// Returns the origin vertices of the two half-edges associated with this edge.
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::{mklens, Dcel, Kevvlfs};
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let Kevvlfs { edge, vertices: [v1, v2], .. } = dcel.mevvlfs(*body, [4, 5]).unwrap();
    ///     let verts = edge.vertices(&dcel).map(|x| x.lens(&dcel));
    ///     mklens!(&dcel, v1, v2);
    ///
    ///     assert!(verts == [v1, v2] || verts == [v2, v1]);
    /// })
    pub fn vertices(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> [ptr!(Vertex); 2] {
        self.half_edges(token).map(|x| x.origin(token))
    }
}

impl<'tok, 'brand, 'arena, V> lens!(Edge) {
    pub fn half_edges(self) -> [lens!(HalfEdge); 2] {
        self.item.half_edges(self.token).map(|x| x.lens(self.token))
    }

    pub fn vertices(self) -> [lens!(Vertex); 2] {
        self.item.vertices(self.token).map(|x| x.lens(self.token))
    }

    fn debug_half_edges(self, f: &mut Formatter) -> fmt::Result
    where
        V: Debug,
    {
        f.debug_list().entries(self.half_edges()).finish()
    }
}

entity!(face: Face;
    /// Returns the outer (peripheral) Loop of this face.
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::{Dcel, Kevvlfs};
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let Kevvlfs { loop_, face, .. } = dcel.mevvlfs(*body, [4, 5]).unwrap();
    ///
    ///     assert!(face.outer_loop(&dcel).eq(*loop_, &dcel));
    /// })
    pub outer_loop: Loop,
    inner_loops[
        /// Returns an iterator over the inner (hole) Loops of this face.
        ///
        /// # Examples
        ///
        /// ```
        /// use dcel::Dcel;
        ///
        /// Dcel::new(|mut dcel| {
        ///     let body = dcel.new_body();
        ///     let face = dcel.mevvlfs(*body, [4, 5]).unwrap().face;
        ///
        ///     assert!(face.iter_inner_loops(&dcel).next().is_none());
        /// })
        inner_loop: loop_ back]: Loop,
    /// Returns a back pointer to the Shell this Face belongs to.
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::{Dcel, Kevvlfs};
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let Kevvlfs { face, shell, .. } = dcel.mevvlfs(*body, [4, 5]).unwrap();
    ///
    ///     assert!(face.shell(&dcel).eq(*shell, &dcel));
    /// })
    pub shell: Shell
);

impl<'brand, 'arena, V> own!(Face) {
    fn destroy(self, dcel: &mut Dcel<'brand, 'arena, V>) {
        Own::unsafe_make_owned(self.outer_loop(dcel)).free(dcel);
        self.iter_mut_inner_loops(dcel, |x, dcel| {
            Own::unsafe_make_owned(x).free(dcel);
        });
        self.free(dcel);
    }
}

entity!(shell: Shell;
    faces[
        /// Returns an iterator over all faces in this shell.
        ///
        /// # Examples
        ///
        /// ```
        /// use dcel::{Dcel, Kevvlfs};
        /// use std::iter::once;
        ///
        /// Dcel::new(|mut dcel| {
        ///     let body = dcel.new_body();
        ///     let Kevvlfs { face, shell, .. } = dcel.mevvlfs(*body, [4, 5]).unwrap();
        ///
        ///     assert!(shell.iter_faces(&dcel).eq(once(face.lens(&dcel))));
        /// })
        face: face back]: Face,
    edges[
        /// Returns an iterator over all faces in this shell.
        ///
        /// # Examples
        ///
        /// ```
        /// use dcel::{Dcel, Kevvlfs};
        /// use std::iter::once;
        ///
        /// Dcel::new(|mut dcel| {
        ///     let body = dcel.new_body();
        ///     let Kevvlfs { edge, shell, .. } = dcel.mevvlfs(*body, [4, 5]).unwrap();
        ///
        ///     assert!(shell.iter_edges(&dcel).eq(once(edge.lens(&dcel))));
        /// })
        edge: edge]: Edge,
    vertices[
        /// Returns an iterator over all faces in this shell.
        ///
        /// # Examples
        ///
        /// ```
        /// use dcel::{mklens, Dcel, Kevvlfs};
        ///
        /// Dcel::new(|mut dcel| {
        ///     let body = dcel.new_body();
        ///     let Kevvlfs { vertices: [v1, v2], shell, .. } = dcel.mevvlfs(*body, [4, 5]).unwrap();
        ///     mklens!(&dcel, v1, v2);
        ///     let verts = shell.iter_vertices(&dcel);
        ///
        ///     assert!(verts.eq([v1, v2]) || verts.eq([v2, v1]));
        /// })
        vertex: vertex (V)]: Vertex,
    /// Returns a back pointer to the Body this Shell belongs to.
    ///
    /// # Examples
    ///
    /// ```
    /// use dcel::Dcel;
    ///
    /// Dcel::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     let shell = dcel.mevvlfs(*body, [4, 5]).unwrap().shell;
    ///
    ///     assert!(shell.body(&dcel).eq(*body, &dcel));
    /// })
    pub body: Body
);

impl<'brand, 'arena, V> own!(Shell) {
    fn destroy(self, dcel: &mut Dcel<'brand, 'arena, V>) {
        self.iter_mut_faces(dcel, |x, dcel| {
            Own::unsafe_make_owned(x).destroy(dcel);
        });
        self.iter_mut_edges(dcel, |x, dcel| {
            Own::unsafe_make_owned(x).destroy(dcel);
        });
        self.iter_mut_vertices(dcel, |x, dcel| {
            Own::unsafe_make_owned(x).destroy(dcel);
        });
        self.free(dcel);
    }
}

entity!(body: Body;
    shells[
        /// Returns an iterator over all shells in this body.
        ///
        /// # Examples
        ///
        /// ```
        /// use dcel::Dcel;
        /// use std::iter::once;
        ///
        /// Dcel::new(|mut dcel| {
        ///     let body = dcel.new_body();
        ///     let shell = dcel.mevvlfs(*body, [4, 5]).unwrap().shell;
        ///
        ///     assert!(body.iter_shells(&dcel).eq(once(shell.lens(&dcel))));
        /// })
        shell: shell back]: Shell
);

impl<'brand, 'arena, V> own!(Body) {
    fn destroy(self, dcel: &mut Dcel<'brand, 'arena, V>) {
        self.iter_mut_shells(dcel, |x, dcel| {
            Own::unsafe_make_owned(x).destroy(dcel);
        });
        dcel.delete_body(self).unwrap();
    }
}

struct Allocator<'brand, 'arena, T: Entity<'brand, 'arena>> {
    next_id: usize,
    arena: &'arena Arena<T>,
    freelist: Vec<&'arena GhostCell<'brand, T>>,
}

impl<'brand, 'arena, T: Entity<'brand, 'arena>> Allocator<'brand, 'arena, T> {
    fn new(arena: &'arena Arena<T>) -> Self {
        Self {
            next_id: 0,
            arena,
            freelist: Vec::new(),
        }
    }

    fn next_id(&mut self) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    fn alloc(&mut self, x: T, token: &mut impl ReflAsMut<GhostToken<'brand>>) -> own_t!(T) {
        Own::unsafe_make_owned(Ptr::new(
            if let Some(cell) = self.freelist.pop() {
                *cell.borrow_mut(token.as_mut()) = x;
                cell
            } else {
                GhostCell::from_mut(self.arena.alloc(x))
            },
            token,
        ))
    }

    fn free(&mut self, token: &mut impl ReflAsMut<GhostToken<'brand>>, ptr: own_t!(T)) {
        let _ = ptr.id(token); // to prevent double free
        ptr.clear(token);
        self.freelist.push(ptr.cell);
    }
}

pub struct OperatorErr<T, E> {
    pub op: T,
    pub err: E,
}

impl<T, E> OperatorErr<T, E> {
    pub fn new(op: T, err: E) -> Self {
        Self { op, err }
    }
}

impl<T, E: std::error::Error> std::error::Error for OperatorErr<T, E> {}
impl<T, E: Debug> Debug for OperatorErr<T, E> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.err.fmt(f)
    }
}
impl<T, E: Display> Display for OperatorErr<T, E> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.err.fmt(f)
    }
}

/// A trait for Euler-Operators with preconditions and inverse operations.
pub trait Operator<'brand, 'arena, V>: Sized {
    /// The inverse of the operation, created by applying it.
    /// Applying the inverse should revert the operation.
    /// This may not work if other operators have been used to modify the DCEL in the meantime.
    type Inverse: Operator<'brand, 'arena, V>;

    /// Error returned on precondition failure.
    type Error: std::error::Error;

    /// Info returned by precondition success.
    type Check;

    /// Check if preconditions are met without making any modifications to the DCEL.
    ///
    /// On precondition failure, an error indicating the reason for the failure is returned.
    ///
    /// On precondition success, this method may return additional info computed during
    /// precondition checking and used by the [`Operator::apply`] method.
    ///
    /// [`Operator::apply`] calls this method to check for preconditions.
    fn check(&self, dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error>;

    /// Check for preconditions and run the operation, taking ownership of it.
    ///
    /// On precondition failure, an [`OperatorErr`] is returned, which contains both an error
    /// as well as the original operation passed in, for recovery purposes.
    ///
    /// On precondition success, the DCEL is modified and the inverse operation is returned.
    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>>;
}

/// A struct containing typed arena allocators for entities used by [`Dcel`].
///
/// Use [`Default::default()`] to construct this, or create [`Arena`] structs individually.
pub struct DcelArena<'brand, 'arena, V> {
    pub vertex: Arena<Vertex<'brand, 'arena, V>>,
    pub half_edge: Arena<HalfEdge<'brand, 'arena, V>>,
    pub loop_: Arena<Loop<'brand, 'arena, V>>,
    pub edge: Arena<Edge<'brand, 'arena, V>>,
    pub face: Arena<Face<'brand, 'arena, V>>,
    pub shell: Arena<Shell<'brand, 'arena, V>>,
    pub body: Arena<Body<'brand, 'arena, V>>,
}

impl<'brand, 'arena, V> Default for DcelArena<'brand, 'arena, V> {
    fn default() -> Self {
        Self {
            vertex: Default::default(),
            half_edge: Default::default(),
            loop_: Default::default(),
            edge: Default::default(),
            face: Default::default(),
            shell: Default::default(),
            body: Default::default(),
        }
    }
}

/// A doubly-connected edge-list.
///
/// Use [`Dcel::new`] to create a DCEL with a new [`GhostToken`] or [`Dcel::from_token`] to create one for an existing [`GhostToken`].
pub struct Dcel<'brand, 'arena, V> {
    pub token: GhostToken<'brand>,
    vertex: Allocator<'brand, 'arena, Vertex<'brand, 'arena, V>>,
    half_edge: Allocator<'brand, 'arena, HalfEdge<'brand, 'arena, V>>,
    loop_: Allocator<'brand, 'arena, Loop<'brand, 'arena, V>>,
    edge: Allocator<'brand, 'arena, Edge<'brand, 'arena, V>>,
    face: Allocator<'brand, 'arena, Face<'brand, 'arena, V>>,
    shell: Allocator<'brand, 'arena, Shell<'brand, 'arena, V>>,
    body: Allocator<'brand, 'arena, Body<'brand, 'arena, V>>,
    bodies: Option<ptr!(Body)>,
}

impl<'brand, 'arena, V> ReflAsRef<GhostToken<'brand>> for Dcel<'brand, 'arena, V> {
    fn as_ref(&self) -> &GhostToken<'brand> {
        &self.token
    }
}

impl<'brand, 'arena, V> ReflAsMut<GhostToken<'brand>> for Dcel<'brand, 'arena, V> {
    fn as_mut(&mut self) -> &mut GhostToken<'brand> {
        &mut self.token
    }
}

impl<'brand, 'arena, V> Dcel<'brand, 'arena, V> {
    /// Creates a new DCEL with a new [`GhostToken`] and default arena allocators.
    #[allow(clippy::new_ret_no_self)]
    pub fn new<R, F>(fun: F) -> R
    where
        for<'new_brand, 'new_arena> F: FnOnce(Dcel<'new_brand, 'new_arena, V>) -> R,
    {
        GhostToken::new(|token| {
            let arena = DcelArena::default();
            let dcel = Dcel::from_token(token, &arena);

            fun(dcel)
        })
    }

    /// Creates a DCEL associated with the given [`GhostToken`] and using the arena allocators passed in.
    pub fn from_token(token: GhostToken<'brand>, ar: &'arena DcelArena<'brand, 'arena, V>) -> Self {
        Self {
            token,
            bodies: None,
            vertex: Allocator::new(&ar.vertex),
            half_edge: Allocator::new(&ar.half_edge),
            loop_: Allocator::new(&ar.loop_),
            edge: Allocator::new(&ar.edge),
            face: Allocator::new(&ar.face),
            shell: Allocator::new(&ar.shell),
            body: Allocator::new(&ar.body),
        }
    }

    /// Adds a new, empty body to the DCEL.
    ///
    /// # Examples
    /// ```
    /// use dcel::Dcel;
    ///
    /// Dcel::<()>::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     /* ... */
    /// })
    /// ```
    pub fn new_body(&mut self) -> own!(Body) {
        let body = Body::new(self);
        self.bodies = Some(Entity::list_add(*body, self.bodies, self));
        body
    }

    /// Removes a body from the DCEL.
    ///
    /// Requires the body to be empty. Ok is returned on success, if the body is non-empty (has shells), Err is returned
    ///
    /// # Examples
    /// ```
    /// use dcel::Dcel;
    ///
    /// Dcel::<()>::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     dcel.delete_body(body).unwrap();
    /// })
    /// ```
    pub fn delete_body(&mut self, body: own!(Body)) -> Result<(), ()> {
        if body.maybe_shells(self).is_some() {
            return Err(());
        }
        self.bodies = Entity::list_remove(*body, self);
        body.free(self);
        Ok(())
    }

    /// Returns an iterator over all bodies in the DCEL.
    ///
    /// # Examples
    /// ```
    /// use dcel::Dcel;
    /// use std::iter::once;
    ///
    /// Dcel::<()>::new(|mut dcel| {
    ///     let body = dcel.new_body();
    ///     assert!(dcel.iter_bodies().eq(once(body.lens(&dcel))));
    /// })
    /// ```
    pub fn iter_bodies<'tok>(
        &'tok self,
    ) -> EntityIterator<'tok, 'brand, 'arena, Body<'brand, 'arena, V>> {
        EntityIterator::new(self.bodies, self)
    }

    fn follow(&mut self, prev: ptr!(HalfEdge), next: ptr!(HalfEdge)) {
        next.set_prev(prev, self);
        prev.set_next(next, self);
    }

    /// Make-Edge-Vertex-Vertex-Loop-Face-Shell
    ///
    /// This corresponds to MEVVLS in SNUMOD and is the inverse of kevvlfs. Adds a new shell with two vertices connected by an
    /// edge. Both half edges in the edge form a loop that is the outer loop of a new face.
    /// No preconditions.
    ///
    /// For examples, see `src/tests.rs`
    pub fn mevvlfs(
        &mut self,
        body: ptr!(Body),
        data: [V; 2],
    ) -> Result<Kevvlfs<'brand, 'arena, V>, OperatorErr<Mevvlfs<'brand, 'arena, V>, Infallible>>
    {
        Mevvlfs::new(body, data).apply(self)
    }

    /// Kill-Edge-Vertex-Vertex-Loop-Face-Shell
    ///
    /// This corresponds to KEVVLS in SNUMOD and is the inverse of mevvlfs. Removes a shell and two vertices connected by an
    /// edge, as well as a face and it's outer loop. The relationships between the entities
    /// must be as described in [`Dcel::mevvlfs`], and the vertices, edge, and face must be
    /// the only ones in the shell.
    ///
    /// For examples, see `src/tests.rs`
    pub fn kevvlfs(
        &mut self,
        edge: own!(Edge),
        vertices: [own!(Vertex); 2],
        loop_: own!(Loop),
        face: own!(Face),
        shell: own!(Shell),
    ) -> Result<Mevvlfs<'brand, 'arena, V>, OperatorErr<Kevvlfs<'brand, 'arena, V>, KevvlfsError>>
    {
        Kevvlfs::new(edge, vertices, loop_, face, shell).apply(self)
    }

    /// Make-Edge-Vertex
    ///
    /// This corresponds to MEV in SNUMOD and is the inverse of kev. Adds a vertex connected to an existing vertex via an
    /// edge going back and forth. Both half-edges of the new edge will be added to the given loop.
    /// The given vertex must be part of the given loop.
    ///
    /// For examples, see `src/tests.rs`
    pub fn mev(
        &mut self,
        loop_: ptr!(Loop),
        vertex: ptr!(Vertex),
        data: V,
    ) -> Result<Kev<'brand, 'arena, V>, OperatorErr<Mev<'brand, 'arena, V>, MevError>> {
        Mev::new(loop_, vertex, data).apply(self)
    }

    /// Kill-Edge-Vertex
    ///
    /// This corresponds to KEV in SNUMOD and is the inverse of mev. Removes a vertex connected to an existing vertex via an
    /// edge going back and forth. The vertex to be removed must only be connected to one other vertex, using the given edge only.
    ///
    /// For examples, see `src/tests.rs`
    pub fn kev(
        &mut self,
        edge: own!(Edge),
        vertex: own!(Vertex),
    ) -> Result<Mev<'brand, 'arena, V>, OperatorErr<Kev<'brand, 'arena, V>, KevError>> {
        Kev::new(edge, vertex).apply(self)
    }

    /// Make-Edge-Loop-Face
    ///
    /// This corresponds to MEL in SNUMOD and is the inverse of kelf. Connects two existing vertices both part of the same
    /// loop, creating a new face (and outer loop)
    ///
    /// For examples, see `src/tests.rs`
    pub fn melf(
        &mut self,
        vertices: [ptr!(Vertex); 2],
        loop_: ptr!(Loop),
    ) -> Result<Kelf<'brand, 'arena, V>, OperatorErr<Melf<'brand, 'arena, V>, MelfError>> {
        Melf::new(vertices, loop_).apply(self)
    }

    /// Make-Edge-Loop-Face
    ///
    /// This corresponds to KEL in SNUMOD and is the inverse of melf. Removes an existing edge
    /// between two vertices, joining two loops in the process, removing one of them (must be
    /// passed in as an owned pointer). The given loop must be the outer loop of the given face,
    /// which must not have inner loops.
    ///
    /// For examples, see `src/tests.rs`
    pub fn kelf(
        &mut self,
        edge: own!(Edge),
        loop_: own!(Loop),
        face: own!(Face),
    ) -> Result<Melf<'brand, 'arena, V>, OperatorErr<Kelf<'brand, 'arena, V>, KelfError>> {
        Kelf::new(edge, loop_, face).apply(self)
    }

    /// Make-Vertex-Edge
    ///
    /// This corresponds to MVE in SNUMOD and is the inverse of kve. Adds a new vertex in the
    /// middle of an existing edge, splitting the edge in two. No preconditions.
    ///
    /// For examples, see `src/tests.rs`
    pub fn mve(
        &mut self,
        edge: ptr!(Edge),
        data: V,
    ) -> Result<Kve<'brand, 'arena, V>, OperatorErr<Mve<'brand, 'arena, V>, Infallible>> {
        Mve::new(edge, data).apply(self)
    }

    /// Kill-Vertex-Edge
    ///
    /// This corresponds to KVE in SNUMOD and is the inverse of mve. Removes a vertex
    /// that exists between two other vertices using two edges, connected to one of the by the given edge, which
    /// is removed (joined with the other edge). The vertex must not be connected to any
    /// other edges.
    ///
    /// For examples, see `src/tests.rs`
    pub fn kve(
        &mut self,
        edge: own!(Edge),
        vertex: own!(Vertex),
    ) -> Result<Mve<'brand, 'arena, V>, OperatorErr<Kve<'brand, 'arena, V>, KveError>> {
        Kve::new(edge, vertex).apply(self)
    }

    /// Make-Edge-Kill-Hole
    ///
    /// This corresponds to MEKH in SNUMOD and is the inverse of kemh. Two loops that are part of
    /// the same face are joined by making an edge between two given vertices part of each loop respectively.
    /// The loop being removed must now be an outer loop, and a loop cannot be joined with itself.
    ///
    /// For examples, see `src/tests.rs`
    pub fn mekh(
        &mut self,
        shell: ptr!(Shell),
        into_loop: ptr!(Loop),
        into_vertex: ptr!(Vertex),
        hole_loop: own!(Loop),
        hole_vertex: ptr!(Vertex),
    ) -> Result<Kemh<'brand, 'arena, V>, OperatorErr<Mekh<'brand, 'arena, V>, MekhError>> {
        Mekh::new(shell, into_loop, into_vertex, hole_loop, hole_vertex).apply(self)
    }

    /// Make-Edge-Kill-Hole
    ///
    /// This corresponds to KEMH in SNUMOD and is the inverse of mekh. An edge going back and forth
    /// between two vertices is removed, splitting a loop into two loops, adding a new hole loop.
    ///
    /// For examples, see `src/tests.rs`
    pub fn kemh(
        &mut self,
        shell: ptr!(Shell),
        edge: own!(Edge),
        loop_: ptr!(Loop),
        hole_vertex: ptr!(Vertex),
    ) -> Result<Mekh<'brand, 'arena, V>, OperatorErr<Kemh<'brand, 'arena, V>, KemhError>> {
        Kemh::new(shell, edge, loop_, hole_vertex).apply(self)
    }

    /// Make-Split-Edge-Vertex
    ///
    /// This corresponds to MZEV in SNUMOD with the exception of not (necessarily) creating a zero-length edge and is the inverse of ksev. It is similar to MVE, except the involved vertices can be
    /// part of more than one loop.
    ///
    /// For examples, see `src/tests.rs`
    pub fn msev(
        &mut self,
        shell: ptr!(Shell),
        vertex: ptr!(Vertex),
        loops: [ptr!(Loop); 2],
        data: V,
    ) -> Result<Ksev<'brand, 'arena, V>, OperatorErr<Msev<'brand, 'arena, V>, MsevError>> {
        Msev::new(shell, vertex, loops, data).apply(self)
    }

    /// Kill-Split-Edge-Vertex
    ///
    /// This corresponds to KZEV in SNUMOD with the exception of not (necessarily) killing a zero-length edge and is the inverse of msev. It is similar to KVE, except the involved vertices can be
    /// part of more than one loop.
    ///
    /// For examples, see `src/tests.rs`
    pub fn ksev(
        &mut self,
        shell: ptr!(Shell),
        loops: [ptr!(Loop); 2],
        old_vertex: ptr!(Vertex),
        new_vertex: own!(Vertex),
        edge: own!(Edge),
    ) -> Result<Msev<'brand, 'arena, V>, OperatorErr<Ksev<'brand, 'arena, V>, KsevError>> {
        Ksev::new(shell, loops, old_vertex, new_vertex, edge).apply(self)
    }

    /// Make-Peripheral-Kill-Hole
    ///
    /// This corresponds to MPKH in SNUMOD and is the inverse of kpmh. An inner (hole) loop is
    /// converted to the outer loop of a new face. This may potentially result in two disconnected
    /// manifolds, in which case the shells are split and the newly created shell is returned.
    ///
    /// For examples, see `src/tests.rs`
    pub fn mpkh(
        &mut self,
        loop_: ptr!(Loop),
    ) -> Result<Kpmh<'brand, 'arena, V>, OperatorErr<Mpkh<'brand, 'arena, V>, MpkhError>> {
        Mpkh::new(loop_).apply(self)
    }

    /// Kill-Peripheral-Make-Hole
    ///
    /// This corresponds to KPMH in SNUMOD and is the inverse of kpmh. An outer (peripheral) loop is
    /// converted to the inner loop of an existing face, removing its original face.
    /// This may cause two previously disconnected shells to now be connected, in which case
    /// they will be merged into one. The shell
    /// to be removed (which, if applicable, is the shell of the removed face) must be passed
    /// in if and only if a merge needs to happen. The removed face must not have any inner loops
    /// and it is not possible to merge shells belonging to different bodies.
    ///
    /// For examples, see `src/tests.rs`
    pub fn kpmh(
        &mut self,
        new_shell: Option<own!(Shell)>,
        old_face: ptr!(Face),
        new_face: own!(Face),
    ) -> Result<Mpkh<'brand, 'arena, V>, OperatorErr<Kpmh<'brand, 'arena, V>, KpmhError>> {
        Kpmh::new(new_shell, old_face, new_face).apply(self)
    }
}
