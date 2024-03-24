#![allow(private_bounds)]

use core::ops::Deref;
pub use ghost_cell::{GhostBorrow, GhostCell, GhostToken};
use paste::paste;
use std::{
    collections::HashMap,
    convert::Infallible,
    fmt::{self, Debug, Display, Formatter},
    hash::{Hash, Hasher},
};
use thiserror::Error;
pub use typed_arena::Arena;

macro_rules! try_check {
    ($this:ident, $dcel:ident) => {
        match $this.check($dcel) {
            Ok(x) => x,
            Err(e) => return Err(OperatorErr::new($this, e)),
        }
    };
}

#[macro_use]
mod entity;
use entity::*;

mod entity_iterator;
pub use entity_iterator::*;

mod dot;
pub use dot::*;

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

pub trait ReflAsRef<T> {
    fn as_ref(&self) -> &T;
}

impl<T> ReflAsRef<T> for T {
    fn as_ref(&self) -> &T {
        self
    }
}

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

#[macro_export]
macro_rules! ptr_t {
	($T:ty) => {
		Ptr<'brand, 'arena, $T>
	}
}

#[macro_export]
macro_rules! ptr {
	($T:ident) => {
		Ptr<'brand, 'arena, $T<'brand, 'arena, V>>
	};
}

#[macro_export]
macro_rules! own_t {
	($T:ty) => {
		Own<'brand, 'arena, $T>
	}
}

#[macro_export]
macro_rules! own {
	($T:ident) => {
		Own<'brand, 'arena, $T<'brand, 'arena, V>>
	};
}

#[macro_export]
macro_rules! lens_t {
	($T:ty) => {
		Lens<'tok, 'brand, 'arena, $T>
	}
}

#[macro_export]
macro_rules! lens {
	($T:ident) => {
		Lens<'tok, 'brand, 'arena, $T<'brand, 'arena, V>>
	};
}

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

pub struct Ptr<'brand, 'arena, T>(pub &'arena GhostCell<'brand, T>);

impl<'brand, 'arena, T> Clone for ptr_t!(T) {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}
impl<'brand, 'arena, T> Copy for ptr_t!(T) {}

impl<'brand, 'arena, T> ptr_t!(T) {
    pub fn borrow<'tok, 'out>(self, token: &'tok impl ReflAsRef<GhostToken<'brand>>) -> &'out T
    where
        'arena: 'out,
        'tok: 'out,
    {
        self.0.borrow(token.as_ref())
    }

    pub fn borrow_mut<'tok, 'out>(
        self,
        token: &'tok mut impl ReflAsMut<GhostToken<'brand>>,
    ) -> &'out mut T
    where
        'arena: 'out,
        'tok: 'out,
    {
        self.0.borrow_mut(token.as_mut())
    }

    pub fn lens<'tok>(self, token: &'tok impl ReflAsRef<GhostToken<'brand>>) -> lens_t!(T) {
        Lens::new(self, token)
    }
}

#[allow(unused)]
impl<'brand, 'arena, T: Entity<'brand, 'arena>> ptr_t!(T) {
    fn clear(self, token: &mut impl ReflAsMut<GhostToken<'brand>>) {
        self.borrow_mut(token).clear()
    }

    pub fn id(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> usize {
        self.borrow(token).id()
    }
    fn maybe_id(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> Option<usize> {
        self.borrow(token).maybe_id()
    }
    fn alive(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> bool {
        self.borrow(token).alive()
    }

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

pub struct Own<'brand, 'arena, T>(ptr_t!(T));

impl<'brand, 'arena, T> Own<'brand, 'arena, T> {
    // avoid this
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

pub struct Lens<'tok, 'brand, 'arena, T> {
    pub item: ptr_t!(T),
    pub token: &'tok GhostToken<'brand>,
}

impl<'tok, 'brand, 'arena, T> Clone for lens_t!(T) {
    fn clone(&self) -> Self {
        Self::new(self.item, self.token)
    }
}
impl<'tok, 'brand, 'arena, T> Copy for lens_t!(T) {}

impl<'tok, 'brand, 'arena, T: PartialEq> PartialEq for lens_t!(T) {
    fn eq(&self, other: &Self) -> bool {
        self.item.borrow(self.token) == other.item.borrow(other.token)
    }
}
impl<'tok, 'brand, 'arena, T: PartialEq> Eq for lens_t!(T) {}

impl<'tok, 'brand, 'arena, T: Hash> Hash for lens_t!(T) {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.item.borrow(self.token).hash(state);
    }
}

impl<'tok, 'brand, 'arena, T> ReflAsRef<GhostToken<'brand>> for lens_t!(T) {
    fn as_ref(&self) -> &GhostToken<'brand> {
        &self.token
    }
}

impl<'tok, 'brand, 'arena, T> From<lens_t!(T)> for ptr_t!(T) {
    fn from(x: lens_t!(T)) -> Self {
        x.item
    }
}

impl<'tok, 'brand, 'arena, T> lens_t!(T) {
    pub fn new(item: ptr_t!(T), token: &'tok impl ReflAsRef<GhostToken<'brand>>) -> Self {
        Self {
            item,
            token: token.as_ref(),
        }
    }
}

#[allow(unused)]
impl<'tok, 'brand, 'arena, T: Entity<'brand, 'arena>> lens_t!(T) {
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

pub struct OutgoingIterator<'tok, 'brand, 'arena, V>(Option<(lens!(HalfEdge), lens!(HalfEdge))>);

impl<'tok, 'brand, 'arena, V> Clone for OutgoingIterator<'tok, 'brand, 'arena, V> {
    fn clone(&self) -> Self {
        Self(self.0)
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
    pub fn data<'tok, 'out>(self, token: &'tok impl ReflAsRef<GhostToken<'brand>>) -> &'out V
    where
        'arena: 'out,
        'tok: 'out,
    {
        self.borrow(token).data.as_ref().unwrap()
    }

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

    pub fn iter_outgoing<'tok>(
        self,
        token: &'tok impl ReflAsRef<GhostToken<'brand>>,
    ) -> OutgoingIterator<'tok, 'brand, 'arena, V> {
        // FIXME: maybe enforce at least one item by using .outgoing()
        // there should be no "standalone" vertices (?)
        OutgoingIterator::new(self.maybe_outgoing(token), token)
    }

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

// TODO: target
entity!(half_edge: HalfEdge;
    pub origin: Vertex,
    pub twin: HalfEdge,
    pub loop_: Loop,
    pub edge: Edge
);

impl<'brand, 'arena, V> ptr!(HalfEdge) {
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
    half_edges[half_edge: half_edge back]: HalfEdge,
    pub face: Face
);

impl<'brand, 'arena, V> ptr!(Loop) {
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
    pub fn half_edges(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> [ptr!(HalfEdge); 2] {
        self.borrow(token)
            .half_edges
            .each_ref()
            .map(|x| *x.as_deref().unwrap())
    }

    pub fn vertices(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> [ptr!(Vertex); 2] {
        self.half_edges(token).map(|x| x.origin(token))
    }

    /*
    fn set_half_edges(
        self,
        x: [own!(HalfEdge); 2],
        token: &mut impl ReflAsMut<GhostToken<'brand>>,
    ) {
        self.borrow_mut(token).half_edges = Some(x);
    }*/
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
    pub outer_loop: Loop,
    inner_loops[inner_loop: loop_ back]: Loop,
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
    faces[face: face back]: Face,
    edges[edge: edge]: Edge,
    vertices[vertex: vertex (V)]: Vertex,
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
    shells[shell: shell back]: Shell
);

impl<'brand, 'arena, V> own!(Body) {
    fn destroy(self, dcel: &mut Dcel<'brand, 'arena, V>) {
        self.iter_mut_shells(dcel, |x, dcel| {
            Own::unsafe_make_owned(x).destroy(dcel);
        });
        dcel.delete_body(self);
    }
}

struct Allocator<'brand, 'arena, T: Entity<'brand, 'arena>> {
    next_id: usize,
    arena: &'arena Arena<T>,
    freelist: Vec<own_t!(T)>,
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
        if let Some(ptr) = self.freelist.pop() {
            *ptr.borrow_mut(token) = x;
            ptr
        } else {
            Own::unsafe_make_owned(Ptr(GhostCell::from_mut(self.arena.alloc(x))))
        }
    }

    fn free(&mut self, token: &mut impl ReflAsMut<GhostToken<'brand>>, ptr: own_t!(T)) {
        debug_assert!(ptr.alive(token), "double free");
        ptr.clear(token);
        self.freelist.push(ptr);
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

pub trait Operator<'brand, 'arena, V>: Sized {
    type Inverse: Operator<'brand, 'arena, V>;
    type Error: std::error::Error;
    type Check;

    fn check(&self, dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error>;

    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>>;
}

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

    pub fn new_body(&mut self) -> own!(Body) {
        let body = Body::new(self);
        self.bodies = Some(Entity::list_add(*body, self.bodies, self));
        body
    }

    pub fn delete_body(&mut self, body: own!(Body)) {
        self.bodies = Entity::list_remove(*body, self);
        body.free(self);
    }

    pub fn iter_bodies<'tok>(
        &'tok self,
    ) -> EntityIterator<'tok, 'brand, 'arena, Body<'brand, 'arena, V>> {
        EntityIterator::new(self.bodies, self)
    }

    // fn new_edge(&mut self, shell: ptr!(Shell)) -> (own!(Edge), [ptr!(HalfEdge); 2]) {}

    fn follow(&mut self, prev: ptr!(HalfEdge), next: ptr!(HalfEdge)) {
        next.set_prev(prev, self);
        prev.set_next(next, self);
    }

    pub fn mevvlfs(
        &mut self,
        body: ptr!(Body),
        data: [V; 2],
    ) -> Result<Kevvlfs<'brand, 'arena, V>, OperatorErr<Mevvlfs<'brand, 'arena, V>, Infallible>>
    {
        Mevvlfs::new(body, data).apply(self)
    }

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

    pub fn mev(
        &mut self,
        loop_: ptr!(Loop),
        vertex: ptr!(Vertex),
        data: V,
    ) -> Result<Kev<'brand, 'arena, V>, OperatorErr<Mev<'brand, 'arena, V>, MevError>> {
        Mev::new(loop_, vertex, data).apply(self)
    }

    pub fn kev(
        &mut self,
        edge: own!(Edge),
        vertex: own!(Vertex),
    ) -> Result<Mev<'brand, 'arena, V>, OperatorErr<Kev<'brand, 'arena, V>, KevError>> {
        Kev::new(edge, vertex).apply(self)
    }

    pub fn melf(
        &mut self,
        vertices: [ptr!(Vertex); 2],
        loop_: ptr!(Loop),
    ) -> Result<Kelf<'brand, 'arena, V>, OperatorErr<Melf<'brand, 'arena, V>, MelfError>> {
        Melf::new(vertices, loop_).apply(self)
    }

    pub fn kelf(
        &mut self,
        edge: own!(Edge),
        loop_: own!(Loop),
        face: own!(Face),
    ) -> Result<Melf<'brand, 'arena, V>, OperatorErr<Kelf<'brand, 'arena, V>, KelfError>> {
        Kelf::new(edge, loop_, face).apply(self)
    }

    pub fn mve(
        &mut self,
        edge: ptr!(Edge),
        data: V,
    ) -> Result<Kve<'brand, 'arena, V>, OperatorErr<Mve<'brand, 'arena, V>, Infallible>> {
        Mve::new(edge, data).apply(self)
    }

    pub fn kve(
        &mut self,
        edge: own!(Edge),
        vertex: own!(Vertex),
    ) -> Result<Mve<'brand, 'arena, V>, OperatorErr<Kve<'brand, 'arena, V>, KveError>> {
        Kve::new(edge, vertex).apply(self)
    }

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

    pub fn kemh(
        &mut self,
        shell: ptr!(Shell),
        edge: own!(Edge),
        loop_: ptr!(Loop),
        hole_vertex: ptr!(Vertex),
    ) -> Result<Mekh<'brand, 'arena, V>, OperatorErr<Kemh<'brand, 'arena, V>, KemhError>> {
        Kemh::new(shell, edge, loop_, hole_vertex).apply(self)
    }

    pub fn msev(
        &mut self,
        shell: ptr!(Shell),
        vertex: ptr!(Vertex),
        loops: [ptr!(Loop); 2],
        data: V,
    ) -> Result<Ksev<'brand, 'arena, V>, OperatorErr<Msev<'brand, 'arena, V>, MsevError>> {
        Msev::new(shell, vertex, loops, data).apply(self)
    }

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

    pub fn mpkh(
        &mut self,
        loop_: ptr!(Loop),
    ) -> Result<Kpmh<'brand, 'arena, V>, OperatorErr<Mpkh<'brand, 'arena, V>, MpkhError>> {
        Mpkh::new(loop_).apply(self)
    }

    pub fn kpmh(
        &mut self,
        new_shell: Option<own!(Shell)>,
        old_face: ptr!(Face),
        new_face: own!(Face),
    ) -> Result<Mpkh<'brand, 'arena, V>, OperatorErr<Kpmh<'brand, 'arena, V>, KpmhError>> {
        Kpmh::new(new_shell, old_face, new_face).apply(self)
    }
}
