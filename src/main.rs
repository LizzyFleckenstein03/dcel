#![allow(unused)]
#![allow(private_bounds)]
// the ptr! macro will expand to complex types but makes things easier to read for humans
// unlike type definitions, a macro can capture the 'brand and 'arena lifetimes from the scope
#![allow(clippy::type_complexity)]

use core::ops::Deref;
pub use ghost_cell::{GhostBorrow, GhostCell, GhostToken};
use paste::paste;
use std::fmt::{self, Debug, Formatter};
pub use typed_arena::Arena;

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

struct DebugFn<F: Fn(&mut Formatter) -> fmt::Result>(F);
impl<F: Fn(&mut Formatter) -> fmt::Result> Debug for DebugFn<F> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.0(f)
    }
}

macro_rules! ptr_t {
	($T:ty) => {
		Ptr<'brand, 'arena, $T>
	}
}

macro_rules! ptr {
	($T:ident) => {
		Ptr<'brand, 'arena, $T<'brand, 'arena, V>>
	};
}

macro_rules! own_t {
	($T:ty) => {
		Own<'brand, 'arena, $T>
	}
}

macro_rules! own {
	($T:ident) => {
		Own<'brand, 'arena, $T<'brand, 'arena, V>>
	};
}

macro_rules! lens_t {
	($T:ty) => {
		Lens<'tok, 'brand, 'arena, $T>
	}
}

macro_rules! lens {
	($T:ident) => {
		Lens<'tok, 'brand, 'arena, $T<'brand, 'arena, V>>
	};
}

fn _short_debug(ty: &'static str, id: usize, f: &mut Formatter) -> fmt::Result {
    f.debug_tuple(ty).field(&id).finish()
}

fn short_debug<'tok, 'brand, 'arena, T: Entity<'brand, 'arena>>(
    x: lens_t!(T),
    f: &mut Formatter,
) -> fmt::Result {
    _short_debug(T::type_name(), x.id(), f)
}

fn short_debug_fn<'tok, 'brand, 'arena, T: Entity<'brand, 'arena>>(x: lens_t!(T)) -> impl Debug {
    let id = x.id();
    DebugFn(move |f| _short_debug(T::type_name(), id, f))
}

fn short_debug_list<'tok, 'brand, 'arena, T, I>(iter: I, f: &mut Formatter) -> fmt::Result
where
    'brand: 'tok + 'arena,
    T: Entity<'brand, 'arena> + 'arena,
    I: Iterator<Item = lens_t!(T)>,
{
    f.debug_list().entries(iter.map(short_debug_fn)).finish()
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

impl<'tok, 'brand, 'arena, T> ReflAsRef<GhostToken<'brand>> for lens_t!(T) {
    fn as_ref(&self) -> &GhostToken<'brand> {
        &self.token
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

pub struct EntityIterator<'tok, 'brand, 'arena, T>(Option<(lens_t!(T), lens_t!(T))>);

impl<'tok, 'brand, 'arena, T> Clone for EntityIterator<'tok, 'brand, 'arena, T> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<'tok, 'brand, 'arena, T> Copy for EntityIterator<'tok, 'brand, 'arena, T> {}

impl<'tok, 'brand, 'arena, T: Entity<'brand, 'arena>> EntityIterator<'tok, 'brand, 'arena, T> {
    fn new(token: &'tok impl ReflAsRef<GhostToken<'brand>>, start: Option<ptr_t!(T)>) -> Self {
        Self(start.map(|s| {
            let l = Lens::new(s, token);
            (l, l.prev())
        }))
    }
}

impl<'tok, 'brand, 'arena, T: Entity<'brand, 'arena>> Iterator
    for EntityIterator<'tok, 'brand, 'arena, T>
{
    type Item = lens_t!(T);

    fn next(&mut self) -> Option<Self::Item> {
        let mut range = self.0.as_mut()?;
        let ret = range.0;

        if range.0 == range.1 {
            self.0 = None;
        } else {
            range.0 = range.0.next();
        }

        Some(ret)
    }
}

impl<'tok, 'brand, 'arena, T: Entity<'brand, 'arena>> DoubleEndedIterator
    for EntityIterator<'tok, 'brand, 'arena, T>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        let mut range = self.0.as_mut()?;
        let ret = range.1;

        if range.0 == range.1 {
            self.0 = None;
        } else {
            range.1 = range.1.prev();
        }

        Some(ret)
    }
}

// trait for a kind of topological element (i.e. Vertex, HalfEdge, Face)
trait Entity<'brand, 'arena>: Eq + Sized {
    type Init;

    fn new(id: usize, init: Self::Init) -> Self;
    fn clear(&mut self);

    fn type_name() -> &'static str;

    fn maybe_id(&self) -> Option<usize>;
    fn id(&self) -> usize {
        self.maybe_id().unwrap()
    }
    fn alive(&self) -> bool {
        self.maybe_id().is_some()
    }

    fn maybe_next(&self) -> Option<ptr_t!(Self)>;
    fn next(&self) -> ptr_t!(Self) {
        self.maybe_next().unwrap()
    }
    fn set_next(&mut self, x: ptr_t!(Self)) {
        self.set_next_opt(Some(x));
    }
    fn set_next_opt(&mut self, x: Option<ptr_t!(Self)>);

    fn maybe_prev(&self) -> Option<ptr_t!(Self)>;
    fn prev(&self) -> ptr_t!(Self) {
        self.maybe_prev().unwrap()
    }
    fn set_prev(&mut self, x: ptr_t!(Self)) {
        self.set_prev_opt(Some(x));
    }
    fn set_prev_opt(&mut self, x: Option<ptr_t!(Self)>);

    fn list_add(
        this: ptr_t!(Self),
        list: Option<ptr_t!(Self)>,
        token: &mut impl ReflAsMut<GhostToken<'brand>>,
    ) -> ptr_t!(Self) {
        let (next, prev) = if let Some(first) = list {
            (first, first.prev(token))
        } else {
            (this, this)
        };

        this.set_next(next, token);
        this.set_prev(prev, token);
        prev.set_next(this, token);
        next.set_prev(this, token);

        next
    }

    fn list_remove(
        this: ptr_t!(Self),
        token: &mut impl ReflAsMut<GhostToken<'brand>>,
    ) -> Option<ptr_t!(Self)> {
        let next = this.next(token);
        let prev = this.prev(token);

        if this.eq(next, token) {
            return None;
        }

        prev.set_next(next, token);
        next.set_prev(prev, token);

        Some(next)
    }
}

macro_rules! mklens {
	($token: expr, $($name:ident),*) => {
		$( let $name = $name.lens($token); )*
	};
}

macro_rules! entity {
	($name:ident : $T:ident,
		$arg_name:ident: $arg_ty:ty
		$(, $($init_field:ident : $init_ty:ty = $init_expr:expr),* )?
		$(;
			$( $field_vis:vis $field:ident
				$([ $list_singular:ident : $list_name:ident  $($list_back:ident)? ])?
			 : $field_ty:ident ),*
		)?
	) => {
		paste! {
			pub struct $T<'brand, 'arena, V> {
				id: Option<usize>,
				next: Option<ptr!($T)>,
				prev: Option<ptr!($T)>,
				$($($init_field: $init_ty,)*)?
				$($($field: Option<ptr!($field_ty)>,)*)?
			}

			impl<'brand, 'arena, V> Entity<'brand, 'arena> for $T<'brand, 'arena, V> {
				type Init = $arg_ty;

				fn new(id: usize, $arg_name: $arg_ty) -> Self {
					Self {
						id: Some(id),
						prev: None,
						next: None,
						$($($init_field: $init_expr,)*)?
						$($($field: None,)*)?
					}
				}

				fn clear(&mut self) {
					self.id = None;
					#[cfg(debug_assertions)]
					{
						self.prev = None;
						self.next = None;
						$($(self.$field = None;)*)?
					}
				}

				fn type_name() -> &'static str {
					stringify!($T)
				}

				fn maybe_id(&self) -> Option<usize> {
					self.id
				}

				fn maybe_next(&self) -> Option<ptr_t!(Self)> {
					self.next
				}

				fn set_next_opt(&mut self, x: Option<ptr_t!(Self)>) {
					self.next = x;
				}

				fn maybe_prev(&self) -> Option<ptr_t!(Self)> {
					self.prev
				}

				fn set_prev_opt(&mut self, x: Option<ptr_t!(Self)>) {
					self.prev = x;
				}
			}

			impl<'brand, 'arena, V> ptr!($T) {
				$($(
					$field_vis fn $field(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> ptr!($field_ty) {
						self.[<maybe_ $field>](token).unwrap()
					}


					fn [<maybe_ $field>](self, token: &impl ReflAsRef<GhostToken<'brand>>) -> Option<ptr!($field_ty)> {
						self.borrow(token).$field
					}


					fn [<set_ $field>](self, token: &mut impl ReflAsMut<GhostToken<'brand>>, x: ptr!($field_ty)) {
						self.[<set_opt_ $field>](token, Some(x));
					}

					fn [<set_opt_ $field>](self, token: &mut impl ReflAsMut<GhostToken<'brand>>, x: Option<ptr!($field_ty)>) {
						self.borrow_mut(token).$field = x;
					}

					$(
						pub fn [<iter_ $field>]<'tok>(
							self,
							token: &'tok impl ReflAsRef<GhostToken<'brand>>,
						) -> EntityIterator<'tok, 'brand, 'arena, $field_ty<'brand, 'arena, V>>
						{
							EntityIterator::new(token, self.[<maybe_ $field>](token))
						}

						fn [<add_ $list_singular>](
							self,
							token: &mut impl ReflAsMut<GhostToken<'brand>>,
							x: ptr!($field_ty),
						) {
							let list = Entity::list_add(x, self.[<maybe_ $field>](token), token);
							self.[<set_ $field>](token, list);

							$(
								let [<_ $list_back>] = ();
								x.[<set_ $name>](token, self);
							)?
						}

						fn [<add_new_ $list_singular>](
							self,
							dcel: &mut Dcel<'brand, 'arena, V>,
							init: <$field_ty<'brand, 'arena, V> as Entity<'brand, 'arena>>::Init,
						) -> own!($field_ty) {
							let x = dcel.$list_name.alloc(&mut dcel.token, init);
							self.[<add_ $list_singular>](dcel, *x);
							x
						}
					)?
				)*)?
			}

			impl<'tok, 'brand, 'arena, V: Debug> Debug for lens!($T) {
				fn fmt(&self, f: &mut Formatter) -> fmt::Result {
					f.debug_struct(stringify!($T))
						.field("id", &self.id())
						.field("prev", &short_debug_fn(self.prev()))
						.field("next", &short_debug_fn(self.next()))
						$($(
							.field(stringify!($field), &DebugFn(|f| self.[<debug_ $field>](f)))
						)*)?
						$($(
							.field(stringify!($init_field), &DebugFn(|f| self.[<debug_ $init_field>](f)))
						)*)?
						.finish()
				}
			}

			impl<'tok, 'brand, 'arena, V> lens!($T) {
				$($(
					$field_vis fn $field(self) -> lens!($field_ty) {
						self.item.$field(&self).lens(self.token)
					}

					fn [<maybe_ $field>](self) -> Option<lens!($field_ty)> {
						self.item.[<maybe_ $field>](&self).map(|x| x.lens(self.token))
					}

					$(
						pub fn [<iter_ $field>](self) -> EntityIterator<'tok, 'brand, 'arena, $field_ty<'brand, 'arena, V>> {
							let [<_ $list_singular>] = ();
							self.item.[<iter_ $field>](self.token)
						}
					)?

					fn [<debug_ $field>](self, f: &mut Formatter) -> fmt::Result {
						$({
							let [<_ $list_singular>] = ();
							if true {
								return short_debug_list(self.[<iter_ $field>](), f);
							}
						})?
						short_debug(self.$field(), f)
					}
				)*)?
			}
		}

		impl<'brand, 'arena, V> Own<'brand, 'arena, $T<'brand, 'arena, V>> {
			fn free(self, dcel: &mut Dcel<'brand, 'arena, V>) {
				dcel.$name.free(&mut dcel.token, self)
			}
		}

		impl<'brand, 'arena, V> PartialEq for $T<'brand, 'arena, V> {
			fn eq(&self, other: &Self) -> bool {
				self.id() == other.id()
			}
		}
		impl<'brand, 'arena, V> Eq for $T<'brand, 'arena, V> {}
	};
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

    fn alloc(
        &mut self,
        token: &mut impl ReflAsMut<GhostToken<'brand>>,
        init: T::Init,
    ) -> own_t!(T) {
        let id = self.next_id;
        self.next_id += 1;

        let t = Entity::new(id, init);

        if let Some(ptr) = self.freelist.pop() {
            *ptr.borrow_mut(token) = t;
            ptr
        } else {
            Own::unsafe_make_owned(Ptr(GhostCell::from_mut(self.arena.alloc(t))))
        }
    }

    fn free(&mut self, token: &mut impl ReflAsMut<GhostToken<'brand>>, ptr: own_t!(T)) {
        debug_assert!(ptr.alive(token), "double free");
        ptr.clear(token);
        self.freelist.push(ptr);
    }
}

entity!(vertex: Vertex,
    init: V,
    data: V = init;
    outgoing: HalfEdge
);

impl<'brand, 'arena, V: Debug> ptr!(Vertex) {
    pub fn data<'tok, 'out>(self, token: &'tok impl ReflAsRef<GhostToken<'brand>>) -> &'out V
    where
        'arena: 'out,
        'tok: 'out,
    {
        &self.borrow(token).data
    }

    pub fn mut_data<'tok, 'out>(
        self,
        token: &'tok mut impl ReflAsMut<GhostToken<'brand>>,
    ) -> &'out mut V
    where
        'arena: 'out,
        'tok: 'out,
    {
        &mut self.borrow_mut(token).data
    }
}

impl<'tok, 'brand, 'arena, V: Debug> lens!(Vertex) {
    pub fn data(&self) -> &V {
        self.item.data(self)
    }

    fn debug_data(self, f: &mut Formatter) -> fmt::Result {
        self.data().fmt(f)
    }
}

// TODO: target
entity!(half_edge: HalfEdge,
    init: ();
    pub origin: Vertex,
    pub twin: HalfEdge,
    pub loop_: Loop,
    pub edge: Edge
);

impl<'brand, 'arena, V> ptr!(HalfEdge) {
    pub fn target(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> ptr!(Vertex) {
        self.twin(token).origin(token)
    }
}

impl<'tok, 'brand, 'arena, V> lens!(HalfEdge) {
    pub fn target(self) -> lens!(Vertex) {
        self.item.target(&self).lens(self.token)
    }
}

entity!(loop_: Loop,
    init: ();
    half_edges[half_edge: half_edge back]: HalfEdge,
    pub face: Face
);

entity!(edge: Edge,
    init: (),
    half_edges: Option<[own!(HalfEdge); 2]> = None
);

impl<'brand, 'arena, V> ptr!(Edge) {
    pub fn half_edges(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> [ptr!(HalfEdge); 2] {
        let he = self.borrow(token).half_edges.as_ref().unwrap();
        [*he[0], *he[1]]
    }

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

    fn debug_half_edges(self, f: &mut Formatter) -> fmt::Result {
        short_debug_list(self.half_edges().into_iter(), f)
    }
}

entity!(face: Face,
    init: ();
    outer_loops[outer_loop: loop_ back]: Loop,
    inner_loops[inner_loop: loop_ back]: Loop,
    pub shell: Shell
);

entity!(shell: Shell,
    init: ();
    faces[face: face back]: Face,
    edges[edge: edge]: Edge,
    vertices[vertex: vertex]: Vertex,
    pub body: Body
);

entity!(body: Body,
    init: ();
    shells[shell: shell back]: Shell
);

pub struct Mevvlfs<'brand, 'arena, V> {
    pub edge: own!(Edge),
    pub vertices: [own!(Vertex); 2],
    pub loop_: own!(Loop),
    pub face: own!(Face),
    pub shell: own!(Shell),
}

pub enum EulerOp<'brand, 'arena, V> {
    Mevvlfs(Mevvlfs<'brand, 'arena, V>),
}

impl<'brand, 'arena, V> From<Mevvlfs<'brand, 'arena, V>> for EulerOp<'brand, 'arena, V> {
    fn from(op: Mevvlfs<'brand, 'arena, V>) -> Self {
        Self::Mevvlfs(op)
    }
}

#[derive(Default)]
pub struct DcelArena<'brand, 'arena, V> {
    pub vertex: Arena<Vertex<'brand, 'arena, V>>,
    pub half_edge: Arena<HalfEdge<'brand, 'arena, V>>,
    pub loop_: Arena<Loop<'brand, 'arena, V>>,
    pub edge: Arena<Edge<'brand, 'arena, V>>,
    pub face: Arena<Face<'brand, 'arena, V>>,
    pub shell: Arena<Shell<'brand, 'arena, V>>,
    pub body: Arena<Body<'brand, 'arena, V>>,
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

/*
impl<'brand, 'arena, V> std::convert::AsMut<GhostToken<'brand>> for Dcel<'brand, 'arena, V> {
    fn as_mut(&mut self) -> &mut GhostToken<'brand> {
        &mut self.token
    }
}

impl<'brand, 'arena, V> core::borrow::Borrow<GhostToken<'brand>> for Dcel<'brand, 'arena, V> {
    fn borrow(&self) -> &GhostToken<'brand> {
        &self.token
    }
}*/

impl<'brand, 'arena, V: Debug> Dcel<'brand, 'arena, V> {
    fn new(token: GhostToken<'brand>, ar: &'arena DcelArena<'brand, 'arena, V>) -> Self {
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

    pub fn new_body(&mut self) -> own!(Body) {
        let body = self.body.alloc(&mut self.token, ());
        self.bodies = Some(Entity::list_add(*body, self.bodies, self));
        body
    }

    fn new_edge(&mut self, shell: ptr!(Shell)) -> (own!(Edge), [ptr!(HalfEdge); 2]) {
        let edge = shell.add_new_edge(self, ());

        let he1_own = self.half_edge.alloc(&mut self.token, ());
        let he2_own = self.half_edge.alloc(&mut self.token, ());

        let he1 = *he1_own;
        let he2 = *he2_own;

        edge.borrow_mut(&mut self.token).half_edges = Some([he1_own, he2_own]);

        he1.set_twin(self, he2);
        he2.set_twin(self, he1);
        he1.set_edge(self, *edge);
        he2.set_edge(self, *edge);

        (edge, [he1, he2])
    }

    #[inline(always)]
    fn origin(&mut self, v: ptr!(Vertex), h: ptr!(HalfEdge)) {
        v.borrow_mut(&mut self.token).outgoing = Some(h);
        h.borrow_mut(&mut self.token).origin = Some(v);
    }

    #[inline(always)]
    fn follow(&mut self, prev: ptr!(HalfEdge), next: ptr!(HalfEdge)) {
        next.borrow_mut(&mut self.token).prev = Some(prev);
        prev.borrow_mut(&mut self.token).next = Some(next);
    }

    pub fn undo(&mut self, op: impl Into<EulerOp<'brand, 'arena, V>>) {
        match op.into() {
            EulerOp::Mevvlfs(x) => self.kevvlfs(x),
        }
    }
    /*
    pub fn equals<'a, 'b, 'slf: 'a + 'b, T: Entity<'brand, 'arena> + 'arena>(
        &'slf self,
        a: impl GhostBorrow<'a, 'brand, Result = &'arena T>,
        b: impl GhostBorrow<'b, 'brand, Result = &'arena T>,
    ) -> bool {
        a.borrow(&self.token) == b.borrow(&self.token)
    }
    */

    pub fn iter_outgoing<T>(
        &mut self,
        vertex: ptr!(Vertex),
        mut f: impl FnMut(&mut GhostToken<'brand>, ptr!(HalfEdge)) -> Option<T>,
    ) -> Option<T> {
        let mut he = vertex.outgoing(&self.token);
        let orig = he;

        while {
            if let Some(x) = f(&mut self.token, he) {
                return Some(x);
            }

            he = he.twin(self).next(self);
            // debug_assert!(he.origin())

            !orig.eq(he, self)
        } {}

        None
    }

    pub fn mevvlfs(&mut self, body: ptr!(Body), data: [V; 2]) -> Mevvlfs<'brand, 'arena, V> {
        let [d1, d2] = data;

        let shell = body.add_new_shell(self, ());
        let face = shell.add_new_face(self, ());
        let (edge, [a, b]) = self.new_edge(*shell);
        let loop_ = face.add_new_outer_loop(self, ());
        let v1 = shell.add_new_vertex(self, d1);
        let v2 = shell.add_new_vertex(self, d2);

        self.origin(*v1, a);
        self.origin(*v2, b);

        loop_.add_half_edge(self, a);
        loop_.add_half_edge(self, b);

        Mevvlfs {
            edge,
            vertices: [v1, v2],
            loop_,
            face,
            shell,
        }
    }

    pub fn kevvlfs(&mut self, op: Mevvlfs<'brand, 'arena, V>) {
        let Mevvlfs {
            edge,
            vertices: [v1, v2],
            loop_,
            face,
            shell,
        } = op;

        let [a, b] = edge.borrow_mut(&mut self.token).half_edges.take().unwrap();

        {
            mklens!(self, a, b, loop_, face, shell, v1, v2);

            assert!([a.origin(), b.origin()] == [v1, v2] || [a.origin(), b.origin()] == [v2, v1]);

            assert_eq!(a.next(), b);
            assert_eq!(b.next(), a);
            assert_eq!(a.loop_(), loop_);

            assert_eq!(face.outer_loops(), loop_);
            assert!(face.maybe_inner_loops().is_none());

            assert_eq!(face.next(), face);
            assert_eq!(shell.faces(), face);
        }

        let shells = Entity::list_remove(*shell, self);
        shell.body(self).set_opt_shells(self, shells);

        edge.free(self);
        a.free(self);
        b.free(self);
        loop_.free(self);
        face.free(self);
        shell.free(self);
        v1.free(self);
        v2.free(self);
    }

    /*
    pub fn mve(
        &mut self,
        shell: ptr!(Shell),
        edge: ptr!(Edge),
        data: V,
    ) -> Option<(ptr!(Vertex), ptr!(Edge))> {
        // before:
        //
        //                        >
        //                       / a3
        //          a1 ->
        // v1                   v2
        //          <- b1
        //                       \ b3
        //                        <
        //
        // after:
        //
        //                        >
        //                       / a3
        //     a1 ->     a2 ->
        // v1         v         v2
        //     <- b1     <- b2
        //                       \ b3
        //                        <

        let v = self.vertices.alloc(&mut self.token, data);
        let a2 = self.half_edges.alloc(&mut self.token, ());
        let b2 = self.half_edges.alloc(&mut self.token, ());

        let a1 = edge;
        let v1 = a1.borrow(&self.token).origin?;
        //let fa = a1.borrow(&self.token).face?;

        let b1 = a1.borrow(&self.token).twin?;
        let v2 = b1.borrow(&self.token).origin?;
        //let fb = b1.borrow(&self.token).face?;

        let mut a3 = a1.borrow(&self.token).next?;
        if a3.borrow(&self.token) == b1.borrow(&self.token) {
            a3 = b1; // a1
        }

        let mut b3 = b1.borrow(&self.token).prev?;
        if b3.borrow(&self.token) == a1.borrow(&self.token) {
            b3 = a2; // b1
        }

        self.twin(a2, b2);

        self.origin(v, a2);
        self.origin(v, b1);
        self.origin(v2, b2);

        self.follow(a1, a2);
        self.follow(a2, a3);

        self.follow(b3, b2);
        self.follow(b2, b1);

        Some((a2, v))
    }*/

    /*

    pub fn mevvls(&mut self, data: [V; 2]) -> (ptr!(HalfEdge), [ptr!(Vertex); 2], ptr!(Face)) {
        let [d1, d2] = data;

        let l = self.faces.alloc(&mut self.token, ());
        let v1 = self.vertices.alloc(&mut self.token, d1);
        let v2 = self.vertices.alloc(&mut self.token, d2);
        let a = self.half_edges.alloc(&mut self.token, ());
        let b = self.half_edges.alloc(&mut self.token, ());

        self.twin(a, b);
        self.follow(a, b);
        self.follow(b, a);
        self.origin(v1, a);
        self.origin(v2, b);

        (a, [v1, v2], l)
    }

    #[inline(always)]
    fn twin(&mut self, a: ptr!(HalfEdge), b: ptr!(HalfEdge)) {
        a.borrow_mut(&mut self.token).twin = Some(b);
        b.borrow_mut(&mut self.token).twin = Some(a);
    }

    pub fn mve(
        &mut self,
        edge: ptr!(HalfEdge),
        data: V,
    ) -> Option<(ptr!(HalfEdge), ptr!(Vertex))> {
        // before:
        //
        //                        >
        //                       / a3
        //          a1 ->
        // v1         v         v2
        //          <- b1
        //                       \ b3
        //                        <
        //
        // after:
        //
        //                        >
        //                       / a3
        //     a1 ->     a2 ->
        // v1         v         v2
        //     <- b1     <- b2
        //                       \ b3
        //                        <

        let v = self.vertices.alloc(&mut self.token, data);
        let a2 = self.half_edges.alloc(&mut self.token, ());
        let b2 = self.half_edges.alloc(&mut self.token, ());

        let a1 = edge;
        let v1 = a1.borrow(&self.token).origin?;
        //let fa = a1.borrow(&self.token).face?;

        let b1 = a1.borrow(&self.token).twin?;
        let v2 = b1.borrow(&self.token).origin?;
        //let fb = b1.borrow(&self.token).face?;

        let mut a3 = a1.borrow(&self.token).next?;
        if a3.borrow(&self.token) == b1.borrow(&self.token) {
            a3 = b1; // a1
        }

        let mut b3 = b1.borrow(&self.token).prev?;
        if b3.borrow(&self.token) == a1.borrow(&self.token) {
            b3 = a2; // b1
        }

        self.twin(a2, b2);

        self.origin(v, a2);
        self.origin(v, b1);
        self.origin(v2, b2);

        self.follow(a1, a2);
        self.follow(a2, a3);

        self.follow(b3, b2);
        self.follow(b2, b1);

        Some((a2, v))
    }

    // pub fn mel(&mut self, b0: ptr!(HalfEdge), a2: ptr!(HalfEdge)) -> Option<()> {
    pub fn mel(&mut self, v1: ptr!(Vertex), v2: ptr!(Vertex)) -> Option<()> {
        // before:
        //     >               >
        //   a0 \             / a2
        //       v1         v2
        //   b0 /             \ b2
        //     <               <
        //
        // after:
        //     >               >
        //   a0 \    a1 ->    / a2
        //       v1         v2
        //   b0 /    <- b1    \ b2
        //     <               <
        //

        let a1 = self.half_edges.alloc(&mut self.token, ());
        let b1 = self.half_edges.alloc(&mut self.token, ());

        let b0 = v1.borrow(&self.token).outgoing?;
        let a2 = v2.borrow(&self.token).outgoing?;

        //let v1 = b0.borrow(&self.token).origin?;
        //let v2 = a2.borrow(&self.token).origin?;

        let a0 = b0.borrow(&self.token).twin?;
        let b2 = a2.borrow(&self.token).twin?;

        self.twin(a1, b1);

        self.origin(v1, a1);
        self.origin(v2, b1);

        self.follow(a0, a1);
        self.follow(a1, a2);

        self.follow(b2, b1);
        self.follow(b1, b0);

        Some(())
    }

    fn mev(
        &mut self,
        from: ptr!(Vertex),
        data: V,
    ) -> (ptr!(Vertex), ptr!(HalfEdge), ptr!(HalfEdge)) {
        let v = self.vertices.alloc(&mut self.token, data);
        let a = self.half_edges.alloc(&mut self.token, ());
        let b = self.half_edges.alloc(&mut self.token, ());

        self.twin(a, b);

        self.origin(v, a);
        self.origin(from, b);

        self.follow(a, b);
        self.follow(b, a);

        (v, a, b)
    }

    //fn mekh(&mut self, )*/
}

/*
struct DcelDotOptions {
    pub twin: bool,
    pub next: bool,
    pub prev: bool,
}

impl DcelDotOptions {
    fn none() -> Self {
        Self {
            twin: false,
            next: false,
            prev: false,
        }
    }

    fn all() -> Self {
        Self {
            twin: true,
            next: true,
            prev: true,
        }
    }
}

fn dcel_write_dot(
    dcel: &Dcel<(&'static str, [i64; 2])>,
    f: &mut fmt::Formatter<'_>,
    opt: DcelDotOptions,
) -> fmt::Result {
    use rand::Rng;
    use std::collections::HashSet;

    writeln!(f, "digraph DCEL {{")?;
    writeln!(f, "node [shape = circle]")?;
    //writeln!(f, "nodesep = 1")?;

    let mut rank = Vec::new();

    for v in dcel.vertices.elements.iter() {
        let v = v.borrow(&dcel.token);
        if let Some(id) = v.id {
            writeln!(
                f,
                "vertex_{id} [label=\"{}\", pos=\"{},{}!\"]",
                v.data.0, v.data.1[0], v.data.1[1]
            );
            rank.push(id);
        }
    }

    for h in dcel.half_edges.elements.iter() {
        let h = h.borrow(&dcel.token);
        if let Some(id) = h.id {
            let twin = h.twin.unwrap().borrow(&dcel.token);
            let twin_id = twin.id.unwrap();

            let connect = |f: &mut fmt::Formatter<'_>,
                           id: &str,
                           label: &str,
                           attr: &str,
                           pts: [(&str, [f64; 2]); 2]|
             -> Result<(), fmt::Error> {
                let mut vec = [pts[1].1[1] - pts[0].1[1], pts[1].1[0] - pts[0].1[0]];

                let len = (vec[0] * vec[0] + vec[1] * vec[1]).sqrt();
                vec[0] *= -0.075;
                vec[1] *= 0.075;

                let mid = [
                    (pts[1].1[0] + pts[0].1[0]) / 2.0 + vec[0],
                    (pts[1].1[1] + pts[0].1[1]) / 2.0 + vec[1],
                ];

                writeln!(
                    f,
                    "{id} [pos=\"{},{}!\", shape=point, width=0.01, height=0.01]",
                    mid[0], mid[1]
                )?;
                writeln!(f, "{} -> {id} [{attr}arrowhead=none]", pts[0].0)?;
                writeln!(f, "{id} -> {} [{attr}label=\"{label}\"]", pts[1].0)?;

                Ok(())
            };

            let a = h.origin.unwrap().borrow(&dcel.token);
            let b = twin.origin.unwrap().borrow(&dcel.token);

            connect(
                f,
                &format!("half_edge_{id}"),
                &format!("{id}"),
                "",
                [
                    (
                        &format!("vertex_{}", a.id.unwrap()),
                        [a.data.1[0] as _, a.data.1[1] as _],
                    ),
                    (
                        &format!("vertex_{}", b.id.unwrap()),
                        [b.data.1[0] as _, b.data.1[1] as _],
                    ),
                ],
            )?;

            if opt.twin {
                writeln!(f, "half_edge_{id} -> half_edge_{twin_id} [color=\"red\"]")?;
            }

            if opt.next {
                writeln!(
                    f,
                    "half_edge_{id} -> half_edge_{} [color=\"green\"]",
                    h.next.unwrap().borrow(&dcel.token).id.unwrap()
                )?;
            }

            if opt.prev {
                writeln!(
                    f,
                    "half_edge_{id} -> half_edge_{} [color=\"blue\"]",
                    h.prev.unwrap().borrow(&dcel.token).id.unwrap()
                )?;
            }
        }
    }

    writeln!(f, "}}")
}

impl_debug!(i32);

struct DisplayFn<T>(T);
impl<T: Fn(&mut fmt::Formatter<'_>) -> fmt::Result> fmt::Display for DisplayFn<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0(f)
    }
}

use std::io::Write;*/

fn main() {
    GhostToken::new(|token| {
        let arena = DcelArena::default();
        let mut dcel = Dcel::new(token, &arena);

        let body = dcel.new_body();
        // Mevvlfs(a, [w, n], l, f, s)
        let op = dcel.mevvlfs(*body, [("W", [-4, 0]), ("N", [0, 4])]);
        println!("{}", op.vertices[0].eq(*op.vertices[0], &dcel));
        println!("{}", op.vertices[0].eq(*op.vertices[1], &dcel));

        println!("{:?}", op.edge.lens(&dcel));
        println!("{:?}", op.vertices[0].lens(&dcel));
        println!("{:?}", op.vertices[1].lens(&dcel));
        println!("{:?}", op.loop_.lens(&dcel));
        dbg!(op.loop_.iter_half_edges(&dcel).rev().collect::<Vec<_>>());
        println!("{:?}", op.face.lens(&dcel));
        println!("{:?}", op.shell.lens(&dcel));

        dcel.undo(op);

        /*
        let show = |name, dcel: &Dcel<(&'static str, [i64; 2])>| {
            write!(
                &mut std::fs::File::create(name).unwrap(),
                "{}",
                DisplayFn(|f: &mut fmt::Formatter<'_>| dcel_write_dot(
                    dcel,
                    f,
                    DcelDotOptions {
                        prev: false,
                        next: true,
                        twin: false,
                    }
                ))
            )
            .unwrap();
        };

        let (a, [w, n], _) = dcel.mevvls([("W", [-4, 0]), ("N", [0, 4])]);
        show("1.dot", &dcel);

        let b = dcel.mve(a, ("E", [4, 0])).unwrap().0;
        show("2.dot", &dcel);

        dcel.mve(a, ("S", [0, -4])).unwrap();
        show("3.dot", &dcel);

        //dcel.mel(w, n);
        show("4.dot", &dcel);*/

        /*
        eprintln!(
            "{} {}",
                     a.borrow(&dcel.token).id.unwrap(),
                     b.borrow(&dcel.token).id.unwrap()
        );*/

        /*
        print!(
            "{}",
            "{}",
                            layFn(|f: &mut fmt::Formatter<'_>| {
                                   v in dcel.vertices.elements.iter() {
                }


                    h in dcel.half_edges.elements.iter() {
                }

                Ok(())
            })
                  })
           );*/
    });
}

/*
trait DcelDebug<'brand> {
    fn fmt(
        &self,
        long: bool,
        token: &GhostToken<'brand>,
        f: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error>;
}

macro_rules! impl_debug {
    ($T:ty) => {
        impl<'brand> DcelDebug<'brand> for $T {
            fn fmt(
                &self,
                long: bool,
                token: &GhostToken<'brand>,
                f: &mut fmt::Formatter<'_>,
            ) -> Result<(), fmt::Error> {
                fmt::Debug::fmt(self, f)?;
                writeln!(f, "")
            }
        }
    };
}

impl<'brand, T: DcelDebug<'brand>> DcelDebug<'brand> for Option<T> {
    fn fmt(
        &self,
        long: bool,
        token: &GhostToken<'brand>,
        f: &mut fmt::Formatter<'_>,
    ) -> Result<(), fmt::Error> {
        match self {
            None => write!(f, "None"),
            Some(x) => DcelDebug::fmt(x, long, token, f),
        }
    }
}

macro_rules! impl_entity_debug {
    ($T:ident $(, $($fields:ident),*)?) => {
        impl<'brand, 'arena, V> DcelDebug<'brand> for &'arena GhostCell<'brand, $T<'brand, 'arena, V>> where V: DcelDebug<'brand> {
            fn fmt(
                &self,
                long: bool,
                token: &GhostToken<'brand>,
                f: &mut fmt::Formatter<'_>,
            ) -> Result<(), fmt::Error> {
                writeln!(f, "{} {:?}", stringify!($T), self.borrow(token).id)?;

                if long {
                    $($(
                        write!(f, "\t{} = ", stringify!($fields))?;
                        DcelDebug::fmt(&self.borrow(token).$fields, false, token, f)?;
                    )*)?
                }

                Ok(())
            }
        }
    };
}*/
