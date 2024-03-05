#![allow(private_bounds)]

use core::ops::Deref;
pub use ghost_cell::{GhostBorrow, GhostCell, GhostToken};
use paste::paste;
use std::{
    fmt::{self, Debug, Display, Formatter},
    hash::{Hash, Hasher},
};
use thiserror::Error;
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
    DisplayFn(move |f| _short_debug(T::type_name(), id, f))
}

fn short_debug_list<'tok, 'brand, 'arena, T, I>(iter: I, f: &mut Formatter) -> fmt::Result
where
    'brand: 'tok + 'arena,
    T: Entity<'brand, 'arena> + 'arena,
    I: Iterator<Item = lens_t!(T)>,
{
    f.debug_list().entries(iter.map(short_debug_fn)).finish()
}

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

pub struct EntityIterator<'tok, 'brand, 'arena, T>(Option<(lens_t!(T), lens_t!(T))>);

impl<'tok, 'brand, 'arena, T> Clone for EntityIterator<'tok, 'brand, 'arena, T> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<'tok, 'brand, 'arena, T> Copy for EntityIterator<'tok, 'brand, 'arena, T> {}

impl<'tok, 'brand, 'arena, T: Entity<'brand, 'arena>> EntityIterator<'tok, 'brand, 'arena, T> {
    fn new(start: Option<ptr_t!(T)>, token: &'tok impl ReflAsRef<GhostToken<'brand>>) -> Self {
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
        let range = self.0.as_mut()?;
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
        let range = self.0.as_mut()?;
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

macro_rules! entity {
	($name:ident : $T:ident $(($init_name:ident : $init_ty:ty))?
		$(, $($custom_field:ident : $custom_ty:ty = $custom_expr:expr),* )?
		$(;
			$( $field_vis:vis $field:ident
				$([ $list_singular:ident : $list_name:ident $(($list_init:ty))? $($list_back:ident)? ])?
			 : $field_ty:ident ),*
		)?
	) => { paste! {
		pub struct $T<'brand, 'arena, V> {
			id: Option<usize>,
			next: Option<ptr!($T)>,
			prev: Option<ptr!($T)>,
			$($($custom_field: $custom_ty,)*)?
			$($($field: Option<ptr!($field_ty)>,)*)?
		}

		impl<'brand, 'arena, V> $T<'brand, 'arena, V> {
			fn new($($init_name: $init_ty,)? dcel: &mut Dcel<'brand, 'arena, V>) -> own_t!(Self) {
				let id = Some(dcel.$name.next_id());
				dcel.$name.alloc(Self {
					id,
					prev: None,
					next: None,
					$($($custom_field: $custom_expr,)*)?
					$($($field: None,)*)?
				}, &mut dcel.token)
			}
		}

		impl<'brand, 'arena, V> Entity<'brand, 'arena> for $T<'brand, 'arena, V> {
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

		#[allow(unused)]
		impl<'brand, 'arena, V> ptr!($T) {
			$($(
				$field_vis fn $field(self, token: &impl ReflAsRef<GhostToken<'brand>>) -> ptr!($field_ty) {
					self.[<maybe_ $field>](token).unwrap()
				}

				fn [<maybe_ $field>](self, token: &impl ReflAsRef<GhostToken<'brand>>) -> Option<ptr!($field_ty)> {
					self.borrow(token).$field
				}

				fn [<set_ $field>](self, x: ptr!($field_ty), token: &mut impl ReflAsMut<GhostToken<'brand>>) {
					self.[<set_opt_ $field>](Some(x), token);
				}

				fn [<set_opt_ $field>](self, x: Option<ptr!($field_ty)>, token: &mut impl ReflAsMut<GhostToken<'brand>>,) {
					self.borrow_mut(token).$field = x;
				}

				$(
					pub fn [<iter_ $field>]<'tok>(
						self,
						token: &'tok impl ReflAsRef<GhostToken<'brand>>,
					) -> EntityIterator<'tok, 'brand, 'arena, $field_ty<'brand, 'arena, V>>
					{
						EntityIterator::new(self.[<maybe_ $field>](token), token)
					}

					pub fn [<iter_mut_ $field>]<T: ReflAsMut<GhostToken<'brand>>>(
						self,
						token: &mut T,
						mut f: impl FnMut(ptr!($field_ty), &mut T),
					) {
						let Some(mut item) = self.[<maybe_ $field>](token) else {
							return;
						};

						let last = item.prev(token);
						while {
							f(item, token);
							item = item.next(token);
							!item.eq(last, token)
						} {}
					}

					fn [<add_ $list_singular>](
						self,
						x: ptr!($field_ty),
						token: &mut impl ReflAsMut<GhostToken<'brand>>,
					) {
						let list = Entity::list_add(x, self.[<maybe_ $field>](token), token);
						self.[<set_ $field>](list, token);

						$(
							let [<_ $list_back>] = ();
							x.[<set_ $name>](self, token);
						)?
					}

					fn [<add_new_ $list_singular>](
						self,
						$(init: $list_init,)?
						dcel: &mut Dcel<'brand, 'arena, V>,
					) -> own!($field_ty) {
						let x = $field_ty::new($(init as $list_init,)? dcel);
						self.[<add_ $list_singular>](*x, dcel);
						x
					}
				)?
			)*)?
		}

		#[allow(unused)]
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

				fn [<debug_ $field>](self, f: &mut Formatter) -> fmt::Result
				where V: Debug
				{
					$({
						let [<_ $list_singular>] = ();
						if true {
							// return short_debug_list(self.[<iter_ $field>](), f);
							return f.debug_list().entries(self.[<iter_ $field>]()).finish();
						}
					})?
					short_debug(self.$field(), f)
				}
			)*)?
		}

		impl<'tok, 'brand, 'arena, V: Debug> Debug for lens!($T) {
			fn fmt(&self, f: &mut Formatter) -> fmt::Result {
				f.debug_struct(stringify!($T))
					.field("id", &self.id())
					.field("prev", &short_debug_fn(self.prev()))
					.field("next", &short_debug_fn(self.next()))
					$($(
						.field(stringify!($field), &DisplayFn(|f| self.[<debug_ $field>](f)))
					)*)?
					$($(
						.field(stringify!($custom_field), &DisplayFn(|f| self.[<debug_ $custom_field>](f)))
					)*)?
					.finish()
			}
		}

		#[allow(unused)]
		impl<'brand, 'arena, V> Own<'brand, 'arena, $T<'brand, 'arena, V>> {
			fn free(self, dcel: &mut Dcel<'brand, 'arena, V>) {
				dcel.$name.free(&mut dcel.token, self)
			}
		}

		impl<'brand, 'arena, V> Hash for $T<'brand, 'arena, V> {
			fn hash<H: Hasher>(&self, state: &mut H) {
				self.id.hash(state);
			}
		}

		impl<'brand, 'arena, V> PartialEq for $T<'brand, 'arena, V> {
			fn eq(&self, other: &Self) -> bool {
				self.id() == other.id()
			}
		}
		impl<'brand, 'arena, V> Eq for $T<'brand, 'arena, V> {}
	}};
}

entity!(vertex: Vertex (init: V),
    data: V = init;
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

impl<'tok, 'brand, 'arena, V: Debug> lens!(Vertex) {
    pub fn data(&self) -> &V {
        self.item.data(self)
    }

    pub fn iter_outgoing(self) -> OutgoingIterator<'tok, 'brand, 'arena, V> {
        self.item.iter_outgoing(self.token)
    }

    pub fn find_outgoing(self, loop_: ptr!(Loop)) -> Option<lens!(HalfEdge)> {
        self.iter_outgoing().find(|x| x.loop_().eq(loop_))
    }

    fn debug_data(self, f: &mut Formatter) -> fmt::Result {
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

entity!(edge: Edge,
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

    fn set_half_edges(
        self,
        x: [own!(HalfEdge); 2],
        token: &mut impl ReflAsMut<GhostToken<'brand>>,
    ) {
        self.borrow_mut(token).half_edges = Some(x);
    }

    fn take_half_edges(
        self,
        token: &mut impl ReflAsMut<GhostToken<'brand>>,
    ) -> [own!(HalfEdge); 2] {
        self.borrow_mut(token).half_edges.take().unwrap()
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
    outer_loops[outer_loop: loop_ back]: Loop,
    inner_loops[inner_loop: loop_ back]: Loop,
    pub shell: Shell
);

entity!(shell: Shell;
    faces[face: face back]: Face,
    edges[edge: edge]: Edge,
    vertices[vertex: vertex (V)]: Vertex,
    pub body: Body
);

entity!(body: Body;
    shells[shell: shell back]: Shell
);

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

pub struct Mevvlfs<'brand, 'arena, V> {
    pub body: ptr!(Body),
    pub edge: own!(Edge),
    pub vertices: [own!(Vertex); 2],
    pub loop_: own!(Loop),
    pub face: own!(Face),
    pub shell: own!(Shell),
}

pub struct Melf<'brand, 'arena, V> {
    pub shell: ptr!(Shell),
    pub vertices: [ptr!(Vertex); 2],
    pub old_loop: ptr!(Loop),
    pub new_loop: own!(Loop),
    pub edge: own!(Edge),
    pub face: own!(Face),
}

pub struct Mev<'brand, 'arena, V> {
    pub shell: ptr!(Shell),
    pub loop_: ptr!(Loop),
    pub old_vertex: ptr!(Vertex),
    pub new_vertex: own!(Vertex),
    pub edge: own!(Edge),
}

pub struct Mve<'brand, 'arena, V> {
    pub shell: ptr!(Shell),
    pub old_edge: ptr!(Edge),
    pub new_edge: own!(Edge),
    pub vertex: own!(Vertex),
}

pub enum EulerOp<'brand, 'arena, V> {
    Mevvlfs(Mevvlfs<'brand, 'arena, V>),
    Melf(Melf<'brand, 'arena, V>),
    Mev(Mev<'brand, 'arena, V>),
    Mve(Mve<'brand, 'arena, V>),
}

macro_rules! euler_op {
    ($x:ident) => {
        impl<'brand, 'arena, V> From<$x<'brand, 'arena, V>> for EulerOp<'brand, 'arena, V> {
            fn from(op: $x<'brand, 'arena, V>) -> Self {
                Self::$x(op)
            }
        }
    };
}

euler_op!(Mevvlfs);
euler_op!(Melf);
euler_op!(Mev);
euler_op!(Mve);

#[derive(Debug, Error)]
pub enum KevvlfsError {
    #[error("edge vertices do not equal vertices")]
    EdgeVerticesMismatch,
    #[error("half_edge loop does not equal loop")]
    HalfEdgeLoopMismatch,
    #[error("loop is not cycle between half edges")]
    InvalidLoop,
    #[error("face outer loop does not match loop")]
    FaceOuterLoopMismatch,
    #[error("face has inner loops")]
    FaceHasInnerLoops,
    #[error("shell has more than one face")]
    ShellHasMoreThanOneFace,
    #[error("shell face does not match face")]
    ShellFaceMismatch,
    #[error("shell body does not match body")]
    ShellBodyMismatch,
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

impl<'brand, 'arena, V: Debug> Dcel<'brand, 'arena, V> {
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

    pub fn new<R, F, W: Debug>(fun: F) -> R
    where
        for<'new_brand, 'new_arena> F: FnOnce(Dcel<'new_brand, 'new_arena, W>) -> R,
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

    fn new_edge(&mut self, shell: ptr!(Shell)) -> (own!(Edge), [ptr!(HalfEdge); 2]) {
        let edge = shell.add_new_edge(self);

        let he1_own = HalfEdge::new(self);
        let he2_own = HalfEdge::new(self);

        let he1 = *he1_own;
        let he2 = *he2_own;

        edge.set_half_edges([he1_own, he2_own], self);

        he1.set_twin(he2, self);
        he2.set_twin(he1, self);
        he1.set_edge(*edge, self);
        he2.set_edge(*edge, self);

        (edge, [he1, he2])
    }

    #[inline(always)]
    fn origin(&mut self, v: ptr!(Vertex), h: ptr!(HalfEdge)) {
        v.set_outgoing(h, self);
        h.set_origin(v, self)
    }

    #[inline(always)]
    fn follow(&mut self, prev: ptr!(HalfEdge), next: ptr!(HalfEdge)) {
        next.set_prev(prev, self);
        prev.set_next(next, self);
    }

    pub fn undo(&mut self, op: impl Into<EulerOp<'brand, 'arena, V>>) {
        match op.into() {
            EulerOp::Mevvlfs(x) => self.kevvlfs(x),
            _ => todo!(),
        }
    }

    // Make Edge-Vertex-Vertex-Loop-Face-Shell

    pub fn mevvlfs(&mut self, body: ptr!(Body), data: [V; 2]) -> Mevvlfs<'brand, 'arena, V> {
        let [d1, d2] = data;

        let shell = body.add_new_shell(self);
        let face = shell.add_new_face(self);
        let (edge, [a, b]) = self.new_edge(*shell);
        let loop_ = face.add_new_outer_loop(self);
        let v1 = shell.add_new_vertex(d1, self);
        let v2 = shell.add_new_vertex(d2, self);

        self.origin(*v1, a);
        self.origin(*v2, b);

        loop_.add_half_edge(a, self);
        loop_.add_half_edge(b, self);

        Mevvlfs {
            body,
            edge,
            vertices: [v1, v2],
            loop_,
            face,
            shell,
        }
    }

    pub fn check_kevvlfs(&self, op: &Mevvlfs<'brand, 'arena, V>) -> Result<(), KevvlfsError> {
        let Mevvlfs {
            body,
            edge,
            vertices: [v1, v2],
            loop_,
            face,
            shell,
        } = op;

        mklens!(self, edge, loop_, face, shell, body, v1, v2);

        let [a, b] = edge.half_edges();
        let edge_verts = edge.vertices();

        or_err(
            edge_verts == [v1, v2] || edge_verts == [v2, v1],
            KevvlfsError::EdgeVerticesMismatch,
        )?;

        or_err(a.loop_() == loop_, KevvlfsError::HalfEdgeLoopMismatch)?;
        or_err(a.next() == b, KevvlfsError::InvalidLoop)?;
        or_err(b.next() == a, KevvlfsError::InvalidLoop)?;

        or_err(
            face.outer_loops() == loop_,
            KevvlfsError::FaceOuterLoopMismatch,
        )?;
        or_err(
            face.maybe_inner_loops().is_none(),
            KevvlfsError::FaceHasInnerLoops,
        )?;

        or_err(face.next() == face, KevvlfsError::ShellHasMoreThanOneFace)?;
        or_err(shell.faces() == face, KevvlfsError::ShellFaceMismatch)?;
        or_err(shell.body() == body, KevvlfsError::ShellBodyMismatch)?;

        Ok(())
    }

    pub fn try_kevvlfs(
        &mut self,
        op: Mevvlfs<'brand, 'arena, V>,
    ) -> Result<(), (Mevvlfs<'brand, 'arena, V>, KevvlfsError)> {
        if let Err(err) = self.check_kevvlfs(&op) {
            return Err((op, err));
        }

        let Mevvlfs {
            body,
            edge,
            vertices: [v1, v2],
            loop_,
            face,
            shell,
        } = op;

        let [a, b] = edge.take_half_edges(self);
        let shells = Entity::list_remove(*shell, self);
        body.set_opt_shells(shells, self);

        edge.free(self);
        a.free(self);
        b.free(self);
        loop_.free(self);
        face.free(self);
        shell.free(self);
        v1.free(self);
        v2.free(self);

        Ok(())
    }

    pub fn kevvlfs(&mut self, op: Mevvlfs<'brand, 'arena, V>) {
        self.try_kevvlfs(op).map_err(|(_, e)| e).unwrap()
    }

    pub fn mev(
        &mut self,
        shell: ptr!(Shell),
        loop_: ptr!(Loop),
        old_vertex: ptr!(Vertex),
        data: V,
    ) -> Mev<'brand, 'arena, V> {
        //
        //      o
        //  a /   \ d
        //   <     <
        //

        //    < n <
        //  b |   | c
        //      o
        //  a /   \ d
        //   <     <

        let (edge, [b, c]) = self.new_edge(shell);
        let new_vertex = shell.add_new_vertex(data, self);

        let a = old_vertex.find_outgoing(loop_, self).unwrap();
        let d = a.prev(self);

        self.follow(d, c);
        self.follow(c, b);
        self.follow(b, a);

        b.set_loop_(loop_, self);
        c.set_loop_(loop_, self);

        self.origin(*new_vertex, b);
        self.origin(old_vertex, c);

        Mev {
            shell,
            loop_,
            old_vertex,
            new_vertex,
            edge,
        }
    }

    pub fn melf(
        &mut self,
        shell: ptr!(Shell),
        vertices: [ptr!(Vertex); 2],
        old_loop: ptr!(Loop),
    ) -> Melf<'brand, 'arena, V> {
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

        let (edge, [a1, b1]) = self.new_edge(shell);
        let face = shell.add_new_face(self);
        let new_loop = face.add_new_outer_loop(self);

        let [v1, v2] = vertices;
        let [b0, a2] = vertices.map(|v| v.find_outgoing(old_loop, self).unwrap());

        let a0 = b0.prev(self);
        let b2 = a2.prev(self);

        self.origin(v1, a1);
        self.follow(a0, a1);
        self.follow(a1, a2);
        old_loop.set_half_edges(a1, self);
        a1.set_loop_(old_loop, self);

        self.origin(v2, b1);
        self.follow(b2, b1);
        self.follow(b1, b0);
        new_loop.set_half_edges(b1, self);
        new_loop.iter_mut_half_edges(self, |x, dcel| x.set_loop_(*new_loop, dcel));

        Melf {
            shell,
            vertices,
            old_loop,
            new_loop,
            edge,
            face,
        }
    }

    pub fn mve(
        &mut self,
        shell: ptr!(Shell),
        old_edge: ptr!(Edge),
        data: V,
    ) -> Mve<'brand, 'arena, V> {
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

        let (new_edge, [a2, b2]) = self.new_edge(shell);
        let v = shell.add_new_vertex(data, self);

        let [a1, b1] = old_edge.half_edges(self);
        let [v1, v2] = old_edge.vertices(self);

        let mut a3 = a1.next(self);
        let mut b3 = b2.prev(self);

        if a3.eq(b1, self) {
            a3 = b2;
        }
        if b3.eq(a1, self) {
            b3 = a2;
        }

        self.origin(*v, a2);
        self.origin(*v, b1);
        self.origin(v2, b2);

        self.follow(a1, a2);
        self.follow(a2, a3);
        self.follow(b3, b2);
        self.follow(b2, b1);

        Mve {
            shell,
            old_edge,
            new_edge,
            vertex: v,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Dcel;

    #[test]
    fn mev_cycle() {
        Dcel::<u32>::new(|mut dcel| {
            let body = dcel.new_body();
            let op = dcel.mevvlfs(*body, [0, 1]);
            let op2 = dcel.mev(*op.shell, *op.loop_, *op.vertices[1], 2);
            let op3 = dcel.mev(*op.shell, *op.loop_, *op2.new_vertex, 3);
            dcel.melf(*op.shell, [*op3.new_vertex, *op.vertices[0]], *op.loop_);

            let mut vertices = op
                .loop_
                .iter_half_edges(&dcel)
                .map(|x| *x.origin().data())
                .peekable();
            assert!((0..4)
                .cycle()
                .skip(*vertices.peek().unwrap() as _)
                .take(4)
                .eq(vertices));
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DcelDotOptions {
    pub twin: bool,
    pub next: bool,
    pub prev: bool,
}

impl DcelDotOptions {
    pub fn none() -> Self {
        Self {
            twin: false,
            next: false,
            prev: false,
        }
    }

    pub fn all() -> Self {
        Self {
            twin: true,
            next: true,
            prev: true,
        }
    }
}

pub fn dcel_write_dot<V: Debug>(
    dcel: &Dcel<V>,
    pos: impl Fn(&V) -> [f64; 2],
    name: impl Fn(&V, &mut Formatter) -> fmt::Result,
    f: &mut Formatter,
    opt: DcelDotOptions,
) -> fmt::Result {
    writeln!(f, "digraph DCEL {{")?;
    writeln!(f, "node [shape = circle]")?;
    //writeln!(f, "nodesep = 1")?;

    for shell in dcel.iter_bodies().flat_map(Lens::iter_shells) {
        for vertex in shell.iter_vertices() {
            let p = pos(vertex.data());

            writeln!(
                f,
                "vertex_{} [label=\"{}\", pos=\"{},{}!\"]",
                vertex.id(),
                DisplayFn(|f| name(vertex.data(), f)),
                p[0],
                p[1]
            )?;
        }

        for hedges in shell
            .iter_edges()
            .map(|x| x.half_edges())
            .flat_map(|[he1, he2]| [[he1, he2], [he2, he1]])
        {
            let ids = hedges.map(Lens::id);
            let vertices = hedges.map(|h| h.origin());
            let points = vertices.map(|v| pos(v.data()));

            let mut diff = [points[1][1] - points[0][1], points[1][0] - points[0][0]];

            let len = (diff[0] * diff[0] + diff[1] * diff[1]).sqrt();
            diff[0] *= -0.075;
            diff[1] *= 0.075;

            let mid = [
                (points[1][0] + points[0][0]) / 2.0 + diff[0],
                (points[1][1] + points[0][1]) / 2.0 + diff[1],
            ];

            writeln!(
                f,
                "half_edge_{} [pos=\"{},{}!\", shape=point, width=0.01, height=0.01]",
                ids[0], mid[0], mid[1]
            )?;
            writeln!(
                f,
                "vertex_{} -> half_edge_{} [arrowhead=none]",
                vertices[0].id(),
                ids[0]
            )?;
            writeln!(
                f,
                "half_edge_{} -> vertex_{} [label=\"{}\"]",
                ids[0],
                vertices[1].id(),
                ids[0]
            )?;

            if opt.twin {
                writeln!(
                    f,
                    "half_edge_{} -> half_edge_{} [color=\"red\"]",
                    ids[0], ids[1]
                )?;
            }

            if opt.next {
                writeln!(
                    f,
                    "half_edge_{} -> half_edge_{} [color=\"green\"]",
                    ids[0],
                    hedges[0].next().id(),
                )?;
            }

            if opt.prev {
                writeln!(
                    f,
                    "half_edge_{} -> half_edge_{} [color=\"blue\"]",
                    ids[0],
                    hedges[0].prev().id(),
                )?;
            }
        }
    }

    writeln!(f, "}}")
}

use std::io::Write;

fn main() {
    let show = |name, dcel: &Dcel<(&'static str, [i64; 2])>| {
        write!(
            &mut std::fs::File::create(name).unwrap(),
            "{}",
            DisplayFn(|f: &mut fmt::Formatter<'_>| dcel_write_dot(
                dcel,
                |v| v.1.map(|x| x as _),
                |v, f| write!(f, "{}", v.0),
                f,
                DcelDotOptions {
                    prev: false,
                    next: true,
                    twin: true,
                }
            ))
        )
        .unwrap();
    };

    GhostToken::new(|token| {
        let arena = DcelArena::default();
        let mut dcel = Dcel::from_token(token, &arena);

        let body = dcel.new_body();
        // Mevvlfs(a, [w, n], l, f, s)

        //let op = dcel.mevvlfs(*body, [("W", [-4, 0]), ("N", [0, 4])]);
        let op = dcel.mevvlfs(*body, [("W", [-4, 0]), ("N", [0, 4])]);
        let op2 = dcel.mev(*op.shell, *op.loop_, *op.vertices[1], ("E", [4, 0]));
        let op3 = dcel.mev(*op.shell, *op.loop_, *op2.new_vertex, ("S", [0, -4]));

        dcel.melf(*op.shell, [*op3.new_vertex, *op.vertices[0]], *op.loop_);
        dcel.melf(*op.shell, [*op.vertices[0], *op2.new_vertex], *op.loop_);

        show("cool_stuff.dot", &dcel);

        /*println!("{:?}", op.edge.lens(&dcel));
        println!("{:?}", op.vertices[0].lens(&dcel));
        println!("{:?}", op.vertices[1].lens(&dcel));
        println!("{:?}", op.loop_.lens(&dcel));
        println!("{:?}", op.face.lens(&dcel));
        println!("{:?}", op.shell.lens(&dcel));*/

        //dbg!(body.lens(&dcel));

        // dcel.undo(op);

        /*

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
