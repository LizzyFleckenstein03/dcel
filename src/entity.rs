use crate::*;

// trait for a kind of topological element (i.e. Vertex, HalfEdge, Face)
pub(crate) trait Entity<'brand, 'arena>: Eq + Sized {
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

						let last = item;
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

					fn [<remove_ $list_singular>](
						self,
						x: ptr!($field_ty),
						token: &mut impl ReflAsMut<GhostToken<'brand>>,
					) {
						let list = Entity::list_remove(x, token);
						self.[<set_opt_ $field>](list, token);
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
