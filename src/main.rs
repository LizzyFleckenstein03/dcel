#![allow(unused)]
// the cell! macro will expand to complex types but makes things easier to read for humans
// unlike type definitions, a macro can capture the 'brand and 'arena lifetimes from the scope
#![allow(clippy::type_complexity)]

use either::Either::{self, *};
use ghost_cell::{GhostBorrow, GhostCell, GhostToken};
use typed_arena::Arena;

type Id = Option<usize>;

// trait for a kind of topological element (i.e. Vertex, HalfEdge, Face)
trait Kind {
    type Init;

    fn new(id: usize, init: Self::Init) -> Self;

    fn is_alive(&self) -> bool {
        self.get_id().is_some()
    }

    fn get_id(&self) -> Id;
    fn clear(&mut self);
}

macro_rules! cell_t {
	($T:ty) => {
		&'arena GhostCell<'brand, $T>
	}
}

macro_rules! cell {
	($T:ident) => {
		&'arena GhostCell<'brand, $T<'brand, 'arena, V>>
	};
}

macro_rules! impl_kind {
	($T:ident, $init_name:ident: $init_ty:ty $(, $($init_field:ident : $init_expr:tt),* )? $(; $($fields:ident),*)?) => {
		impl<'brand, 'arena, V> Kind for $T<'brand, 'arena, V> {
			type Init = $init_ty;

			fn get_id(&self) -> Id {
				self.id
			}

			fn new(id: usize, $init_name: $init_ty) -> Self {
				Self {
					id: Some(id),
					$($($init_field: $init_expr,)*)?
					$($($fields: Default::default(),)*)?
				}
			}

			fn clear(&mut self) {
				self.id = Default::default();
				#[cfg(debug_assertions)]
				{ $($(self.$fields = Default::default();)*)? }
			}
		}

		impl<'brand, 'arena, V: Default> PartialEq for $T<'brand, 'arena, V> {
			fn eq(&self, other: &Self) -> bool {
				self.get_id() == other.get_id()
			}
		}
		impl<'brand, 'arena, V: Default> Eq for $T<'brand, 'arena, V> {}
	};
}

use std::fmt;

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

macro_rules! impl_kind_debug {
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
}

// responsible for allocation of a certain Kind
struct Container<'brand, 'arena, T: Kind> {
    next_id: usize,
    arena: &'arena Arena<T>,
    elements: Vec<cell_t!(T)>,
    freelist: Vec<cell_t!(T)>,
}

impl<'brand, 'arena, T: Kind> Container<'brand, 'arena, T> {
    fn new(arena: &'arena Arena<T>) -> Self {
        Self {
            next_id: 0,
            arena,
            elements: Vec::new(),
            freelist: Vec::new(),
        }
    }

    fn alloc(
        &mut self,
        token: &mut GhostToken<'brand>,
        init: T::Init, /*f: impl FnOnce(Id) -> T*/
    ) -> cell_t!(T) {
        let id = self.next_id;
        self.next_id += 1;

        let t = Kind::new(id, init);

        if let Some(cell) = self.freelist.pop() {
            *cell.borrow_mut(token) = t;
            cell
        } else {
            let cell = GhostCell::from_mut(self.arena.alloc(t));
            self.elements.push(cell);
            cell
        }
    }

    fn free(&mut self, token: &mut GhostToken<'brand>, cell: cell_t!(T)) {
        debug_assert!(!cell.borrow(token).is_alive(), "double free");
        cell.borrow_mut(token).clear();
        self.freelist.push(cell);
    }
}

#[derive(Default)]
struct DcelAllocator<'brand, 'arena, V> {
    edge: Arena<HalfEdge<'brand, 'arena, V>>,
    vertex: Arena<Vertex<'brand, 'arena, V>>,
    face: Arena<Face<'brand, 'arena, V>>,
}

struct Dcel<'brand, 'arena, V: Default> {
    token: GhostToken<'brand>,
    half_edges: Container<'brand, 'arena, HalfEdge<'brand, 'arena, V>>,
    vertices: Container<'brand, 'arena, Vertex<'brand, 'arena, V>>,
    faces: Container<'brand, 'arena, Face<'brand, 'arena, V>>,
}

struct Vertex<'brand, 'arena, V> {
    id: Id,
    data: V,
    outgoing: Option<cell!(HalfEdge)>,
}
//type VertexRef<'brand, 'arena, V> = &'arena GhostCell<'brand, Vertex<'brand, 'arena, V>>;
impl_kind!(Vertex, init: V, data: init; outgoing);
impl_kind_debug!(Vertex, data, outgoing);

struct HalfEdge<'brand, 'arena, V> {
    id: Id,
    next: Option<cell!(HalfEdge)>,
    origin: Option<cell!(Vertex)>,
    twin: Option<cell!(HalfEdge)>,
    face: Option<cell!(Face)>,
    prev: Option<cell!(HalfEdge)>,
}
//type HalfEdgeRef<'brand, 'arena, V> = &'arena GhostCell<'brand, HalfEdge<'brand, 'arena, V>>;
impl_kind!(HalfEdge, init: (); origin, twin, face, next, prev);
impl_kind_debug!(HalfEdge, origin, twin, face, next, prev);

/*
struct FaceL<'brand, 'arena, V> {
    id: Id,
    outer: Vec<cell!(Loop)>,
    inner: Vec<cell!(Loop)>,
    solid: Option<cell!(Solid)>,
}

struct Solid<'brand, 'arena, V> {
    id: Id,
    faces: Vec<cell!(Faces)>,
    half_edges: Vec<cell!(HalfEdge)>,
}*/

struct Face<'brand, 'arena, V> {
    id: Id,
    outer: Vec<cell!(HalfEdge)>,
    inner: Vec<cell!(HalfEdge)>,
}
//type FaceRef<'brand, 'arena, V> = &'arena GhostCell<'brand, Face<'brand, 'arena, V>>;
impl_kind!(Face, init: (); outer, inner);
impl_kind_debug!(Face);

impl<'brand, 'arena, V: Default> Dcel<'brand, 'arena, V> {
    fn new(token: GhostToken<'brand>, alloc: &'arena DcelAllocator<'brand, 'arena, V>) -> Self {
        Self {
            token,
            half_edges: Container::new(&alloc.edge),
            vertices: Container::new(&alloc.vertex),
            faces: Container::new(&alloc.face),
        }
    }

    pub fn mevvls(&mut self, data: [V; 2]) -> (cell!(HalfEdge), [cell!(Vertex); 2], cell!(Face)) {
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
    fn twin(&mut self, a: cell!(HalfEdge), b: cell!(HalfEdge)) {
        a.borrow_mut(&mut self.token).twin = Some(b);
        b.borrow_mut(&mut self.token).twin = Some(a);
    }

    #[inline(always)]
    fn origin(&mut self, v: cell!(Vertex), h: cell!(HalfEdge)) {
        v.borrow_mut(&mut self.token).outgoing = Some(h);
        h.borrow_mut(&mut self.token).origin = Some(v);
    }

    #[inline(always)]
    fn follow(&mut self, prev: cell!(HalfEdge), next: cell!(HalfEdge)) {
        next.borrow_mut(&mut self.token).prev = Some(prev);
        prev.borrow_mut(&mut self.token).next = Some(next);
    }

    pub fn mve(
        &mut self,
        edge: cell!(HalfEdge),
        data: V,
    ) -> Option<(cell!(HalfEdge), cell!(Vertex))> {
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

    // pub fn mel(&mut self, b0: cell!(HalfEdge), a2: cell!(HalfEdge)) -> Option<()> {
    pub fn mel(&mut self, v1: cell!(Vertex), v2: cell!(Vertex)) -> Option<()> {
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
        from: cell!(Vertex),
        data: V,
    ) -> (cell!(Vertex), cell!(HalfEdge), cell!(HalfEdge)) {
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

    //fn mekh(&mut self, )
}

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

use std::io::Write;

fn main() {
    GhostToken::new(|token| {
        let alloc = DcelAllocator::default();
        let mut dcel = Dcel::new(token, &alloc);

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

        dcel.mel(/*a, b.borrow(&dcel.token).twin.unwrap()*/ w, n);
        show("4.dot", &dcel);

        eprintln!(
            "{} {}",
            a.borrow(&dcel.token).id.unwrap(),
            b.borrow(&dcel.token).id.unwrap()
        );

        /*
        print!(
            "{}",
            DisplayFn(|f: &mut fmt::Formatter<'_>| {
                for v in dcel.vertices.elements.iter() {
                    DcelDebug::fmt(v, true, &dcel.token, f)?;
                }

                for h in dcel.half_edges.elements.iter() {
                    DcelDebug::fmt(h, true, &dcel.token, f)?;
                }

                Ok(())
            })
        );*/
    });
}
