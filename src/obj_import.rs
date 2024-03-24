use crate::*;
pub use obj;
use obj::raw::object::RawObj;

#[derive(Debug, Error)]
pub enum ObjImportError {
    #[error("vertex {0} position index out of bounds")]
    InvalidPositionIndex(usize),
    #[error("half-edge between vertices {0} and {1} appears twice")]
    SameHalfEdge(usize, usize),
    #[error("half-edge between vertices {0} and {1} does not have a twin")]
    UnclaimedHalfEdge(usize, usize),
    #[error("empty face")]
    EmptyFace,
    #[error("vertex {0} is not connected to any edges")]
    StandaloneVertex(usize),
}

use ObjImportError::*;

pub struct ObjImport<'tok, 'brand, 'arena, V> {
    dcel: &'tok mut Dcel<'brand, 'arena, V>,
    obj: &'tok RawObj,
    shell: ptr!(Shell),
    half_edges: HashMap<(usize, usize), Option<ptr!(HalfEdge)>>,
    vertices: Vec<ptr!(Vertex)>,
}

struct CyclicWindows<T, I> {
    first: Option<T>,
    last: Option<T>,
    iter: I,
}

fn cyclic_windows<T, I>(iter: I) -> CyclicWindows<T, I> {
    CyclicWindows {
        first: None,
        last: None,
        iter,
    }
}

impl<T, I> Iterator for CyclicWindows<T, I>
where
    T: Clone,
    I: Iterator<Item = T>,
{
    type Item = (T, T);

    fn next(&mut self) -> Option<Self::Item> {
        let Some(item) = self.iter.next() else {
            let first = self.first.take()?;
            let last = self.last.take()?;
            return Some((last, first));
        };

        self.first.get_or_insert_with(|| item.clone());
        let Some(last) = self.last.replace(item.clone()) else {
            return self.next();
        };

        Some((last, item))
    }
}

impl<'tok, 'brand, 'arena, V> ObjImport<'tok, 'brand, 'arena, V> {
    pub fn import(
        dcel: &'tok mut Dcel<'brand, 'arena, V>,
        obj: &'tok RawObj,
        fun: impl Fn((f32, f32, f32, f32)) -> V,
    ) -> Result<own!(Body), ObjImportError> {
        let body = dcel.new_body();
        let shell = *body.add_new_shell(dcel);

        let vertices = obj
            .positions
            .iter()
            .map(|&x| *shell.add_new_vertex(fun(x), dcel))
            .collect();

        let mut imp = ObjImport {
            dcel,
            obj,
            shell,
            half_edges: HashMap::new(),
            vertices,
        };

        match imp.import_faces() {
            Ok(_) => Ok(body),
            Err(x) => {
                body.destroy(dcel);
                Err(x)
            }
        }
    }

    fn iter_polygon(p: &obj::raw::object::Polygon) -> impl DoubleEndedIterator<Item = usize> + '_ {
        use either::{Left, Right};
        use obj::raw::object::Polygon::*;

        match p {
            P(v) => Left(Left(v.iter().cloned())),
            PT(v) => Left(Right(v.iter().map(|&(x, _)| x))),
            PN(v) => Right(Left(v.iter().map(|&(x, _)| x))),
            PTN(v) => Right(Right(v.iter().map(|&(x, _, _)| x))),
        }
    }

    fn import_faces(&mut self) -> Result<(), ObjImportError> {
        for p in self.obj.polygons.iter() {
            if cyclic_windows(Self::iter_polygon(p))
                .any(|(a, b)| matches!(self.half_edges.get(&(a, b)), Some(None)))
            {
                self.import_face(Self::iter_polygon(p).rev())?;
            } else {
                self.import_face(Self::iter_polygon(p))?;
            }
        }

        if let Some((k, _)) = self.half_edges.iter().find(|(_, v)| v.is_some()) {
            Err(UnclaimedHalfEdge(k.1 + 1, k.0 + 1))
        } else if let Some((i, _)) = self
            .vertices
            .iter()
            .enumerate()
            .find(|(_, x)| x.maybe_outgoing(self.dcel).is_none())
        {
            Err(StandaloneVertex(i + 1))
        } else {
            Ok(())
        }
    }

    fn add_half_edge(
        &mut self,
        loop_: ptr!(Loop),
        prev: Option<ptr!(HalfEdge)>,
        vertices: [usize; 2],
    ) -> Result<ptr!(HalfEdge), ObjImportError> {
        use std::collections::hash_map::Entry::*;

        let [a, b] = vertices;
        let v = *self.vertices.get(a).ok_or(InvalidPositionIndex(a + 1))?;

        let he = match self.half_edges.entry((a, b)) {
            Occupied(mut e) => e.get_mut().take().ok_or(SameHalfEdge(a + 1, b + 1))?,
            Vacant(e) => {
                let (_, [he1, he2]) = Edge::create(self.shell, self.dcel);
                e.insert(None);
                self.half_edges.insert((b, a), Some(he2));
                he1
            }
        };

        he.update_origin(v, self.dcel);
        he.set_loop_(loop_, self.dcel);

        if let Some(prev) = prev {
            self.dcel.follow(prev, he);
        }

        Ok(he)
    }

    fn import_face(&mut self, mut it: impl Iterator<Item = usize>) -> Result<(), ObjImportError> {
        let face = *self.shell.add_new_face(self.dcel);
        let loop_ = *Loop::new(self.dcel);
        loop_.set_face(face, self.dcel);
        face.set_outer_loop(loop_, self.dcel);

        let fv = it.next().ok_or(EmptyFace)?;
        let (fe, le, lv) = it.try_fold((None, None, fv), |(fe, le, a), b| {
            let he = self.add_half_edge(loop_, le, [a, b])?;
            Ok((fe.or(Some(he)), Some(he), b))
        })?;

        let fe = fe.ok_or(EmptyFace)?;
        let le = self.add_half_edge(loop_, le, [lv, fv])?;
        self.dcel.follow(le, fe);

        loop_.set_half_edges(fe, self.dcel);

        Ok(())
    }
}
