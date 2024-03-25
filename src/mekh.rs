use crate::*;

/// Operator corresponding to MEKH in SNUMOD.
///
/// See [`Dcel::mekh`] for details.
pub struct Mekh<'brand, 'arena, V> {
    pub shell: ptr!(Shell),
    pub into_loop: ptr!(Loop),
    pub into_vertex: ptr!(Vertex),
    pub hole_loop: own!(Loop),
    pub hole_vertex: ptr!(Vertex),
}

impl<'brand, 'arena, V> Mekh<'brand, 'arena, V> {
    pub fn new(
        shell: ptr!(Shell),
        into_loop: ptr!(Loop),
        into_vertex: ptr!(Vertex),
        hole_loop: own!(Loop),
        hole_vertex: ptr!(Vertex),
    ) -> Self {
        Self {
            shell,
            into_loop,
            into_vertex,
            hole_loop,
            hole_vertex,
        }
    }
}

/// Precondition Error for [`Mekh`].
#[derive(Debug, Error)]
pub enum MekhError {
    #[error("cannot join loop with itself")]
    SameLoop,
    #[error("loops do not share the same face")]
    LoopFaceMismatch,
    #[error("hole loop is an outer loop")]
    HoleIsOuter,
    #[error("vertex is not part of loop")]
    VertexLoopMismatch,
}

impl<'brand, 'arena, V> Operator<'brand, 'arena, V> for Mekh<'brand, 'arena, V> {
    type Inverse = Kemh<'brand, 'arena, V>;
    type Error = MekhError;
    type Check = [ptr!(HalfEdge); 2];

    fn check(&self, dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error> {
        use MekhError::*;

        let into_loop = self.into_loop.lens(dcel);
        or_err(!into_loop.eq(*self.hole_loop), SameLoop)?;
        or_err(
            into_loop.face().eq(self.hole_loop.face(dcel)),
            LoopFaceMismatch,
        )?;
        or_err(!self.hole_loop.is_outer(dcel), HoleIsOuter)?;

        let into_he = self
            .into_vertex
            .find_outgoing(self.into_loop, dcel)
            .ok_or(VertexLoopMismatch)?;
        let hole_he = self
            .hole_vertex
            .find_outgoing(*self.hole_loop, dcel)
            .ok_or(VertexLoopMismatch)?;

        Ok([into_he, hole_he])
    }

    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>> {
        let [b0, a2] = try_check!(self, dcel);

        let Mekh {
            shell,
            into_loop,
            into_vertex,
            hole_loop,
            hole_vertex,
        } = self;

        let (edge, [a1, b1]) = Edge::create(shell, dcel);

        let a0 = b0.prev(dcel);
        let b2 = a2.prev(dcel);

        a1.update_origin(into_vertex, dcel);
        dcel.follow(a0, a1);
        dcel.follow(a1, a2);

        b1.update_origin(hole_vertex, dcel);
        dcel.follow(b2, b1);
        dcel.follow(b1, b0);

        into_loop.update_connectivity(dcel);

        hole_loop.face(dcel).remove_inner_loop(*hole_loop, dcel);
        hole_loop.free(dcel);

        Ok(Kemh {
            shell,
            edge,
            loop_: into_loop,
            hole_vertex,
        })
    }
}

/// Operator corresponding to KEMH in SNUMOD.
///
/// See [`Dcel::kemh`] for details.
pub struct Kemh<'brand, 'arena, V> {
    pub shell: ptr!(Shell),
    pub edge: own!(Edge),
    pub loop_: ptr!(Loop),
    pub hole_vertex: ptr!(Vertex),
}

/// Precondition Error for [`Kemh`].
#[derive(Error, Debug)]
pub enum KemhError {
    #[error("vertex is not part of edge")]
    HalfEdgeVertexMismatch,
    #[error("both half edges need to be part of loop")]
    HalfEdgeLoopMismatch,
}

impl<'brand, 'arena, V> Kemh<'brand, 'arena, V> {
    pub fn new(
        shell: ptr!(Shell),
        edge: own!(Edge),
        loop_: ptr!(Loop),
        hole_vertex: ptr!(Vertex),
    ) -> Self {
        Self {
            shell,
            edge,
            loop_,
            hole_vertex,
        }
    }
}

impl<'brand, 'arena, V> Operator<'brand, 'arena, V> for Kemh<'brand, 'arena, V> {
    type Inverse = Mekh<'brand, 'arena, V>;
    type Error = KemhError;
    type Check = [ptr!(HalfEdge); 2];

    fn check(&self, dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error> {
        use KemhError::*;
        let Kemh {
            edge,
            loop_,
            hole_vertex,
            ..
        } = self;

        let [mut a, mut b] = edge.lens(dcel).half_edges();

        if a.origin().eq(*hole_vertex) {
            [b, a] = [a, b];
        } else {
            or_err(b.origin().eq(*hole_vertex), HalfEdgeVertexMismatch)?;
        }

        or_err(
            a.loop_().eq(*loop_) && b.loop_().eq(*loop_),
            HalfEdgeLoopMismatch,
        )?;

        Ok([a.item, b.item])
    }

    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>> {
        let [a1, b1] = try_check!(self, dcel);
        let Kemh {
            shell,
            edge,
            loop_: into_loop,
            hole_vertex,
        } = self;

        let hole_loop = into_loop.face(dcel).add_new_inner_loop(dcel);
        let into_vertex = a1.origin(dcel);

        let a0 = a1.prev(dcel);
        let a2 = a1.next(dcel);

        let b0 = b1.next(dcel);
        let b2 = b1.prev(dcel);

        dcel.follow(a0, b0);
        dcel.follow(b2, a2);

        b0.update_origin(into_vertex, dcel);
        a2.update_origin(hole_vertex, dcel);

        hole_loop.set_half_edges(a2, dcel);
        hole_loop.update_connectivity(dcel);

        shell.remove_edge(*edge, dcel);
        edge.destroy(dcel);

        Ok(Mekh {
            shell,
            into_loop,
            into_vertex,
            hole_loop,
            hole_vertex,
        })
    }
}
