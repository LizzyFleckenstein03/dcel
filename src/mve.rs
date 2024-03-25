use crate::*;

// Make Vertex-Edge

/// Operator corresponding to MVE in SNUMOD.
///
/// See [`Dcel::mve`] for details.
pub struct Mve<'brand, 'arena, V> {
    pub edge: ptr!(Edge),
    pub data: V,
}

impl<'brand, 'arena, V> Mve<'brand, 'arena, V> {
    pub fn new(edge: ptr!(Edge), data: V) -> Self {
        Self { edge, data }
    }
}

impl<'brand, 'arena, V> Operator<'brand, 'arena, V> for Mve<'brand, 'arena, V> {
    type Inverse = Kve<'brand, 'arena, V>;
    type Error = Infallible;
    type Check = ();

    fn check(&self, _dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error> {
        Ok(())
    }

    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>> {
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

        try_check!(self, dcel);

        let Mve { edge, data } = self;

        let shell = edge.lens(dcel).half_edges()[0].loop_().face().shell().item;

        let (new_edge, [a2, b2]) = Edge::create(shell, dcel);
        let v = shell.add_new_vertex(data, dcel);

        let [a1, b1] = edge.half_edges(dcel);
        let v2 = edge.vertices(dcel)[1];

        let mut a3 = a1.next(dcel);
        let mut b3 = b1.prev(dcel);

        if a3.eq(b1, dcel) {
            a3 = b2;
        }
        if b3.eq(a1, dcel) {
            b3 = a2;
        }

        a2.update_origin(*v, dcel);
        b1.update_origin(*v, dcel);
        b2.update_origin(v2, dcel);

        dcel.follow(a1, a2);
        dcel.follow(a2, a3);
        dcel.follow(b3, b2);
        dcel.follow(b2, b1);

        a2.set_loop_(a1.loop_(dcel), dcel);
        b2.set_loop_(b1.loop_(dcel), dcel);

        Ok(Kve {
            edge: new_edge,
            vertex: v,
        })
    }
}

/// Operator corresponding to KVE in SNUMOD.
///
/// See [`Dcel::kve`] for details.
pub struct Kve<'brand, 'arena, V> {
    pub edge: own!(Edge),
    pub vertex: own!(Vertex),
}

impl<'brand, 'arena, V> Kve<'brand, 'arena, V> {
    pub fn new(edge: own!(Edge), vertex: own!(Vertex)) -> Self {
        Self { edge, vertex }
    }
}

/// Precondition Error for [`Kve`].
#[derive(Debug, Error)]
pub enum KveError {
    #[error("vertex is not part of edge")]
    VertexEdgeMismatch,
    #[error("vertex has more than two outgoing edges")]
    TooManyOutgoing,
    #[error("vertex is turning point, use KEV")]
    VertexTurningPoint,
}

impl<'brand, 'arena, V> Operator<'brand, 'arena, V> for Kve<'brand, 'arena, V> {
    type Inverse = Mve<'brand, 'arena, V>;
    type Error = KveError;
    type Check = [ptr!(HalfEdge); 2];

    fn check(&self, dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error> {
        use KveError::*;

        let [mut a2, mut b2] = self.edge.lens(dcel).half_edges();
        if b2.origin().eq(*self.vertex) {
            [a2, b2] = [b2, a2];
        }

        or_err(a2.origin().eq(*self.vertex), VertexEdgeMismatch)?;
        or_err(
            self.vertex.iter_outgoing(dcel).count() == 2,
            TooManyOutgoing,
        )?;
        or_err(b2.next() != a2, VertexTurningPoint)?;

        Ok([a2.item, b2.item])
    }

    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>> {
        let [a2, b2] = try_check!(self, dcel);

        let a1 = a2.prev(dcel);
        let b1 = b2.next(dcel);

        let v2 = b2.origin(dcel);

        let mut a3 = a2.next(dcel);
        if a3.eq(b2, dcel) {
            a3 = b1;
        }
        let mut b3 = b2.prev(dcel);
        if b3.eq(a2, dcel) {
            b3 = a1;
        }

        dcel.follow(a1, a3);
        dcel.follow(b3, b1);

        b1.update_origin(v2, dcel);
        a1.loop_(dcel).set_half_edges(a1, dcel);
        b1.loop_(dcel).set_half_edges(b1, dcel);

        let shell = a1.loop_(dcel).face(dcel).shell(dcel);
        shell.remove_edge(*self.edge, dcel);
        shell.remove_vertex(*self.vertex, dcel);

        self.edge.destroy(dcel);

        Ok(Mve {
            edge: a1.edge(dcel),
            data: self.vertex.destroy(dcel),
        })
    }
}
