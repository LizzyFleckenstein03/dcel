use crate::*;

// Make Edge-Vertex

/// Operator corresponding to MEV in SNUMOD.
///
/// See [`Dcel::mev`] for details.
pub struct Mev<'brand, 'arena, V> {
    pub loop_: ptr!(Loop),
    pub vertex: ptr!(Vertex),
    pub data: V,
}

impl<'brand, 'arena, V> Mev<'brand, 'arena, V> {
    pub fn new(loop_: ptr!(Loop), vertex: ptr!(Vertex), data: V) -> Self {
        Self {
            loop_,
            vertex,
            data,
        }
    }
}

/// Precondition Error for [`Mev`].
#[derive(Debug, Error)]
pub enum MevError {
    #[error("vertex is not part of loop")]
    VertexLoopMismatch,
}

impl<'brand, 'arena, V> Operator<'brand, 'arena, V> for Mev<'brand, 'arena, V> {
    type Inverse = Kev<'brand, 'arena, V>;
    type Error = MevError;
    type Check = ptr!(HalfEdge);

    fn check(&self, dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error> {
        self.vertex
            .find_outgoing(self.loop_, dcel)
            .ok_or(MevError::VertexLoopMismatch)
    }

    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>> {
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

        let a = try_check!(self, dcel);
        let d = a.prev(dcel);

        let shell = self.loop_.face(dcel).shell(dcel);
        let (edge, [b, c]) = Edge::create(shell, dcel);
        let vertex = shell.add_new_vertex(self.data, dcel);

        dcel.follow(d, c);
        dcel.follow(c, b);
        dcel.follow(b, a);

        b.set_loop_(self.loop_, dcel);
        c.set_loop_(self.loop_, dcel);

        b.update_origin(*vertex, dcel);
        c.update_origin(self.vertex, dcel);

        Ok(Kev { edge, vertex })
    }
}

/// Operator corresponding to KEV in SNUMOD.
///
/// See [`Dcel::kev`] for details.
pub struct Kev<'brand, 'arena, V> {
    pub edge: own!(Edge),
    pub vertex: own!(Vertex),
}

impl<'brand, 'arena, V> Kev<'brand, 'arena, V> {
    pub fn new(edge: own!(Edge), vertex: own!(Vertex)) -> Self {
        Self { edge, vertex }
    }
}

/// Precondition Error for [`Kev`].
#[derive(Debug, Error)]
pub enum KevError {
    #[error("half edges don't go back and forth between new and old vertex")]
    NotBackForth,
    #[error("new vertex is not the turning point")]
    EdgeVertexMismatch,
    #[error("vertex has more than one outgoing edge")]
    VertexNotSingleton,
}

impl<'brand, 'arena, V> Operator<'brand, 'arena, V> for Kev<'brand, 'arena, V> {
    type Inverse = Mev<'brand, 'arena, V>;
    type Error = KevError;
    type Check = [ptr!(HalfEdge); 2];

    fn check(&self, dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error> {
        use KevError::*;

        let [mut b, mut c] = self.edge.lens(dcel).half_edges();

        if b.next() == c {
            [b, c] = [c, b];
        }

        or_err(c.next() == b, NotBackForth)?;
        or_err(b.origin().eq(*self.vertex), EdgeVertexMismatch)?;

        or_err(
            self.vertex.iter_outgoing(dcel).count() == 1,
            VertexNotSingleton,
        )?;

        Ok([b.item, c.item])
    }

    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>> {
        let [b, c] = try_check!(self, dcel);

        let a = b.next(dcel);
        let d = c.prev(dcel);
        dcel.follow(d, a);

        let shell = a.loop_(dcel).face(dcel).shell(dcel);
        shell.remove_edge(*self.edge, dcel);
        shell.remove_vertex(*self.vertex, dcel);

        self.edge.destroy(dcel);
        let data = self.vertex.destroy(dcel);

        Ok(Mev {
            data,
            vertex: a.origin(dcel),
            loop_: a.loop_(dcel),
        })
    }
}
