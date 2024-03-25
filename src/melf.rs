use crate::*;

// Make Edge-Vertex

/// Operator corresponding to MEL in SNUMOD.
///
/// See [`Dcel::melf`] for details.
pub struct Melf<'brand, 'arena, V> {
    pub vertices: [ptr!(Vertex); 2],
    pub loop_: ptr!(Loop),
}

impl<'brand, 'arena, V> Melf<'brand, 'arena, V> {
    pub fn new(vertices: [ptr!(Vertex); 2], loop_: ptr!(Loop)) -> Self {
        Self { vertices, loop_ }
    }
}

/// Precondition Error for [`Melf`].
#[derive(Debug, Error)]
pub enum MelfError {
    #[error("vertex is not part of loop")]
    VertexLoopMismatch,
}

impl<'brand, 'arena, V> Operator<'brand, 'arena, V> for Melf<'brand, 'arena, V> {
    type Inverse = Kelf<'brand, 'arena, V>;
    type Error = MelfError;
    type Check = [ptr!(HalfEdge); 2];

    fn check(&self, dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error> {
        let b0 = self.vertices[0]
            .find_outgoing(self.loop_, dcel)
            .ok_or(MelfError::VertexLoopMismatch)?;
        let a2 = self.vertices[1]
            .find_outgoing(self.loop_, dcel)
            .ok_or(MelfError::VertexLoopMismatch)?;

        Ok([b0, a2])
    }

    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>> {
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

        let [b0, a2] = try_check!(self, dcel);
        let a0 = b0.prev(dcel);
        let b2 = a2.prev(dcel);

        let old_loop = self.loop_;
        let [v1, v2] = self.vertices;
        let shell = old_loop.face(dcel).shell(dcel);

        let (edge, [a1, b1]) = Edge::create(shell, dcel);
        let face = shell.add_new_face(dcel);
        let new_loop = Loop::new(dcel); // face.add_new_outer_loop(self);
        new_loop.set_face(*face, dcel);
        face.set_outer_loop(*new_loop, dcel);

        a1.update_origin(v1, dcel);
        dcel.follow(a0, a1);
        dcel.follow(a1, a2);
        old_loop.set_half_edges(a1, dcel);
        a1.set_loop_(old_loop, dcel);

        b1.update_origin(v2, dcel);
        dcel.follow(b2, b1);
        dcel.follow(b1, b0);
        new_loop.set_half_edges(b1, dcel);
        new_loop.update_connectivity(dcel);

        Ok(Kelf {
            loop_: new_loop,
            edge,
            face,
        })
    }
}

/// Operator corresponding to KEL in SNUMOD.
///
/// See [`Dcel::kelf`] for details.
pub struct Kelf<'brand, 'arena, V> {
    pub edge: own!(Edge),
    pub loop_: own!(Loop),
    pub face: own!(Face),
}

/// Precondition Error for [`Kelf`].
impl<'brand, 'arena, V> Kelf<'brand, 'arena, V> {
    pub fn new(edge: own!(Edge), loop_: own!(Loop), face: own!(Face)) -> Self {
        Self { edge, loop_, face }
    }
}

#[derive(Debug, Error)]
pub enum KelfError {
    #[error("edge is not part of loop")]
    EdgeLoopMismatch,
    #[error("loop is not outer loop of face")]
    FaceLoopMismatch,
    #[error("face has inner loops")]
    HasInnerLoops,
}

impl<'brand, 'arena, V> Operator<'brand, 'arena, V> for Kelf<'brand, 'arena, V> {
    type Inverse = Melf<'brand, 'arena, V>;
    type Error = KelfError;
    type Check = [ptr!(HalfEdge); 2];

    fn check(&self, dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error> {
        use KelfError::*;

        let [mut a1, mut b1] = self.edge.lens(dcel).half_edges();

        if a1.loop_().eq(*self.loop_) {
            [a1, b1] = [b1, a1];
        }

        or_err(b1.loop_().eq(*self.loop_), EdgeLoopMismatch)?;
        or_err(
            self.face.outer_loop(dcel).eq(*self.loop_, dcel),
            FaceLoopMismatch,
        )?;
        or_err(self.face.maybe_inner_loops(dcel).is_none(), HasInnerLoops)?;

        Ok([a1.item, b1.item])
    }

    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>> {
        let [a1, b1] = try_check!(self, dcel);

        let Kelf { edge, loop_, face } = self;
        let shell = face.shell(dcel);

        let a0 = a1.prev(dcel);
        let b0 = b1.next(dcel);
        let a2 = a1.next(dcel);
        let b2 = b1.prev(dcel);

        let v1 = a1.origin(dcel);
        let v2 = b1.origin(dcel);

        let old_loop = a1.loop_(dcel);

        dcel.follow(a0, b0);
        dcel.follow(b2, a2);

        old_loop.set_half_edges(a0, dcel);
        old_loop.update_connectivity(dcel);

        shell.remove_edge(*edge, dcel);
        shell.remove_face(*face, dcel);

        edge.destroy(dcel);
        face.free(dcel);
        loop_.free(dcel);

        Ok(Melf {
            vertices: [v1, v2],
            loop_: old_loop,
        })
    }
}
