use crate::*;

// Make Edge-Vertex-Vertex-Loop-Face-Shell

/// Operator corresponding to MEVVLS in SNUMOD.
///
/// See [`Dcel::mevvlfs`] for details.
pub struct Mevvlfs<'brand, 'arena, V> {
    pub body: ptr!(Body),
    pub data: [V; 2],
}

impl<'brand, 'arena, V> Mevvlfs<'brand, 'arena, V> {
    pub fn new(body: ptr!(Body), data: [V; 2]) -> Self {
        Self { body, data }
    }
}

impl<'brand, 'arena, V> Operator<'brand, 'arena, V> for Mevvlfs<'brand, 'arena, V> {
    type Inverse = Kevvlfs<'brand, 'arena, V>;
    type Error = Infallible;
    type Check = ();

    fn check(&self, _dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error> {
        Ok(())
    }

    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>> {
        try_check!(self, dcel);

        let Mevvlfs {
            body,
            data: [d1, d2],
        } = self;

        let shell = body.add_new_shell(dcel);
        let face = shell.add_new_face(dcel);
        let (edge, [a, b]) = Edge::create(*shell, dcel);
        let loop_ = Loop::new(dcel);
        let v1 = shell.add_new_vertex(d1, dcel);
        let v2 = shell.add_new_vertex(d2, dcel);

        loop_.set_face(*face, dcel);
        face.set_outer_loop(*loop_, dcel);

        a.update_origin(*v1, dcel);
        b.update_origin(*v2, dcel);

        loop_.add_half_edge(a, dcel);
        loop_.add_half_edge(b, dcel);

        Ok(Kevvlfs {
            edge,
            vertices: [v1, v2],
            loop_,
            face,
            shell,
        })
    }
}

/// Operator corresponding to KEVVLS in SNUMOD.
///
/// See [`Dcel::kevvlfs`] for details.
pub struct Kevvlfs<'brand, 'arena, V> {
    pub edge: own!(Edge),
    pub vertices: [own!(Vertex); 2],
    pub loop_: own!(Loop),
    pub face: own!(Face),
    pub shell: own!(Shell),
}

/// Precondition Error for [`Kevvlfs`].
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
}

impl<'brand, 'arena, V> Kevvlfs<'brand, 'arena, V> {
    pub fn new(
        edge: own!(Edge),
        vertices: [own!(Vertex); 2],
        loop_: own!(Loop),
        face: own!(Face),
        shell: own!(Shell),
    ) -> Self {
        Self {
            edge,
            vertices,
            loop_,
            face,
            shell,
        }
    }
}

impl<'brand, 'arena, V> Operator<'brand, 'arena, V> for Kevvlfs<'brand, 'arena, V> {
    type Inverse = Mevvlfs<'brand, 'arena, V>;
    type Error = KevvlfsError;
    type Check = ();

    fn check(&self, dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error> {
        let Kevvlfs {
            edge,
            vertices: [v1, v2],
            loop_,
            face,
            shell,
        } = self;

        mklens!(dcel, edge, loop_, face, shell, v1, v2);

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
            face.outer_loop() == loop_,
            KevvlfsError::FaceOuterLoopMismatch,
        )?;
        or_err(
            face.maybe_inner_loops().is_none(),
            KevvlfsError::FaceHasInnerLoops,
        )?;

        or_err(face.next() == face, KevvlfsError::ShellHasMoreThanOneFace)?;
        or_err(shell.faces() == face, KevvlfsError::ShellFaceMismatch)?;

        Ok(())
    }

    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>> {
        try_check!(self, dcel);

        let Kevvlfs {
            edge,
            vertices,
            loop_,
            face,
            shell,
        } = self;

        let body = shell.body(dcel);
        body.remove_shell(*shell, dcel);

        edge.destroy(dcel);
        loop_.free(dcel);
        face.free(dcel);
        shell.free(dcel);

        Ok(Mevvlfs {
            body,
            data: vertices.map(|v| v.destroy(dcel)),
        })
    }
}
