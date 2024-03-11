use crate::*;

fn maybe_split<'brand, 'arena, V>(
    dcel: &mut Dcel<'brand, 'arena, V>,
    old_shell: ptr!(Shell),
    inside_edge: ptr!(Edge),
    outside_edge: ptr!(Edge),
) -> Option<own!(Shell)> {
    let mut seen_vertices = HashMap::new();
    let mut seen_edges = HashMap::new();
    let mut seen_faces = HashMap::new();
    let mut edge_stack = Vec::new();
    let mut face_stack = Vec::<ptr!(Face)>::new();

    let mut add_edge = |edge: ptr!(Edge), edge_stack: &mut Vec<ptr!(Edge)>| {
        if edge.eq(inside_edge, dcel) {
            return None;
        }

        if seen_edges.insert(edge.id(dcel), edge).is_none() {
            edge_stack.push(edge);
        }

        Some(())
    };

    add_edge(outside_edge, &mut edge_stack)?;

    loop {
        let Some(edge) = edge_stack.pop() else {
            let Some(face) = face_stack.pop() else {
                break;
            };

            for loop_ in
                std::iter::once(face.lens(dcel).outer_loop()).chain(face.iter_inner_loops(dcel))
            {
                add_edge(loop_.half_edges().edge().item, &mut edge_stack)?;
            }

            continue;
        };

        for h in edge.half_edges(dcel) {
            let face = h.loop_(dcel).face(dcel);
            if seen_faces.insert(face.id(dcel), face).is_none() {
                face_stack.push(face);
            }

            let origin = h.origin(dcel);
            seen_vertices.insert(origin.id(dcel), origin);

            add_edge(h.next(dcel).edge(dcel), &mut edge_stack)?;
        }
    }

    let new_shell = old_shell.body(dcel).add_new_shell(dcel);

    for &v in seen_vertices.values() {
        old_shell.remove_vertex(v, dcel);
        new_shell.add_vertex(v, dcel);
    }
    for &e in seen_edges.values() {
        old_shell.remove_edge(e, dcel);
        new_shell.add_edge(e, dcel);
    }
    for &f in seen_faces.values() {
        old_shell.remove_face(f, dcel);
        new_shell.add_face(f, dcel);
    }

    Some(new_shell)
}

pub struct Mpkh<'brand, 'arena, V> {
    pub loop_: ptr!(Loop),
}

impl<'brand, 'arena, V> Mpkh<'brand, 'arena, V> {
    pub fn new(loop_: ptr!(Loop)) -> Self {
        Self { loop_ }
    }
}

#[derive(Debug, Error)]
pub enum MpkhError {
    #[error("loop is not an inner loop")]
    LoopIsOuter,
}

impl<'brand, 'arena, V> Operator<'brand, 'arena, V> for Mpkh<'brand, 'arena, V> {
    type Inverse = Kpmh<'brand, 'arena, V>;
    type Error = MpkhError;
    type Check = ();

    fn check(&self, dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error> {
        use MpkhError::*;

        or_err(!self.loop_.is_outer(dcel), LoopIsOuter)?;

        Ok(())
    }

    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>> {
        try_check!(self, dcel);

        let old_face = self.loop_.face(dcel);
        let old_shell = old_face.shell(dcel);

        let new_face = old_shell.add_new_face(dcel);

        old_face.remove_inner_loop(self.loop_, dcel);
        new_face.set_outer_loop(self.loop_, dcel);
        self.loop_.set_face(*new_face, dcel);

        let new_shell = maybe_split(
            dcel,
            old_shell,
            old_face.outer_loop(dcel).half_edges(dcel).edge(dcel),
            self.loop_.half_edges(dcel).edge(dcel),
        );

        Ok(Kpmh {
            new_shell,
            old_face,
            new_face,
        })
    }
}

pub struct Kpmh<'brand, 'arena, V> {
    pub new_shell: Option<own!(Shell)>,
    pub old_face: ptr!(Face),
    pub new_face: own!(Face),
}

#[derive(Error, Debug)]
pub enum KpmhError {
    #[error("face does not match shell")]
    FaceShellMismatch,
    #[error("shell passed in, but faces are already part of same shell")]
    CannotMerge,
    #[error("no shell passed in but faces are part of different shells")]
    ShouldMerge,
    #[error("face has inner loops")]
    HasInnerLoops,
    #[error("shells are part of different body")]
    BodyMismatch,
}

impl<'brand, 'arena, V> Kpmh<'brand, 'arena, V> {
    pub fn new(new_shell: Option<own!(Shell)>, old_face: ptr!(Face), new_face: own!(Face)) -> Self {
        Self {
            new_shell,
            old_face,
            new_face,
        }
    }
}

impl<'brand, 'arena, V> Operator<'brand, 'arena, V> for Kpmh<'brand, 'arena, V> {
    type Inverse = Mpkh<'brand, 'arena, V>;
    type Error = KpmhError;
    type Check = ();

    fn check(&self, dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error> {
        use KpmhError::*;

        let Kpmh {
            new_shell,
            old_face,
            new_face,
        } = self;

        let old_shell = old_face.shell(dcel);
        let needs_merge = !new_face.shell(dcel).eq(old_shell, dcel);

        if let Some(new_shell) = new_shell {
            or_err(
                new_face.shell(dcel).eq(**new_shell, dcel),
                FaceShellMismatch,
            )?;
            or_err(needs_merge, CannotMerge)?;
        } else {
            or_err(!needs_merge, ShouldMerge)?;
        }

        or_err(new_face.maybe_inner_loops(dcel).is_none(), HasInnerLoops)?;

        Ok(())
    }

    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>> {
        try_check!(self, dcel);

        let Kpmh {
            new_shell,
            old_face,
            new_face,
        } = self;

        let loop_ = new_face.outer_loop(dcel);
        old_face.add_inner_loop(loop_, dcel);

        new_face.shell(dcel).remove_face(*new_face, dcel);
        new_face.free(dcel);

        if let Some(new_shell) = new_shell {
            let old_shell = old_face.shell(dcel);
            new_shell.iter_mut_vertices(dcel, |x, dcel| old_shell.add_vertex(x, dcel));
            new_shell.iter_mut_edges(dcel, |x, dcel| old_shell.add_edge(x, dcel));
            new_shell.iter_mut_faces(dcel, |x, dcel| old_shell.add_face(x, dcel));

            new_shell.body(dcel).remove_shell(*new_shell, dcel);
            new_shell.free(dcel);
        }

        Ok(Mpkh { loop_ })
    }
}
