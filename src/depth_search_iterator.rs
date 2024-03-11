use crate::*;

pub(crate) struct DepthSearchIterator<'tok, 'brand, 'arena, V> {
    token: &'tok GhostToken<'brand>,
    seen_vertices: Option<HashMap<usize, ptr!(Vertex)>>,
    seen_edges: HashMap<usize, ptr!(Edge)>,
    seen_faces: HashMap<usize, ptr!(Face)>,
    edge_stack: Vec<ptr!(Edge)>,
    face_stack: Vec<ptr!(Face)>,
}

impl<'tok, 'brand, 'arena, V> DepthSearchIterator<'tok, 'brand, 'arena, V> {
    pub(crate) fn new(
        edge: ptr!(Edge),
        collect_vertices: bool,
        token: &'tok impl ReflAsRef<GhostToken<'brand>>,
    ) -> Self {
        Self {
            token: token.as_ref(),
            seen_vertices: collect_vertices.then(|| HashMap::new()),
            seen_edges: HashMap::from([(edge.id(token), edge)]),
            seen_faces: HashMap::new(),
            edge_stack: Vec::from([edge]),
            face_stack: Vec::new(),
        }
    }

    fn add_edge(&mut self, edge: ptr!(Edge)) {
        if self.seen_edges.insert(edge.id(self.token), edge).is_none() {
            self.edge_stack.push(edge);
        }
    }

    pub(crate) fn collect_seen(
        edge: ptr!(Edge),
        token: &'tok impl ReflAsRef<GhostToken<'brand>>,
    ) -> (
        HashMap<usize, ptr!(Vertex)>,
        HashMap<usize, ptr!(Edge)>,
        HashMap<usize, ptr!(Face)>,
    )
    where
        'brand: 'tok,
    {
        let mut x = Self::new(edge, true, token);
        for _ in &mut x {}
        (x.seen_vertices.unwrap(), x.seen_edges, x.seen_faces)
    }
}

impl<'tok, 'brand, 'arena, V> Iterator for DepthSearchIterator<'tok, 'brand, 'arena, V> {
    type Item = ptr!(Edge);

    fn next(&mut self) -> Option<Self::Item> {
        let Some(edge) = self.edge_stack.pop() else {
            let face = self.face_stack.pop()?;

            for loop_ in std::iter::once(face.lens(self.token).outer_loop())
                .chain(face.iter_inner_loops(self.token))
            {
                self.add_edge(loop_.half_edges().edge().item);
            }

            return self.next();
        };

        for h in edge.half_edges(self.token) {
            let face = h.loop_(self.token).face(self.token);
            if self.seen_faces.insert(face.id(self.token), face).is_none() {
                self.face_stack.push(face);
            }

            let origin = h.origin(self.token);
            if let Some(seen_vertices) = self.seen_vertices.as_mut() {
                seen_vertices.insert(origin.id(self.token), origin);
            }

            self.add_edge(h.next(self.token).edge(self.token));
        }

        Some(edge)
    }
}
