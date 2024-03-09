// Make Split Edge Vertex

use crate::*;

pub struct Msev<'brand, 'arena, V> {
    pub shell: ptr!(Shell),
    pub vertex: ptr!(Vertex),
    pub loops: [ptr!(Loop); 2],
    pub data: V,
}

impl<'brand, 'arena, V> Msev<'brand, 'arena, V> {
    pub fn new(shell: ptr!(Shell), vertex: ptr!(Vertex), loops: [ptr!(Loop); 2], data: V) -> Self {
        Self {
            shell,
            vertex,
            loops,
            data,
        }
    }
}

#[derive(Debug, Error)]
pub enum MsevError {
    #[error("vertex is not part of loop")]
    VertexLoopMismatch,
}

impl<'brand, 'arena, V> Operator<'brand, 'arena, V> for Msev<'brand, 'arena, V> {
    type Inverse = Ksev<'brand, 'arena, V>;
    type Error = MsevError;
    type Check = [ptr!(HalfEdge); 2];

    fn check(&self, dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error> {
        use MsevError::*;

        let a = self
            .vertex
            .find_outgoing(self.loops[0], dcel)
            .ok_or(VertexLoopMismatch)?;
        let b = self
            .vertex
            .find_outgoing(self.loops[1], dcel)
            .ok_or(VertexLoopMismatch)?;

        Ok([a, b])
    }

    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>> {
        let [a2, b0] = try_check!(self, dcel);
        let a0 = a2.prev(dcel);
        let b2 = b0.prev(dcel);

        let (edge, [a1, b1]) = Edge::create(self.shell, dcel);
        let v = self.shell.add_new_vertex(self.data, dcel);

        a1.update_origin(self.vertex, dcel);
        b2.twin(dcel).update_origin(*v, dcel);
        b1.update_origin(*v, dcel);
        a2.update_origin(*v, dcel);

        dcel.follow(a0, a1);
        dcel.follow(a1, a2);

        dcel.follow(b2, b1);
        dcel.follow(b1, b0);

        a1.set_loop_(self.loops[0], dcel);
        b1.set_loop_(self.loops[1], dcel);

        Ok(Ksev {
            shell: self.shell,
            loops: self.loops,
            old_vertex: self.vertex,
            new_vertex: v,
            edge,
        })
    }
}

pub struct Ksev<'brand, 'arena, V> {
    pub shell: ptr!(Shell),
    pub loops: [ptr!(Loop); 2],
    pub old_vertex: ptr!(Vertex),
    pub new_vertex: own!(Vertex),
    pub edge: own!(Edge),
}

impl<'brand, 'arena, V> Ksev<'brand, 'arena, V> {
    pub fn new(
        shell: ptr!(Shell),
        loops: [ptr!(Loop); 2],
        old_vertex: ptr!(Vertex),
        new_vertex: own!(Vertex),
        edge: own!(Edge),
    ) -> Self {
        Self {
            shell,
            loops,
            old_vertex,
            new_vertex,
            edge,
        }
    }
}

#[derive(Debug, Error)]
pub enum KsevError {
    #[error("edge does not match vertices")]
    EdgeVertexMismatch,
    #[error("edge does not match loops")]
    EdgeLoopMismatch,
}

impl<'brand, 'arena, V> Operator<'brand, 'arena, V> for Ksev<'brand, 'arena, V> {
    type Inverse = Msev<'brand, 'arena, V>;
    type Error = KsevError;
    type Check = [ptr!(HalfEdge); 2];

    fn check(&self, dcel: &Dcel<'brand, 'arena, V>) -> Result<Self::Check, Self::Error> {
        use KsevError::*;

        let [mut a, mut b] = self.edge.lens(dcel).half_edges();
        if a.origin().eq(*self.new_vertex) {
            [a, b] = [b, a];
        }

        or_err(
            a.origin().eq(self.old_vertex) && b.origin().eq(*self.new_vertex),
            EdgeVertexMismatch,
        )?;

        or_err(
            (a.loop_().eq(self.loops[0]) && b.loop_().eq(self.loops[1]))
                || (a.loop_().eq(self.loops[1]) && b.loop_().eq(self.loops[0])),
            EdgeLoopMismatch,
        )?;

        Ok([a.item, b.item])
    }

    fn apply(
        self,
        dcel: &mut Dcel<'brand, 'arena, V>,
    ) -> Result<Self::Inverse, OperatorErr<Self, Self::Error>> {
        let [a1, b1] = try_check!(self, dcel);

        let Ksev {
            shell,
            old_vertex,
            new_vertex,
            edge,
            ..
        } = self;

        let loops = [a1.loop_(dcel), b1.loop_(dcel)];

        let a0 = a1.prev(dcel);
        let a2 = a1.next(dcel);

        let b0 = b1.next(dcel);
        let b2 = b1.prev(dcel);

        dcel.follow(a0, a2);
        dcel.follow(b2, b0);

        a2.update_origin(old_vertex, dcel);
        b2.twin(dcel).update_origin(old_vertex, dcel);

        loops[0].set_half_edges(a0, dcel);
        loops[1].set_half_edges(b0, dcel);

        edge.destroy(dcel);
        let data = new_vertex.destroy(dcel);

        Ok(Msev {
            shell,
            vertex: old_vertex,
            loops,
            data,
        })
    }
}
