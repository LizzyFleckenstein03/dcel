use crate::*;

struct VertAttr<L, F, T, V> {
    func: F,
    items: Vec<T>,
    local: HashMap<usize, Option<usize>>,
    // global: HashMap<T, usize>,
    marker: std::marker::PhantomData<(V, L)>,
}

impl<L, F, T, V> VertAttr<L, F, T, V>
where
    F: FnMut(L, &V) -> Option<T>,
    T: Copy, // + Hash + Eq,
{
    fn new(func: F) -> Self {
        Self {
            func,
            items: Vec::new(),
            local: HashMap::new(),
            // global: HashMap::new(),
            marker: std::marker::PhantomData,
        }
    }

    fn add(&mut self, local: L, vert_id: usize, vert_data: &V) -> Option<usize> {
        *self.local.entry(vert_id).or_insert_with(|| {
            let item = (self.func)(local, vert_data);

            //*self.global.entry(item).or_insert_with(|| {
            item.map(|item| {
                self.items.push(item);
                self.items.len()
            })
            //})
        })
    }
}

pub struct ObjExport<'tok, 'brand, 'arena, V, W, VPos, VTex, VNorm> {
    writer: &'tok mut W,
    dcel: &'tok Dcel<'brand, 'arena, V>,
    vertex_pos: VPos,
    pos_ids: Vec<Option<usize>>,
    textures: VertAttr<lens!(Face), VTex, (f64, Option<(f64, Option<f64>)>), V>,
    normals: VertAttr<lens!(Face), VNorm, (f64, f64, f64), V>,
}

impl<'tok, 'brand, 'arena, V, W, VPos, VTex, VNorm>
    ObjExport<'tok, 'brand, 'arena, V, W, VPos, VTex, VNorm>
where
    W: std::io::Write,
    VPos: FnMut(&V) -> (f64, f64, f64, Option<f64>),
    VTex: FnMut(lens!(Face), &V) -> Option<(f64, Option<(f64, Option<f64>)>)>,
    VNorm: FnMut(lens!(Face), &V) -> Option<(f64, f64, f64)>,
{
    pub fn export(
        writer: &'tok mut W,
        dcel: &'tok Dcel<'brand, 'arena, V>,
        vertex_pos: VPos,
        vertex_texture: VTex,
        vertex_normal: VNorm,
    ) -> std::io::Result<()> {
        Self {
            writer,
            dcel,
            vertex_pos,
            pos_ids: Vec::new(),
            textures: VertAttr::new(vertex_texture),
            normals: VertAttr::new(vertex_normal),
        }
        .write()
    }

    fn write(&mut self) -> std::io::Result<()> {
        let mut next_id = 1;
        for shell in self.dcel.iter_bodies().flat_map(Lens::iter_shells) {
            for vertex in shell.iter_vertices() {
                let v_id = vertex.id();
                if v_id <= self.pos_ids.len() {
                    self.pos_ids.resize(v_id + 1, None);
                }
                self.pos_ids.insert(v_id, Some(next_id));
                next_id += 1;

                let (x, y, z, w) = (self.vertex_pos)(vertex.data());
                write!(self.writer, "v {x} {y} {z}")?;
                if let Some(w) = w {
                    write!(self.writer, " {w}")?;
                }
                writeln!(self.writer)?;
            }

            for face in shell.iter_faces() {
                write!(self.writer, "f")?;

                for inner in face.iter_inner_loops() {
                    self.write_vertex(face, face.outer_loop().half_edges())?;
                    for h in inner.iter_half_edges() {
                        self.write_vertex(face, h)?;
                    }
                }

                for h in face.outer_loop().iter_half_edges() {
                    self.write_vertex(face, h)?;
                }

                self.textures.local.clear();
                self.normals.local.clear();

                writeln!(self.writer)?;
            }
        }

        for (u, vw) in &self.textures.items {
            write!(self.writer, "vt {u}")?;
            if let Some((v, w)) = vw {
                write!(self.writer, " {v}")?;
                if let Some(w) = w {
                    write!(self.writer, " {w}")?;
                }
            }
            writeln!(self.writer)?;
        }

        for (x, y, z) in &self.normals.items {
            writeln!(self.writer, "vn {x} {y} {z}")?;
        }

        Ok(())
    }

    fn write_vertex(
        &mut self,
        face: lens!(Face),
        half_edge: lens!(HalfEdge),
    ) -> std::io::Result<()> {
        let vert = half_edge.origin();
        write!(self.writer, " {}", self.pos_ids[vert.id()].unwrap())?;

        let t = self.textures.add(face, vert.id(), vert.data());
        let n = self.normals.add(face, vert.id(), vert.data());

        if t.is_some() || n.is_some() {
            write!(self.writer, "/")?;
        }

        if let Some(t) = t {
            write!(self.writer, "{t}")?;
        }

        if let Some(n) = n {
            write!(self.writer, "/{n}")?;
        }

        Ok(())
    }
}
