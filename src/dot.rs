use crate::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DcelDotOptions {
    pub twin: bool,
    pub next: bool,
    pub prev: bool,
}

impl DcelDotOptions {
    pub fn none() -> Self {
        Self {
            twin: false,
            next: false,
            prev: false,
        }
    }

    pub fn all() -> Self {
        Self {
            twin: true,
            next: true,
            prev: true,
        }
    }
}

pub fn dcel_write_dot<V>(
    dcel: &Dcel<V>,
    pos: impl Fn(&V) -> [f64; 2],
    name: impl Fn(&V, &mut Formatter) -> fmt::Result,
    f: &mut Formatter,
    opt: DcelDotOptions,
) -> fmt::Result {
    writeln!(f, "digraph DCEL {{")?;
    writeln!(f, "node [shape = circle]")?;
    //writeln!(f, "nodesep = 1")?;

    for shell in dcel.iter_bodies().flat_map(Lens::iter_shells) {
        for vertex in shell.iter_vertices() {
            let p = pos(vertex.data());

            writeln!(
                f,
                "vertex_{} [label=\"{}\", pos=\"{},{}!\"]",
                vertex.id(),
                DisplayFn(|f| name(vertex.data(), f)),
                p[0],
                p[1]
            )?;
        }

        for hedges in shell
            .iter_edges()
            .map(|x| x.half_edges())
            .flat_map(|[he1, he2]| [[he1, he2], [he2, he1]])
        {
            let ids = hedges.map(Lens::id);
            let vertices = hedges.map(|h| h.origin());
            let points = vertices.map(|v| pos(v.data()));

            let mut diff = [points[1][1] - points[0][1], points[1][0] - points[0][0]];

            // let len = (diff[0] * diff[0] + diff[1] * diff[1]).sqrt();
            diff[0] *= -0.075;
            diff[1] *= 0.075;

            let mid = [
                (points[1][0] + points[0][0]) / 2.0 + diff[0],
                (points[1][1] + points[0][1]) / 2.0 + diff[1],
            ];

            writeln!(
                f,
                "half_edge_{} [pos=\"{},{}!\", shape=point, width=0.01, height=0.01]",
                ids[0], mid[0], mid[1]
            )?;
            writeln!(
                f,
                "vertex_{} -> half_edge_{} [arrowhead=none]",
                vertices[0].id(),
                ids[0]
            )?;
            writeln!(
                f,
                "half_edge_{} -> vertex_{} [label=\"{}\"]",
                ids[0],
                vertices[1].id(),
                ids[0]
            )?;

            if opt.twin {
                writeln!(
                    f,
                    "half_edge_{} -> half_edge_{} [color=\"red\"]",
                    ids[0], ids[1]
                )?;
            }

            if opt.next {
                writeln!(
                    f,
                    "half_edge_{} -> half_edge_{} [color=\"green\"]",
                    ids[0],
                    hedges[0].next().id(),
                )?;
            }

            if opt.prev {
                writeln!(
                    f,
                    "half_edge_{} -> half_edge_{} [color=\"blue\"]",
                    ids[0],
                    hedges[0].prev().id(),
                )?;
            }
        }
    }

    writeln!(f, "}}")
}
