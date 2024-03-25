use dcel::{ptr_t, Dcel, ObjExport, ObjImport, Shell};
use std::array::from_fn;
use std::collections::HashMap;

fn avg(iter: impl Iterator<Item = [f32; 3]>) -> Option<[f32; 3]> {
    let mut count = 0usize;
    let mut accum = [0.0; 3];

    for x in iter {
        count += 1;
        accum = from_fn(|i| accum[i] + x[i])
    }

    (count > 0).then(|| accum.map(|x| x / (count as f32)))
}

fn catmull_clark_subdivision<'brand, 'arena>(
    dcel: &mut Dcel<'brand, 'arena, [f32; 3]>,
    shell: ptr_t!(Shell<'brand, 'arena, [f32; 3]>),
) {
    let face_points = shell
        .iter_faces(dcel)
        .map(|f| {
            (
                f.id(),
                avg(f.outer_loop().iter_half_edges().map(|x| *x.origin().data())).unwrap(),
            )
        })
        .collect::<HashMap<_, _>>();

    let vert_points = shell
        .iter_vertices(dcel)
        .map(|vert| {
            let p = vert.data();
            let mut n = 0.0;
            let mut f = [0.0; 3];
            let mut r = [0.0; 3];

            for h in vert.iter_outgoing() {
                let fp = face_points[&h.loop_().face().id()];
                let op = *h.origin().data();
                let tp = *h.target().data();

                f = from_fn(|i| f[i] + fp[i]);
                r = from_fn(|i| r[i] + op[i] + tp[i]);

                n += 1.0;
            }

            (
                vert.id(),
                (
                    vert.item,
                    from_fn(|i| (f[i] / n + r[i] / n + (n - 3.0) * p[i]) / n),
                ),
            )
        })
        .collect::<HashMap<_, _>>();

    for edge in shell.iter_edges(dcel).map(|x| x.item).collect::<Vec<_>>() {
        let data = avg(edge
            .lens(dcel)
            .half_edges()
            .into_iter()
            .flat_map(|h| [face_points[&h.loop_().face().id()], *h.origin().data()]))
        .unwrap();

        dcel.mve(edge, data).unwrap();
    }

    for &(vert, data) in vert_points.values() {
        *vert.mut_data(dcel) = data;
    }

    for face in shell.iter_faces(dcel).map(|x| x.item).collect::<Vec<_>>() {
        let loop_ = face.outer_loop(dcel);

        let mut verts = loop_
            .iter_half_edges(dcel)
            .skip_while(|h| vert_points.contains_key(&h.origin().id()))
            .map(|h| h.origin().item)
            .step_by(2)
            .collect::<Vec<_>>()
            .into_iter();

        let inner = *dcel
            .mev(loop_, verts.next().unwrap(), face_points[&face.id(dcel)])
            .unwrap()
            .vertex;

        verts.fold([loop_; 2], |loops, vert| {
            let l = loops
                .into_iter()
                .find(|&l| vert.find_outgoing(l, dcel).is_some())
                .unwrap();
            [l, *dcel.melf([vert, inner], l).unwrap().loop_]
        });
    }
}

fn main() {
    Dcel::new(|mut dcel| {
        let body = ObjImport::import(
            &mut dcel,
            &obj::raw::object::parse_obj(&mut std::io::BufReader::new(
                std::fs::File::open("bunny.obj").unwrap(),
            ))
            .unwrap(),
            |(x, y, z, _)| [x, y, z],
        )
        .unwrap();

        let shell = body.iter_shells(&dcel).next().unwrap().item;

        for i in 0..5 {
            println!("subdivision level {i}...");
            catmull_clark_subdivision(&mut dcel, shell);
        }

        println!("exporting...");
        ObjExport::export(
            &mut std::io::BufWriter::new(std::fs::File::create("bunny2.obj").unwrap()),
            &dcel,
            |&[x, y, z]| (x as _, y as _, z as _, None),
            |_, _| None,
            |_, _| None,
        )
        .unwrap();
    });
}
