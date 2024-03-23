use dcel::{Dcel, Kevvlfs, ObjExport};

fn main() {
    Dcel::new(|mut dcel| {
        let body = dcel.new_body();

        let [d1, d2, d3, d4] = [
            ((8.0f64 / 9.0).sqrt(), 0.0, -1.0 / 3.0),
            (-(2.0f64 / 9.0).sqrt(), (2.0f64 / 3.0).sqrt(), -1.0 / 3.0),
            (-(2.0f64 / 9.0).sqrt(), -(2.0f64 / 3.0).sqrt(), -1.0 / 3.0),
            (0.0, 0.0, 1.0),
        ];

        let Kevvlfs {
            vertices: [v1, v2],
            loop_: l1,
            ..
        } = dcel.mevvlfs(*body, [d1, d2]).unwrap();
        let v3 = dcel.mev(*l1, *v2, d3).unwrap().vertex;
        let l2 = dcel.melf([*v1, *v3], *l1).unwrap().loop_;
        let v4 = dcel.mev(*l2, *v1, d4).unwrap().vertex;
        let mut l3 = dcel.melf([*v4, *v2], *l2).unwrap().loop_;
        if v3.find_outgoing(*l3, &dcel).is_none() {
            l3 = l2;
        }
        let _l4 = dcel.melf([*v4, *v3], *l3).unwrap().loop_;

        ObjExport::export(
            &mut std::fs::File::create("pyramid.obj").unwrap(),
            &dcel,
            |&(x, y, z)| (x, y, z, None),
            |_, _| None,
            |_, _| None,
        )
        .unwrap();
    });
}
