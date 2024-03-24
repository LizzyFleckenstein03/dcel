use cairo::{Context, SvgSurface};
use dcel::Dcel;
use std::borrow::Cow;

fn main() {
    let show = |name, dcel: &Dcel<(&'static str, [i64; 2])>| {
        let width = 300.0;
        let height = width;

        let surf =
			//cairo::ImageSurface::create(cairo::Format::ARgb32, width as _, height as _).unwrap();
			SvgSurface::new(width, height, Some(name)).unwrap();
        let ctx = Context::new(surf).unwrap();
        ctx.set_line_width(1.0);

        dcel::write_img(
            &dcel,
            &ctx,
            |v| {
                [
                    v.1[0] as f64 * width / 3.0 + width / 2.0,
                    v.1[1] as f64 * height / 3.0 + height / 2.0,
                ]
            },
            |v| Cow::Borrowed(v.0),
            12.0,
        )
        .unwrap();

        /*ctx.target()
            .write_to_png(&mut std::fs::File::create(name).unwrap())
            .unwrap();
        */
    };

    Dcel::new(|mut dcel| {
        let body = dcel.new_body();

        let op = dcel
            .mevvlfs(*body, [("W", [-1, 0]), ("N", [0, 1])])
            .unwrap();
        let op2 = dcel.mev(*op.loop_, *op.vertices[1], ("E", [1, 0])).unwrap();
        let op3 = dcel.mev(*op.loop_, *op2.vertex, ("S", [0, -1])).unwrap();

        dcel.melf([*op3.vertex, *op.vertices[0]], *op.loop_)
            .unwrap();
        dcel.melf([*op.vertices[0], *op2.vertex], *op.loop_)
            .unwrap();

        show("cairo.svg", &dcel);
    });
}
