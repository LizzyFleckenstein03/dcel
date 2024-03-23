use cairo::{Context, SvgSurface};
use dcel::Dcel;
use enumset::EnumSet;
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
            EnumSet::all(),
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
        /*write!(
            &mut std::fs::File::create(name).unwrap(),
            "{}",
            DisplayFn(|f: &mut fmt::Formatter<'_>| dcel_write_dot(
                dcel,
                |v| v.1.map(|x| x as _),
                |v, f| write!(f, "{}", v.0),
                f,
                DcelDotOptions {
                    prev: false,
                    next: true,
                    twin: true,
                }
            ))
        )
        .unwrap();*/
    };

    Dcel::new(|mut dcel| {
        let body = dcel.new_body();
        // Mevvlfs(a, [w, n], l, f, s)

        //let op = dcel.mevvlfs(*body, [("W", [-4, 0]), ("N", [0, 4])]);
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

    /*
    dbg!(ctx.clip_extents().unwrap());

    let text = "meow meow meow mew mew mrrrp";
    let x = 250.0;
    let y = 250.0;

    let ext = ctx.text_extents(text).unwrap();

    ctx.move_to(
        x - ext.width() / 2.0,
        y - ext.y_bearing() - ext.height() / 2.0,
    );
    ctx.show_text(text).unwrap();

    ctx.set_line_width(1.0);
    {
        let mat = ctx.matrix();

        ctx.translate(x, y);
        ctx.scale(
            (ext.width() + ctx.line_width()) / 2.0f64.sqrt(),
            (ext.height() + ctx.line_width()) / 2.0f64.sqrt(),
        );
        ctx.translate(-x, -y);
        ctx.new_path();
        ctx.arc(x, y, 1.0, 0.0, 2.0 * std::f64::consts::PI);
        ctx.set_matrix(mat);
    }

    ctx.stroke().unwrap();*/

    /*ctx.rectangle(
        x - (ext.width() + ctx.line_width()) / 2.0,
        y - (ext.height() + ctx.line_width()) / 2.0,
        ext.width() + ctx.line_width(),
        ext.height() + ctx.line_width(),
    );
    ctx.stroke().unwrap();*/

    /*ctx.rectangle(
        x - ext.width() / 2.0,
        y - ext.height() / 2.0,
        ext.width(),
        ext.height(),
    );*/

    //cairo_move_to (cr, i + 0.5 - te.x_bearing - te.width / 2,
    //            0.5 - te.y_bearing - te.height / 2);
}
