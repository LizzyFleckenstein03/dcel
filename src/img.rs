use crate::*;

pub use cairo;

use cairo::Context;
use std::borrow::{Borrow, Cow};

pub fn write_img<V>(
    dcel: &Dcel<V>,
    ctx: &Context,
    pos: impl Fn(&V) -> [f64; 2],
    label: impl Fn(&V) -> Cow<str>,
    font_size: f64,
) -> Result<(), cairo::Error> {
    ctx.set_font_size(font_size);
    for shell in dcel.iter_bodies().flat_map(Lens::iter_shells) {
        for hedges in shell
            .iter_edges()
            .map(|x| x.half_edges())
            .flat_map(|[a, b]| [[a, b], [b, a]])
        {
            let mut points = hedges.map(|h| pos(h.origin().data()));

            let mut dir = [points[1][0] - points[0][0], points[1][1] - points[0][1]];
            let scale = ctx.line_width() / (dir[0] * dir[0] + dir[1] * dir[1]).sqrt();
            dir = [dir[0] * scale, dir[1] * scale];
            let prp = [-dir[1], dir[0]];
            points[0] = [points[0][0] + prp[0] * 2.0, points[0][1] + prp[1] * 2.0];
            points[1] = [points[1][0] + prp[0] * 2.0, points[1][1] + prp[1] * 2.0];

            ctx.move_to(points[0][0], points[0][1]);
            ctx.line_to(points[1][0], points[1][1]);
            ctx.stroke()?;

            let arrow_pos = 1.2;
            let arrow = [
                (points[0][0] * (2.0 - arrow_pos) + points[1][0] * arrow_pos) / 2.0,
                (points[0][1] * (2.0 - arrow_pos) + points[1][1] * arrow_pos) / 2.0,
            ];
            let arrow_scale = 3.0;

            ctx.move_to(arrow[0], arrow[1]);
            ctx.rel_line_to(
                (-dir[0] + prp[0]) * arrow_scale,
                (-dir[1] + prp[1]) * arrow_scale,
            );
            ctx.rel_line_to(-prp[0] * 2.0 * arrow_scale, -prp[1] * 2.0 * arrow_scale);
            ctx.line_to(arrow[0], arrow[1]);
            ctx.close_path();
            ctx.fill()?;

            // edge ids
            let num_pos = [arrow[0] + prp[0] * 4.0, arrow[1] + prp[1] * 4.0];
            let num_text = hedges[0].id().to_string();

            ctx.set_font_size(font_size / 2.0);
            let ext = ctx.text_extents(&num_text)?;
            ctx.move_to(
                num_pos[0] - ext.x_advance() / 2.0,
                num_pos[1] - ext.y_bearing() - ext.height() / 2.0,
            );
            ctx.show_text(&num_text)?;
            ctx.set_font_size(font_size);
        }

        for vertex in shell.iter_vertices() {
            let v = vertex.data();
            let [x, y] = pos(v);
            let text = label(v);
            let ext = ctx.text_extents(text.borrow())?;

            let mat = ctx.matrix();
            ctx.translate(x, y);
            ctx.scale(
                (ext.x_advance() + ctx.line_width()) / 2.0f64.sqrt(),
                (ext.height() + ctx.line_width()) / 2.0f64.sqrt(),
            );
            ctx.translate(-x, -y);
            ctx.new_path();
            ctx.arc(x, y, 1.0, 0.0, 2.0 * std::f64::consts::PI);
            ctx.set_matrix(mat);

            let path = ctx.copy_path()?;

            ctx.set_source_rgb(1.0, 1.0, 1.0);
            ctx.fill()?;

            ctx.append_path(&path);
            ctx.set_source_rgb(0.0, 0.0, 0.0);
            ctx.stroke()?;

            ctx.move_to(
                x - ext.x_advance() / 2.0,
                y - ext.y_bearing() - ext.height() / 2.0,
            );
            ctx.show_text(text.borrow())?;
        }
    }

    Ok(())
}
