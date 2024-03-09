use crate::*;

#[test]
fn mev_cycle() {
    Dcel::<u32>::new(|mut dcel| {
        let body = dcel.new_body();
        let op = dcel.mevvlfs(*body, [0, 1]).unwrap();
        let op2 = dcel.mev(*op.shell, *op.loop_, *op.vertices[1], 2);
        let op3 = dcel.mev(*op.shell, *op.loop_, *op2.new_vertex, 3);
        dcel.melf(*op.shell, [*op3.new_vertex, *op.vertices[0]], *op.loop_);

        let mut vertices = op
            .loop_
            .iter_half_edges(&dcel)
            .map(|x| *x.origin().data())
            .peekable();

        assert!((0..4)
            .cycle()
            .skip(*vertices.peek().unwrap() as _)
            .take(4)
            .eq(vertices));
    })
}

#[test]
fn kemh_mekh() {
    #[derive(Copy, Clone, Debug, Eq, PartialEq)]
    enum Vert {
        Inner(u8),
        Outer(u8),
    }
    use Vert::*;

    impl Vert {
        fn flip(self) -> Self {
            match self {
                Outer(x) => Inner(x),
                Inner(x) => Outer(x),
            }
        }

        fn is_outer(self) -> bool {
            match self {
                Outer(_) => true,
                Inner(_) => false,
            }
        }

        fn either(self) -> u8 {
            match self {
                Outer(x) => x,
                Inner(x) => x,
            }
        }
    }

    Dcel::<Vert>::new(|mut dcel| {
        let body = dcel.new_body();
        let Kevvlfs {
            shell,
            loop_: loop_0,
            vertices: [inner_0, inner_1],
            ..
        } = dcel.mevvlfs(*body, [Inner(0), Inner(1)]).unwrap();

        let inner_2 = dcel.mev(*shell, *loop_0, *inner_1, Inner(2)).new_vertex;
        let mut outer_loop = dcel.melf(*shell, [*inner_0, *inner_2], *loop_0).new_loop;

        let Mev {
            new_vertex: outer_0,
            edge,
            ..
        } = dcel.mev(*shell, *outer_loop, *inner_0, Outer(0));

        let outer_1 = dcel.mev(*shell, *outer_loop, *outer_0, Outer(1)).new_vertex;
        let outer_2 = dcel.mev(*shell, *outer_loop, *outer_1, Outer(2)).new_vertex;

        let loop_2 = dcel
            .melf(*shell, [*outer_0, *outer_2], *outer_loop)
            .new_loop;
        if edge.lens(&dcel).half_edges()[0].loop_().eq(*loop_2) {
            outer_loop = loop_2;
        }

        let mut kemh = Kemh::new(*shell, edge, *outer_loop, *inner_0);

        for _ in 0..3 {
            let mut seen = 0;
            let mut last = None::<Vert>;

            for v in outer_loop
                .iter_half_edges(&dcel)
                .map(|x| *x.origin().data())
            {
                let mut s = 1u8 << v.either();
                if v.is_outer() {
                    s <<= 4;
                }
                if seen & s == 0 {
                    seen |= s;
                } else {
                    assert_eq!(v.either(), 0);
                    assert_eq!(seen & (s << 3), 0);
                    seen |= s << 3;
                }

                if let Some(last) = last {
                    if v.either() == 0 {
                        assert!(
                            last == v.flip()
                                || (last.is_outer() == v.is_outer() && last.either() != 0)
                        );
                    } else {
                        assert_eq!(last.is_outer(), v.is_outer());
                    }
                }

                last = Some(v);
            }

            assert_eq!(seen, 255);

            let mekh = kemh.apply(&mut dcel).unwrap();

            for (loop_, outer) in [(*outer_loop, true), (*mekh.hole_loop, false)] {
                let mut seen = 0;
                for v in loop_.iter_half_edges(&dcel).map(|x| *x.origin().data()) {
                    let s = 1 << v.either();
                    assert_eq!(v.is_outer(), outer);
                    assert_eq!(seen & s, 0);
                    seen |= s;
                }
                assert_eq!(seen, 7);
            }

            kemh = mekh.apply(&mut dcel).unwrap();
        }
    })
}

#[test]
fn msev_ksev() {
    Dcel::<u32>::new(|mut dcel| {
        let body = dcel.new_body();

        let Kevvlfs {
            shell,
            loop_: mut loop_0,
            vertices: [out_0, out_1],
            ..
        } = dcel.mevvlfs(*body, [0, 1]).unwrap();

        let out_2 = dcel.mev(*shell, *loop_0, *out_1, 2).new_vertex;
        let out_3 = dcel.mev(*shell, *loop_0, *out_2, 3).new_vertex;
        dcel.melf(*shell, [*out_0, *out_3], *loop_0);

        let Melf {
            new_loop: mut loop_2,
            edge,
            ..
        } = dcel.melf(*shell, [*out_0, *out_2], *loop_0);
        if out_1.find_outgoing(*loop_0, &dcel).is_none() {
            [loop_0, loop_2] = [loop_2, loop_0];
        }

        let in_0 = dcel.mve(*shell, *edge, 4).vertex;

        let mut loop_1 = dcel.melf(*shell, [*out_1, *in_0], *loop_0).new_loop;
        if out_0.find_outgoing(*loop_0, &dcel).is_none() {
            [loop_0, loop_1] = [loop_1, loop_0];
        }

        let mut loop_3 = dcel.melf(*shell, [*out_3, *in_0], *loop_2).new_loop;
        if out_2.find_outgoing(*loop_2, &dcel).is_none() {
            [loop_2, loop_3] = [loop_3, loop_2];
        }

        fn test_integrity<'brand, 'arena>(
            debug: &'static str,
            dcel: &Dcel<'brand, 'arena, u32>,
            loops: &[(ptr_t!(Loop<'brand, 'arena, u32>), &[u32])],
        ) {
            for (i, (l, want)) in loops.iter().enumerate() {
                let mut got = l
                    .iter_half_edges(dcel)
                    .map(|x| *x.origin().data())
                    .collect::<Vec<_>>();

                assert!(
                    (0..want.len()).any(|_| {
                        let x = got.remove(0);
                        got.push(x);
                        want == &got
                    }),
                    "{debug} loop = {i} want = {want:?} got = {got:?}"
                );
            }
        }

        let mut msev = Msev::new(*shell, *in_0, [*loop_0, *loop_2], 5);

        for i in 0..4 {
            test_integrity(
                "before msev:",
                &dcel,
                &[
                    (*loop_0, &[0, 4, 1]),
                    (*loop_1, &[1, 4, 2]),
                    (*loop_2, &[2, 4, 3]),
                    (*loop_3, &[3, 4, 0]),
                ],
            );

            let mut ksev = msev.apply(&mut dcel).unwrap();

            if i % 2 == 0 {
                // ksev should be able to fix the order of the loops
                [ksev.loops[0], ksev.loops[1]] = [ksev.loops[1], ksev.loops[0]];
            }

            test_integrity(
                "after msev:",
                &dcel,
                &[
                    (*loop_0, &[0, 4, 5, 1]),
                    (*loop_1, &[1, 5, 2]),
                    (*loop_2, &[2, 5, 4, 3]),
                    (*loop_3, &[3, 4, 0]),
                ],
            );

            msev = ksev.apply(&mut dcel).unwrap();
        }
    })
}
