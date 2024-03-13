use crate::*;

#[test]
fn mev_cycle() {
    Dcel::<u32>::new(|mut dcel| {
        let body = dcel.new_body();
        let op = dcel.mevvlfs(*body, [0, 1]).unwrap();
        let op2 = dcel.mev(*op.loop_, *op.vertices[1], 2).unwrap();
        let op3 = dcel.mev(*op.loop_, *op2.vertex, 3).unwrap();
        dcel.melf(*op.shell, [*op3.vertex, *op.vertices[0]], *op.loop_);

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

/*

makes this shape:

   O      O
   |\    /|
   | \__/ |
   | O__O |
   | /  \ |
   |/    \|
   O      O

*/
fn make_hourglass<'brand, 'arena, V>(
    dcel: &mut Dcel<'brand, 'arena, V>,
    data: [V; 6],
) -> (own!(Shell), [own!(Loop); 3], own!(Edge), [own!(Vertex); 6]) {
    let [d0, d1, d2, d3, d4, d5] = data;

    let body = dcel.new_body();
    let Kevvlfs {
        shell,
        loop_: loop_0,
        vertices: [inner_0, inner_1],
        ..
    } = dcel.mevvlfs(*body, [d0, d1]).unwrap();

    let inner_2 = dcel.mev(*loop_0, *inner_1, d2).unwrap().vertex;
    let mut outer_loop = dcel.melf(*shell, [*inner_0, *inner_2], *loop_0).new_loop;

    let Kev {
        vertex: outer_0,
        edge,
    } = dcel.mev(*outer_loop, *inner_0, d3).unwrap();

    let outer_1 = dcel.mev(*outer_loop, *outer_0, d4).unwrap().vertex;
    let outer_2 = dcel.mev(*outer_loop, *outer_1, d5).unwrap().vertex;

    let mut loop_2 = dcel
        .melf(*shell, [*outer_0, *outer_2], *outer_loop)
        .new_loop;
    if edge.lens(dcel).half_edges()[0].loop_().eq(*loop_2) {
        [outer_loop, loop_2] = [loop_2, outer_loop];
    }

    (
        shell,
        [outer_loop, loop_0, loop_2],
        edge,
        [inner_0, inner_1, inner_2, outer_0, outer_1, outer_2],
    )
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
        let (shell, [outer_loop, ..], edge, [inner_0, ..]) = make_hourglass(
            &mut dcel,
            [Inner(0), Inner(1), Inner(2), Outer(0), Outer(1), Outer(2)],
        );
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

        let out_2 = dcel.mev(*loop_0, *out_1, 2).unwrap().vertex;
        let out_3 = dcel.mev(*loop_0, *out_2, 3).unwrap().vertex;
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

#[test]
fn mpkh_kpmh() {
    Dcel::<()>::new(|mut dcel| {
        let (shell, [outer_0, inner_1, outer_1], edge, [vert, ..]) =
            make_hourglass(&mut dcel, [(); 6]);
        let inner_0 = dcel.kemh(*shell, edge, *outer_0, *vert).unwrap().hole_loop;

        let mut mpkh = Mpkh::new(*inner_0);

        for _ in 0..4 {
            use std::collections::HashSet;

            {
                mklens!(&dcel, shell, outer_0, outer_1, inner_0, inner_1);

                assert_eq!(
                    shell.iter_faces().collect::<HashSet<_>>(),
                    HashSet::from([outer_0, outer_1, inner_0, inner_1].map(Lens::face))
                );

                assert_eq!(outer_0.face(), inner_0.face());
                assert_eq!(outer_0.face().outer_loop(), outer_0);
                assert_eq!(outer_0.face().inner_loops(), inner_0);
                assert_eq!(inner_0.next(), inner_0);
            }

            let kpmh = mpkh.apply(&mut dcel).unwrap();

            {
                let new_face = &kpmh.new_face;
                let new_shell = kpmh.new_shell.as_ref().unwrap();

                mklens!(&dcel, shell, new_shell, new_face, outer_0, outer_1, inner_0, inner_1);

                assert_eq!(new_face, inner_0.face());
                assert_eq!(new_face.outer_loop(), inner_0);
                assert!(new_face.iter_inner_loops().next().is_none());

                assert_eq!(
                    shell.body().iter_shells().collect::<HashSet<_>>(),
                    HashSet::from([new_shell, shell])
                );

                assert_eq!(
                    shell.iter_faces().collect::<HashSet<_>>(),
                    HashSet::from([outer_0.face(), outer_1.face()])
                );

                assert_eq!(
                    new_shell.iter_faces().collect::<HashSet<_>>(),
                    HashSet::from([inner_0.face(), inner_1.face()])
                );
            }

            mpkh = kpmh.apply(&mut dcel).unwrap();
        }
    })
}
