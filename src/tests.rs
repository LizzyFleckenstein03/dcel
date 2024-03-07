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

        for i in 0..10 {
            struct State {
                seen: u8,
                last: Option<Vert>,
            }

            let mut st = State {
                seen: 0,
                last: None,
            };

            for v in outer_loop
                .iter_half_edges(&dcel)
                .map(|x| *x.origin().data())
            {
                let mut s = 1u8 << v.either();
                if v.is_outer() {
                    s <<= 4;
                }
                if st.seen & s == 0 {
                    st.seen |= s;
                } else {
                    assert_eq!(v.either(), 0);
                    assert_eq!(st.seen & (s << 3), 0);
                    st.seen |= s << 3;
                }

                if let Some(last) = st.last {
                    if v.either() == 0 {
                        assert!(
                            last == v.flip()
                                || (last.is_outer() == v.is_outer() && last.either() != 0)
                        );
                    } else {
                        assert_eq!(last.is_outer(), v.is_outer());
                    }
                }

                st.last = Some(v);
            }

            assert_eq!(st.seen, 255);

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
