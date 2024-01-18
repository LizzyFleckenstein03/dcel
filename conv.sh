#!/bin/bash
set -e
cargo run
for x in *.dot; do
	dot -Kneato -T png $x -o $x.png
	../resize/target/release/resize $x.png 830 827
done
gifski --fast -r 1 -o dcel.gif *.dot.png
