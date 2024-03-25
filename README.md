# dcel

An implementation of a [half-edge data structure (DCEL)](https://en.wikipedia.org/wiki/Doubly_connected_edge_list) in purely safe Rust, using [ghost-cell](https://plv.mpi-sws.org/rustbelt/ghostcell/) and typed arena allocation to deal with the cyclic nature of the data structure.

The goal is to provide a safe (primary priority) and performant (secondary priority) library for mesh processing in Rust.

Provided features are importing from and exporting to OBJ-files as well as a set of Euler Operators for surgery. For debugging purposes, using cairo to visualize the graph as an image is also supported.

OBJ-files can only be imported as long as they represent a valid 2-manifold / surface.

Using hole (inner) loops, objects of arbitrary genus can be represented.

A freelist is used to reuse arena-allocated memory, together with generational references that prevent use-after-free and double-free bugs using runtime checks.

# Operators/Surgery

This library's set of euler operators is similar to the one used in [SNUMOD](https://ocw.snu.ac.kr/sites/default/files/NOTE/4837.pdf). All operators and their preconditions are documented via rustdoc, but it is recommended to check out the SNUMOD slides to get a visual representation of what the operators do. [src/tests.rs](src/tests.rs) contains many usage examples in the form of integration tests.

# Read Access

A `Ptr` type is used to represent pointers to different kinds of entities (`Vertex`, `HalfEdge`, `Loop`, `Face`, `Edge`, `Shell`, `Body`). For each entity, its `Ptr` implementation has various methods to access its attributes which are documented via rustdoc. `Iterator` implementations are available for iteratin over list data (Outgoing half-edges from a vertex, half-edges in a loop, faces in a shell etc.).

To access the contents of a `Ptr`, a reference to a `GhostToken` (from the [ghost-cell](https://crates.io/crates/ghost-cell) crate) is required. This ensures that Rust's AXM (Aliasing XOR Mutation) rule is not broken.

Additionally, there is a `Lens` struct which holds both a `Ptr` and a reference to a `GhostToken`. This allows for more ergonomic usage since no token needs to be passed to each method, but it also means lenses cannot be held while the DCEL structure is mutated.

# Export

DCELs can be written to a `.obj` file using the `ObjExport::export` method, passing it functions to convert vertex user-data stored in the DCEL structure to positions (and optionally texture coordinates and normals). In the exported file, hole loops are connected to their peripheral loops using edges, which is equivalent to using the MEKH operator on them. [examples/pyramid.rs](examples/pyramid.rs) and [examples/subdivision.rs](examples/subdivision.rs) contain usage examples.

# Import

For importing `.obj` files, the `RawObj` struct from the [obj-rs](https://crates.io/crates/obj-rs) crate is used. Therefore, the `obj_import` feature flag must be enabled if the user wishes to import OBJ files using `ObjImport::import`. As with exporting, a function to convert vertex position data to DCEL vertex user-data must be provided. If the OBJ file is not a valid 2-manifold, an error describing the detected invalidity in the topology is returned. [examples/subdivision.rs](examples/subdivision.rs) contains a usage example.
