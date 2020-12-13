Compute the callgraph of a crate.

## Usage

First, run `cargo-callgraph`. The output is currently `target/doc/dependencies.dot` (it’s
hardcoded).

Assuming you are on linux, you can use `dot -Txlib target/doc/dependencies.dot`
to generate an image from the graphviz text file.

You can also use `dot -Tpng target/doc/dependencies.dot > some_file.png` or `dot
-Tpng:cairo target/doc/dependencies.dot > some_file.svg` if you prefer. Note
that `dot -Tsvg` has a bug the miscompute the size of the fonts, so you need to
use `-Tsvg:cairo` instead. You can the use image viewer like `eog` or even
`firefox` ot open the svg file.

Instead of using `dot`, you can also use `fdp` (it's provided alongside `dot`).
Functions will be more spread on the screen.

### Callgraph of a single file in the test directory

```sh
cargo run -- test/test1/src/main.rs && dot target/doc/dependencies.dot -Txlib
```

### Callgraph of the test project.

First you need to build (either in debug or release mode `cargo-callgraph`.

```sh
cargo build
```

Then you can move in the test repository and generate the callgraph. To do so
you need to adjust `RUSTDOC` to point to the binary you just compiled.

```sh
cd test/test1
RUSTDOC=../../target/debug/cargo-callgraph cargo doc && dot target/doc/dependencies.dot -Txlib
```

### Callgraph of any other project

Currently, I highly advice against testing `cargo-callgraph` on any crate that
has more than 500 SLOC since the output will be very hard to visualize, and
`dot` is extremely slow with bigger graph.

Like for the test project, you will first need to compile the current crate with
`cargo build`. Then you will need to use the same nighly version that this crate
use to generate the callgraph. Fortunately, it’s easy to know which version
works, since it’s in the `rust-toolchain` file (it’s the `channel` in followed
by your target triple).

```txt
[toolchain]
channel = "nightly-2020-12-10"
components = ["rustc-dev", "llvm-tools-preview"]
```

```
cd /your/other/crate
RUSTDOC=/path/to/cargo-callgraph/target/debug/cargo-callgraph cargo doc && dot target/dot/dependencies.dot -Txlib
```

I recommend using the `--no-deps` option, in order to limit a bit the size of
the output. `dot` (or `fdp` for that matter) is very slow with huge graphs.


