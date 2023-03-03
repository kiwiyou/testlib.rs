# testlib.rs

Rust version of Mike Mirzayanov's [testlib.](https://github.com/MikeMirzayanov/testlib)

The original testlib is documented quite bad, so testlib.rs leverages rustdoc.

# Implemented Features

- arguments (indexed, named)
- pseudo random number generator
- input stream validator
- quit with status

# Usage in Polygon

Add `src/lib.rs` to `Resources` as `testlib.rs`, and put `mod testlib` in your source.

# Common Pitfalls

- **DO NOT USE `println!`.**

Validator written in `testlib.h` rejects `\n` line endings as EOLN.

Use `testlib::EOLN` to print EOLN.
