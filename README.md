# Adler-32 checksums for Rust

[![crates.io](https://img.shields.io/crates/v/adler.svg)](https://crates.io/crates/adler)
[![docs.rs](https://docs.rs/adler/badge.svg)](https://docs.rs/adler/)
[![Build Status](https://travis-ci.org/jonas-schievink/adler.svg?branch=master)](https://travis-ci.org/jonas-schievink/adler)

This crate provides a simple implementation of the Adler-32 checksum, used in
zlib, rsync, and other software.

Please refer to the [changelog](CHANGELOG.md) to see what changed in the last
releases.

## Features

- Permissively licensed (0BSD) clean-room implementation.
- Zero dependencies.
- Decent performance (3-4 GB/s).
- Supports `#![no_std]` (with `default-features = false`).

## Usage

Add an entry to your `Cargo.toml`:

```toml
[dependencies]
adler = "0.2.0"
```

Check the [API Documentation](https://docs.rs/adler/) for how to use the
crate's functionality.

## Rust version support

Currently, this crate supports all Rust versions starting at Rust 1.8.0 (earlier
versions are unsupported only because they cannot communicate with crates.io
anymore).

Bumping the Minimum Supported Rust Version (MSRV) is *not* considered a breaking
change, but will not be done without good reasons. The latest 3 stable Rust
versions will always be supported no matter what.
