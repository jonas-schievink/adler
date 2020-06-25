# Adler-32 checksums

[![crates.io](https://img.shields.io/crates/v/adler.svg)](https://crates.io/crates/adler)
[![docs.rs](https://docs.rs/adler/badge.svg)](https://docs.rs/adler/)
[![Build Status](https://travis-ci.org/jonas-schievink/adler.svg?branch=master)](https://travis-ci.org/jonas-schievink/adler)

This crate provides a simple implementation of the Adler-32 checksum, used in
zlib, rsync, and other software.

Please refer to the [changelog](CHANGELOG.md) to see what changed in the last
releases.

## Features

- Permissively licensed clean-room implementation.
- Zero dependencies.

## Usage

Add an entry to your `Cargo.toml`:

```toml
[dependencies]
adler = "0.1.0"
```

Check the [API Documentation](https://docs.rs/adler/) for how to use the
crate's functionality.

## Rust version support

This crate supports the 3 latest stable Rust releases. Bumping the minimum
supported Rust version (MSRV) is not considered a breaking change as long as
these 3 versions are still supported.

The MSRV is also explicitly tested against in [.travis.yml](.travis.yml).
