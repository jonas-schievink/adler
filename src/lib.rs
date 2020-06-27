//! Adler-32 checksum implementation.
//!
//! This implementation features:
//!
//! - Permissively licensed (0BSD) clean-room implementation.
//! - Zero dependencies.
//! - Decent performance (3-4 GB/s).
//! - `#![no_std]` support (with `default-features = false`).

#![doc(html_root_url = "https://docs.rs/adler/0.1.0")]
// Deny a few warnings in doctests, since rustdoc `allow`s many warnings by default
#![doc(test(attr(deny(unused_imports, unused_must_use))))]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(missing_debug_implementations, rust_2018_idioms)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate core as std;

use std::hash::Hasher;

#[cfg(feature = "std")]
use std::io::{self, BufRead};

/// Adler-32 checksum calculator.
///
/// An instance of this type is equivalent to an Adler-32 checksum: It can be created in the default
/// state via [`new`] (or the provided `Default` impl), or from a precalculated checksum via
/// [`from_checksum`], and the currently stored checksum can be fetched via [`checksum`].
///
/// This type also implements `Hasher`, which makes it easy to calculate Adler-32 checksums of any
/// type that implements or derives `Hash`. This also allows using Adler-32 in a `HashMap`, although
/// that is not recommended (while every checksum is a hash, they are not necessarily good at being
/// one).
///
/// [`new`]: #method.new
/// [`from_checksum`]: #method.from_checksum
/// [`checksum`]: #method.checksum
#[derive(Debug, Copy, Clone)]
pub struct Adler32 {
    a: u16,
    b: u16,
}

impl Adler32 {
    /// Creates a new Adler-32 instance with default state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an `Adler32` instance from a precomputed Adler-32 checksum.
    ///
    /// This allows resuming checksum calculation without having to keep the `Adler32` instance
    /// around.
    ///
    /// # Example
    ///
    /// ```
    /// # use adler::Adler32;
    /// let parts = [
    ///     "rust",
    ///     "acean",
    /// ];
    /// let whole = adler::adler32_slice(b"rustacean");
    ///
    /// let mut sum = Adler32::new();
    /// sum.write_slice(parts[0].as_bytes());
    /// let partial = sum.checksum();
    ///
    /// // ...later
    ///
    /// let mut sum = Adler32::from_checksum(partial);
    /// sum.write_slice(parts[1].as_bytes());
    /// assert_eq!(sum.checksum(), whole);
    /// ```
    pub fn from_checksum(sum: u32) -> Self {
        Adler32 {
            a: sum as u16,
            b: (sum >> 16) as u16,
        }
    }

    /// Returns the calculated checksum at this point in time.
    pub fn checksum(&self) -> u32 {
        (u32::from(self.b) << 16) | u32::from(self.a)
    }

    /// Adds `bytes` to the checksum calculation.
    ///
    /// If efficiency matters, this should be called with Byte slices that contain at least a few
    /// thousand Bytes.
    pub fn write_slice(&mut self, bytes: &[u8]) {
        // The basic algorithm is, for every byte:
        //   a = (a + byte) % MOD
        //   b = (b + a) % MOD
        // where MOD = 65521.
        //
        // For efficiency, we can defer the `% MOD` operations as long as neither a nor b overflows:
        // - Between calls to `write`, we ensure that a and b are always in range 0..MOD.
        // - We use 32-bit arithmetic in this function.
        // - Therefore, a and b must not increase by more than 2^32-MOD without performing a `% MOD`
        //   operation.
        //
        // According to Wikipedia, b is calculated as follows for non-incremental checksumming:
        //   b = n×D1 + (n−1)×D2 + (n−2)×D3 + ... + Dn + n*1 (mod 65521)
        // Where n is the number of bytes and Di is the i-th Byte. We need to change this to account
        // for the previous values of a and b, as well as treat every input Byte as being 255:
        //   b_inc = n×255 + (n-1)×255 + ... + 255 + n*65521
        // Or in other words:
        //   b_inc = n*65521 + n(n+1)/2*255
        // The max chunk size is thus the largest value of n so that b_inc <= 2^32-65521.
        //   2^32-65521 = n*65521 + n(n+1)/2*255
        // Plugging this into an equation solver since I can't math gives n = 5552.18..., so 5552.

        const MOD: u32 = 65521;
        const CHUNK_SIZE: usize = 5552;

        let mut a = u32::from(self.a);
        let mut b = u32::from(self.b);
        for chunk in bytes.chunks(CHUNK_SIZE) {
            for byte in chunk {
                let val = u32::from(*byte);
                a += val;
                b += a;
            }

            a %= MOD;
            b %= MOD;
        }
        self.a = a as u16;
        self.b = b as u16;
    }
}

impl Default for Adler32 {
    fn default() -> Self {
        Adler32 { a: 1, b: 0 }
    }
}

impl Hasher for Adler32 {
    fn finish(&self) -> u64 {
        u64::from(self.checksum())
    }

    fn write(&mut self, bytes: &[u8]) {
        self.write_slice(bytes);
    }
}

/// Calculates the Adler-32 checksum of a byte slice.
pub fn adler32_slice(data: &[u8]) -> u32 {
    let mut h = Adler32::new();
    h.write_slice(data);
    h.checksum()
}

/// Calculates the Adler-32 checksum of a `BufRead`'s contents.
///
/// The passed `BufRead` implementor will be read until it reaches EOF.
///
/// If you only have a `Read` implementor, wrap it in `std::io::BufReader`.
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
pub fn adler32_reader<R: BufRead>(reader: &mut R) -> io::Result<u32> {
    let mut h = Adler32::new();
    loop {
        let len = {
            let buf = try!(reader.fill_buf());
            if buf.is_empty() {
                return Ok(h.checksum());
            }

            h.write_slice(buf);
            buf.len()
        };
        reader.consume(len);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::BufReader;

    #[test]
    fn zeroes() {
        assert_eq!(adler32_slice(&[]), 1);
        assert_eq!(adler32_slice(&[0]), 1 | 1 << 16);
        assert_eq!(adler32_slice(&[0, 0]), 1 | 2 << 16);
        assert_eq!(adler32_slice(&[0; 100]), 0x00640001);
        assert_eq!(adler32_slice(&[0; 1024]), 0x04000001);
        assert_eq!(adler32_slice(&[0; 1024 * 1024]), 0x00f00001);
    }

    #[test]
    fn ones() {
        assert_eq!(adler32_slice(&[0xff; 1024]), 0x79a6fc2e);
        assert_eq!(adler32_slice(&[0xff; 1024 * 1024]), 0x8e88ef11);
    }

    #[test]
    fn mixed() {
        assert_eq!(adler32_slice(&[1]), 2 | 2 << 16);
        assert_eq!(adler32_slice(&[40]), 41 | 41 << 16);

        assert_eq!(adler32_slice(&[0xA5; 1024 * 1024]), 0xd5009ab1);
    }

    /// Example calculation from https://en.wikipedia.org/wiki/Adler-32.
    #[test]
    fn wiki() {
        assert_eq!(adler32_slice(b"Wikipedia"), 0x11E60398);
    }

    #[test]
    fn resume() {
        let mut adler = Adler32::new();
        adler.write_slice(&[0xff; 1024]);
        let partial = adler.checksum();
        assert_eq!(partial, 0x79a6fc2e); // from above
        adler.write_slice(&[0xff; 1024 * 1024 - 1024]);
        assert_eq!(adler.checksum(), 0x8e88ef11); // from above

        // Make sure that we can resume computing from the partial checksum via `from_checksum`.
        let mut adler = Adler32::from_checksum(partial);
        adler.write_slice(&[0xff; 1024 * 1024 - 1024]);
        assert_eq!(adler.checksum(), 0x8e88ef11); // from above
    }

    #[test]
    fn bufread() {
        fn test(data: &[u8], checksum: u32) {
            // `BufReader` uses an 8 KB buffer, so this will test buffer refilling.
            let mut buf = BufReader::new(data);
            let real_sum = adler32_reader(&mut buf).unwrap();
            assert_eq!(checksum, real_sum);
        }

        test(&[], 1);
        test(&[0; 1024], 0x04000001);
        test(&[0; 1024 * 1024], 0x00f00001);
        test(&[0xA5; 1024 * 1024], 0xd5009ab1);
    }
}
