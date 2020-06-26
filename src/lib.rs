//! Adler-32 checksum implementation.

#![doc(html_root_url = "https://docs.rs/adler/0.1.0")]
// Deny a few warnings in doctests, since rustdoc `allow`s many warnings by default
#![doc(test(attr(deny(unused_imports, unused_must_use))))]
#![warn(missing_debug_implementations, rust_2018_idioms)]
#![no_std]

use core::hash::Hasher;

/// Adler-32 checksum calculator.
#[derive(Debug, Copy, Clone)]
pub struct Adler32 {
    a: u16,
    b: u16,
}

impl Adler32 {
    /// Creates a new Adler-32 instance.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the calculated checksum at this point in time.
    // FIXME: Rename to `checksum`?
    pub fn finish(&self) -> u32 {
        (u32::from(self.b) << 16) | u32::from(self.a)
    }

    /// Adds `bytes` to the checksum calculation.
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
        u64::from(self.finish())
    }

    fn write(&mut self, bytes: &[u8]) {
        self.write_slice(bytes);
    }
}

/// Calculates the Adler-32 checksum of a byte slice.
// FIXME: Rename this?
pub fn from_slice(data: &[u8]) -> u32 {
    let mut h = Adler32::new();
    h.write_slice(data);
    h.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zeroes() {
        assert_eq!(from_slice(&[]), 1);
        assert_eq!(from_slice(&[0]), 1 | 1 << 16);
        assert_eq!(from_slice(&[0, 0]), 1 | 2 << 16);
        assert_eq!(from_slice(&[0; 100]), 0x00640001);
        assert_eq!(from_slice(&[0; 1024]), 0x04000001);
        assert_eq!(from_slice(&[0; 1024 * 1024]), 0x00f00001);
    }

    #[test]
    fn ones() {
        assert_eq!(from_slice(&[0xff; 1024]), 0x79a6fc2e);
        assert_eq!(from_slice(&[0xff; 1024 * 1024]), 0x8e88ef11);
    }

    #[test]
    fn mixed() {
        assert_eq!(from_slice(&[1]), 2 | 2 << 16);
        assert_eq!(from_slice(&[40]), 41 | 41 << 16);

        assert_eq!(from_slice(&[0xA5; 1024 * 1024]), 0xd5009ab1);
    }

    /// Example calculation from https://en.wikipedia.org/wiki/Adler-32.
    #[test]
    fn wiki() {
        assert_eq!(from_slice(b"Wikipedia"), 0x11E60398);
    }
}
