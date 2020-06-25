//! TODO: Write crate docs

#![doc(html_root_url = "https://docs.rs/adler/0.0.0")]
// Deny a few warnings in doctests, since rustdoc `allow`s many warnings by default
#![doc(test(attr(deny(unused_imports, unused_must_use))))]
#![warn(missing_debug_implementations, rust_2018_idioms)]

mod readme;

use core::hash::Hasher;

const MOD: u32 = 65521;

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
    pub fn finish(&self) -> u32 {
        (u32::from(self.b) << 16) | u32::from(self.a)
    }
}

impl Default for Adler32 {
    fn default() -> Self {
        Self { a: 1, b: 0 }
    }
}

impl Hasher for Adler32 {
    fn finish(&self) -> u64 {
        u64::from(self.finish())
    }

    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            let val = u32::from(*byte);
            let a = u32::from(self.a);
            let b = u32::from(self.b);
            let new_a = (a + val) % MOD;
            let new_b = (b + new_a) % MOD;
            self.a = new_a as u16;
            self.b = new_b as u16;
        }
    }
}

/// Calculates the Adler-32 checksum of a byte slice.
pub fn from_slice(data: &[u8]) -> u32 {
    let mut h = Adler32::new();
    h.write(data);
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
