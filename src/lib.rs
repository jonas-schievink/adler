//! Adler-32 checksum implementation.
//!
//! This implementation features:
//!
//! - Permissively licensed (0BSD) clean-room implementation.
//! - Zero dependencies.
//! - Decent performance (3-4 GB/s).
//! - `#![no_std]` support (with `default-features = false`).

#![doc(html_root_url = "https://docs.rs/adler/0.2.2")]
// Deny a few warnings in doctests, since rustdoc `allow`s many warnings by default
#![doc(test(attr(deny(unused_imports, unused_must_use))))]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(missing_debug_implementations)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate core as std;

use std::hash::Hasher;
use std::ops::{AddAssign, MulAssign, RemAssign};

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
    #[inline]
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
    #[inline]
    pub fn from_checksum(sum: u32) -> Self {
        Adler32 {
            a: sum as u16,
            b: (sum >> 16) as u16,
        }
    }

    /// Returns the calculated checksum at this point in time.
    #[inline]
    pub fn checksum(&self) -> u32 {
        (u32::from(self.b) << 16) | u32::from(self.a)
    }

    /// Adds `bytes` to the checksum calculation.
    ///
    /// If efficiency matters, this should be called with Byte slices that contain at least a few
    /// thousand Bytes.
    pub fn write_slice(&mut self, bytes: &[u8]) {
        let a = u32::from(self.a);
        let b = u32::from(self.b);

        let (a, b) = if bytes.len() <= 512 {
            half_parallel_checksum_loop(a, b, bytes)
        } else {
            let (pre_bytes, aligned_bytes, post_bytes) = unsafe {
                // safe to do because we aren't actually reinterpreting bytes--
                // only making sure we do aligned accesses in the main loop
                bytes.align_to::<U8X4>()
            };

            // start with serial iteration until we hit a memory-aligned offset into the slice
            let (a, b) = serial_checksum_loop(a, b, pre_bytes);

            // iterate in parallel
            let (a, b) = parallel_checksum_loop(a, b, aligned_bytes);

            // compute the rest of the sum in serial
            serial_checksum_loop(a, b, post_bytes)
        };

        self.a = a as u16;
        self.b = b as u16;
    }
}

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

fn serial_checksum_loop(a: u32, b: u32, bytes: &[u8]) -> (u32, u32) {
    let mut a = a;
    let mut b = b;
    for chunk in bytes.chunks(CHUNK_SIZE) {
        for &byte in chunk {
            a += u32::from(byte);
            b += a;
        }
        a %= MOD;
        b %= MOD;
    }
    (a, b)
}

// On top of the optimization outlined above, the algorithm can also be parallelized with a
// bit more work:
//
// Note that b is a linear combination of a vector of input bytes (D1, ..., Dn).
//
// If we fix some value k<N and rewrite indices 1, ..., N as
//
//   1_1, 1_2, ..., 1_k, 2_1, ..., 2_k, ..., (N/k)_k,
//
// then we can express a and b in terms of sums of smaller sequences kb and ka:
//
//   ka(j) := D1_j + D2_j + ... + D(N/k)_j where j <= k
//   kb(j) := (N\k)*D1_j + (N/k-1)*D2_j + ... + D(N/k)_j where j <= k
//
//  a = ka(1) + ka(2) + ... + ka(k) + 1
//  b = k*(kb(1) + kb(2) + ... + kb(k)) - 1*ka(2) - ...  - (k-1)*ka(k) + N
//
// We use this insight to unroll the main loop and process 4 bytes at a time.
// The resulting code is higly amenable to auto-vectorization.
//
// This technique is described in-depth (here:)[https://software.intel.com/content/www/us/\
// en/develop/articles/fast-computation-of-fletcher-checksums.html]

fn parallel_checksum_loop(a: u32, b: u32, bytes: &[U8X4]) -> (u32, u32) {
    let mut a = a;
    let mut b = b;
    let mut a_vec = U32X4([0; 4]);
    let mut b_vec = a_vec;

    for chunk in bytes.chunks(CHUNK_SIZE) {
        for byte_vec in chunk {
            a_vec += U32X4::from(byte_vec);
            b_vec += a_vec;
            b += 4 * a;
        }
        a_vec %= MOD;
        b_vec %= MOD;
        b %= MOD;
    }
    // combine the sub-sum results into the main sum
    b_vec *= 4;
    b_vec.0[1] += ((MOD - 1) * a_vec.0[1]) % MOD;
    b_vec.0[2] += ((MOD - 2) * a_vec.0[2]) % MOD;
    b_vec.0[3] += ((MOD - 3) * a_vec.0[3]) % MOD;
    for (av, bv) in a_vec.0.iter().zip(b_vec.0.iter()) {
        a += av;
        b += bv;
    }
    (a % MOD, b % MOD)
}

// Optimized function for short byte slices. The tradeoff of larger k values
// is that the modular-subtraction operation requires relatively frequent
// '%' operations to ensure that the multiply doesn't overflow, which offsets
// the increased instruction parallelism below a certain chunk/buffer length.
// Here we strike a compromise, using k = 2 and foregoing the usual
// arithmetic-overflow bookkeeping around CHUNK_SIZE.

fn half_parallel_checksum_loop(a: u32, b: u32, bytes: &[u8]) -> (u32, u32) {
    debug_assert!(bytes.len() <= CHUNK_SIZE);

    let mut a = a;
    let mut b = b;
    let mut a1 = 0;
    let mut a2 = 0;
    let mut b1 = 0;
    let mut b2 = 0;

    let u8x2_iter = bytes.chunks_exact(2);
    let remainder = u8x2_iter.remainder();

    for u8x2 in u8x2_iter {
        a1 += u32::from(u8x2[0]);
        a2 += u32::from(u8x2[1]);
        b1 += a1;
        b2 += a2;
        b += 2 * a;
    }
    b1 += b1;
    b2 += b2 + (((MOD - 1) * a2) % MOD);
    a += a1 + a2;
    b += b1 + b2;
    for &byte in remainder {
        a += u32::from(byte);
        b += a;
    }
    (a % MOD, b % MOD)
}

impl Default for Adler32 {
    #[inline]
    fn default() -> Self {
        Adler32 { a: 1, b: 0 }
    }
}

impl Hasher for Adler32 {
    #[inline]
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

#[derive(Copy, Clone)]
#[repr(align(4))]
struct U8X4([u8; 4]);

#[derive(Copy, Clone)]
struct U32X4([u32; 4]);

impl U32X4 {
    #[inline]
    fn from(bytes: &U8X4) -> Self {
        U32X4([
            u32::from(bytes.0[0]),
            u32::from(bytes.0[1]),
            u32::from(bytes.0[2]),
            u32::from(bytes.0[3]),
        ])
    }
}

impl AddAssign<Self> for U32X4 {
    #[inline]
    fn add_assign(&mut self, other: Self) {
        for (s, o) in self.0.iter_mut().zip(other.0.iter()) {
            *s += o;
        }
    }
}

impl RemAssign<u32> for U32X4 {
    #[inline]
    fn rem_assign(&mut self, quotient: u32) {
        for s in self.0.iter_mut() {
            *s %= quotient;
        }
    }
}

impl MulAssign<u32> for U32X4 {
    #[inline]
    fn mul_assign(&mut self, rhs: u32) {
        for s in self.0.iter_mut() {
            *s *= rhs;
        }
    }
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
            let buf = reader.fill_buf()?;
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
    fn unaligned() {
        let buf = [0xe7; 1024];
        assert_eq!(adler32_slice(&buf[0..1021]), 0x6c739979);
        assert_eq!(adler32_slice(&buf[1..1022]), 0x6c739979);
        assert_eq!(adler32_slice(&buf[2..1023]), 0x6c739979);
        assert_eq!(adler32_slice(&buf[3..]), 0x6c739979);
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
