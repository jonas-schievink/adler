extern crate adler;
extern crate criterion;

use adler::{adler32_slice, Adler32};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

fn simple(c: &mut Criterion) {
    {
        const SIZE: usize = 100;

        let mut group = c.benchmark_group("simple-100b");
        group.throughput(Throughput::Bytes(SIZE as u64));
        group.bench_function("zeroes-100", |bencher| {
            bencher.iter(|| {
                adler32_slice(&[0; SIZE]);
            });
        });
        group.bench_function("ones-100", |bencher| {
            bencher.iter(|| {
                adler32_slice(&[0xff; SIZE]);
            });
        });
    }

    {
        const SIZE: usize = 1024;

        let mut group = c.benchmark_group("simple-1k");
        group.throughput(Throughput::Bytes(SIZE as u64));

        group.bench_function("zeroes-1k", |bencher| {
            bencher.iter(|| {
                adler32_slice(&[0; SIZE]);
            });
        });

        group.bench_function("ones-1k", |bencher| {
            bencher.iter(|| {
                adler32_slice(&[0xff; SIZE]);
            });
        });
    }

    {
        const SIZE: usize = 1024 * 1024;

        let mut group = c.benchmark_group("simple-1m");
        group.throughput(Throughput::Bytes(SIZE as u64));
        group.bench_function("zeroes-1m", |bencher| {
            bencher.iter(|| {
                adler32_slice(&[0; SIZE]);
            });
        });

        group.bench_function("ones-1m", |bencher| {
            bencher.iter(|| {
                adler32_slice(&[0xff; SIZE]);
            });
        });
    }
}

fn chunked(c: &mut Criterion) {
    const SIZE: usize = 16 * 1024 * 1024;

    let data = vec![0xAB; SIZE];

    let mut group = c.benchmark_group("chunked-16m");
    group.throughput(Throughput::Bytes(SIZE as u64));
    group.bench_function("5552", |bencher| {
        bencher.iter(|| {
            let mut h = Adler32::new();
            for chunk in data.chunks(5552) {
                h.write_slice(chunk);
            }
            h.checksum()
        });
    });
    group.bench_function("8k", |bencher| {
        bencher.iter(|| {
            let mut h = Adler32::new();
            for chunk in data.chunks(8 * 1024) {
                h.write_slice(chunk);
            }
            h.checksum()
        });
    });
    group.bench_function("64k", |bencher| {
        bencher.iter(|| {
            let mut h = Adler32::new();
            for chunk in data.chunks(64 * 1024) {
                h.write_slice(chunk);
            }
            h.checksum()
        });
    });
    group.bench_function("1m", |bencher| {
        bencher.iter(|| {
            let mut h = Adler32::new();
            for chunk in data.chunks(1024 * 1024) {
                h.write_slice(chunk);
            }
            h.checksum()
        });
    });
}

fn compare_input_sizes(c: &mut Criterion) {
    const SIZE: usize = 2048;
    const INCR: usize = 128;

    let data = vec![0xff; SIZE];

    let mut group = c.benchmark_group("compare-input-size");
    for size_increment in 1..=SIZE / INCR {
        let size = size_increment * INCR;
        group.throughput(Throughput::Bytes(size as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            &data[0..size],
            |bencher, d| {
                bencher.iter(|| adler32_slice(d));
            },
        );
    }
    group.finish();
}

criterion_group!(benches, simple, chunked, compare_input_sizes);
criterion_main!(benches);
