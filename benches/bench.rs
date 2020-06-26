extern crate criterion;

use criterion::{criterion_group, criterion_main, Criterion, Throughput};

fn bench(c: &mut Criterion) {
    {
        const SIZE: usize = 100;

        let mut group = c.benchmark_group("100b");
        group.throughput(Throughput::Bytes(SIZE as u64));
        group.bench_function("zeroes-100", |bencher| {
            bencher.iter(|| {
                adler::from_slice(&[0; SIZE]);
            });
        });
        group.bench_function("ones-100", |bencher| {
            bencher.iter(|| {
                adler::from_slice(&[0xff; SIZE]);
            });
        });
    }

    {
        const SIZE: usize = 1024;

        let mut group = c.benchmark_group("1k");
        group.throughput(Throughput::Bytes(SIZE as u64));

        group.bench_function("zeroes-1k", |bencher| {
            bencher.iter(|| {
                adler::from_slice(&[0; SIZE]);
            });
        });

        group.bench_function("ones-1k", |bencher| {
            bencher.iter(|| {
                adler::from_slice(&[0xff; SIZE]);
            });
        });
    }

    {
        const SIZE: usize = 1024 * 1024;

        let mut group = c.benchmark_group("1m");
        group.throughput(Throughput::Bytes(SIZE as u64));
        group.bench_function("zeroes-1m", |bencher| {
            bencher.iter(|| {
                adler::from_slice(&[0; SIZE]);
            });
        });

        group.bench_function("ones-1m", |bencher| {
            bencher.iter(|| {
                adler::from_slice(&[0xff; SIZE]);
            });
        });
    }
}

criterion_group!(benches, bench);
criterion_main!(benches);
