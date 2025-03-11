use std::path::Path;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion, SamplingMode};
use smt2parser::vmt::VMTModel;
use yardbird::{strategies::Abstract, Driver};

fn run(path: impl AsRef<Path>, depth: u16) {
    let vmt_model = VMTModel::from_path(path).unwrap();

    let cfg = z3::Config::new();
    let context = z3::Context::new(&cfg);
    let mut driver = Driver::new(&context, vmt_model);

    let strat = Box::new(Abstract::new(depth, false));

    _ = driver.check_strategy(depth, strat);
}

fn bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("vmt");
    group.sampling_mode(SamplingMode::Flat);
    group.bench_function("array_double_inverse", |b| {
        b.iter(|| run("examples/array_double_inverse.vmt", 10))
    });
    // group.bench_function("array_doub_access_init_const", |b| {
    //     b.iter(|| run("examples/array_doub_access_init_const.vmt", 10))
    // });
    group.sampling_mode(SamplingMode::Flat);
    group.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .sample_size(10)
        .warm_up_time(Duration::from_secs(50))
        .measurement_time(Duration::from_secs(200));
    targets = bench,
}
criterion_main!(benches);
