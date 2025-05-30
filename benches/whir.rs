use criterion::{Criterion, criterion_group, criterion_main};
use whir_p3::{
    parameters::{FoldType, FoldingFactor, errors::SecurityAssumption},
    whir::make_whir_things,
};

fn benchmark_whir(c: &mut Criterion) {
    let num_variables = 18;
    let folding_factor = FoldingFactor::Constant(4);
    let num_points = 2;
    let soundness_type = SecurityAssumption::UniqueDecoding;
    let pow_bits = 10;
    let fold_type = FoldType::ProverHelps;

    c.bench_function("whir_end_to_end", |b| {
        b.iter(|| {
            make_whir_things(
                num_variables,
                folding_factor,
                num_points,
                soundness_type,
                pow_bits,
                fold_type,
            );
        });
    });
}

criterion_group!(benches, benchmark_whir);
criterion_main!(benches);
