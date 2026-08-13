use yardbird::{model_from_options, Driver, EGraphBuilderStrategy, SolverBackend, YardbirdOptions};

fn run_cone_then_full(filename: &str, depth: u16, profile: bool) -> yardbird::ProofLoopResult {
    let mut options = YardbirdOptions::from_filename(filename.to_string());
    options.depth = depth;
    options.egraph_builder = EGraphBuilderStrategy::ConeThenFull;
    options.profile = profile;

    let model = model_from_options(&options);
    let mut driver = Driver::new(
        model,
        options.build_instantiation_strategy(),
        SolverBackend::Z3,
    )
    .with_profiler(options.build_profiler());

    driver
        .check_strategy(options.depth, options.build_array_strategy())
        .expect("cone-then-full refinement should complete")
}

#[test]
fn unproductive_cone_search_widens_without_exhausting_refinement_budget() {
    let result = run_cone_then_full("examples/array/array_split_16.vmt", 14, true);

    assert!(result.total_refinement_steps < 100);
    assert!(
        result
            .profiling
            .cost_records
            .iter()
            .filter_map(|record| record.counters.get("egraph_build_full_stages"))
            .sum::<u64>()
            > 0,
        "an ineligible cone candidate should advance the same-model builder to its full stage"
    );
}

#[test]
fn source_grounded_cone_preserves_complete_write_sites() {
    let result = run_cone_then_full("examples/array/array_partial_init.vmt", 3, false);
    let instantiations = result
        .used_instances
        .iter()
        .chain(&result.const_instances)
        .map(ToString::to_string)
        .collect::<Vec<_>>();

    assert!(
        !instantiations.is_empty(),
        "the source-grounding assertion must observe at least one selected instantiation"
    );
    assert!(
        instantiations
            .iter()
            .all(|term| !term.contains("(Write_Int_Int c+0 Z Z)")),
        "individually source-grounded slots must not be recombined into a write site absent from the source: {instantiations:#?}"
    );
}

#[test]
fn exhaustive_full_stage_uses_derived_candidates_before_concrete_validation() {
    let result = run_cone_then_full("examples/array/array_init_and_copy_inverse.vmt", 6, true);
    let concrete_depths = result
        .profiling
        .driver_records
        .iter()
        .filter(|record| record.action.starts_with("concrete_"))
        .map(|record| record.bmc_depth)
        .collect::<Vec<_>>();

    assert!(
        concrete_depths.is_empty(),
        "full e-graph search is not exhaustive while derived candidates remain hidden; concrete validation ran at depths {concrete_depths:?}"
    );
}
