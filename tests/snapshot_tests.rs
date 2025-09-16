use insta::assert_debug_snapshot;
use std::{
    path::Path,
    sync::mpsc::{self, RecvTimeoutError},
    thread,
    time::Duration,
};
use yardbird::{
    self,
    cost_functions::array::best_symbol_cost_factory,
    model_from_options,
    strategies::{Abstract, ProofStrategy},
    Driver, YardbirdOptions,
};

#[derive(Debug)]
enum BenchStatus {
    Good,
    Timeout,
    Panic,
}

fn run_with_timeout<F, T>(f: F, timeout: Duration) -> (BenchStatus, T)
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + Default + 'static,
{
    let (tx, rx) = mpsc::channel();
    let _ = thread::spawn(move || {
        let result = f();
        if let Ok(()) = tx.send(result) {}
    });

    match rx.recv_timeout(timeout) {
        Ok(insts) => (BenchStatus::Good, insts),
        Err(RecvTimeoutError::Timeout) => (BenchStatus::Timeout, T::default()),
        Err(RecvTimeoutError::Disconnected) => (BenchStatus::Panic, T::default()),
    }
}

#[allow(unused)]
#[derive(Debug)]
struct BenchmarkResult {
    example_name: String,
    status: BenchStatus,
    used_instantiations: Vec<String>,
}

fn run_benchmark(filename: impl AsRef<Path>) -> BenchmarkResult {
    let options = YardbirdOptions::from_filename(filename.as_ref().to_string_lossy().to_string());
    let vmt_model = model_from_options(&options);
    let (status, used_instantiations) = run_with_timeout(
        move || {
            let ctx = z3::Context::new(&z3::Config::new());
            let mut driver = Driver::new(&ctx, vmt_model);
            let strat: Box<dyn ProofStrategy<_>> =
                Box::new(Abstract::new(10, false, best_symbol_cost_factory));
            let res = driver.check_strategy(options.depth, strat).unwrap();
            res.used_instances
        },
        Duration::from_secs(20),
    );
    BenchmarkResult {
        example_name: filename.as_ref().to_string_lossy().to_string(),
        status,
        used_instantiations: used_instantiations
            .iter()
            .map(ToString::to_string)
            .collect(),
    }
}

macro_rules! create_snapshot_test {
    ($test:ident) => {
        #[test]
        fn $test() {
            let path = format!("examples/{}.vmt", stringify!($test));
            assert_debug_snapshot!(stringify!($test), run_benchmark(&path));
        }
    };
}

// TODO: would be nice to automatically generate this
create_snapshot_test!(array2dim_copy);
create_snapshot_test!(array2dim_init);
create_snapshot_test!(array2dim_init_i);
create_snapshot_test!(array2dim_init_j);
create_snapshot_test!(array2dim_rec1);
create_snapshot_test!(array2dim_rec2);
create_snapshot_test!(array_append2_array_horn);
create_snapshot_test!(array_bubble_sort);
create_snapshot_test!(array_bubble_sort_rev);
create_snapshot_test!(array_copy);
create_snapshot_test!(array_copy_increment);
create_snapshot_test!(array_copy_increment_ind);
create_snapshot_test!(array_copy_ind);
create_snapshot_test!(array_copy_inverse);
create_snapshot_test!(array_copy_nondet_add);
create_snapshot_test!(array_copy_sum);
create_snapshot_test!(array_copy_sum_ind);
create_snapshot_test!(array_doub_access_init);
create_snapshot_test!(array_doub_access_init_const);
create_snapshot_test!(array_double_inverse);
create_snapshot_test!(array_equiv_1);
create_snapshot_test!(array_equiv_2);
create_snapshot_test!(array_equiv_3);
create_snapshot_test!(array_even_odd_1);
create_snapshot_test!(array_even_odd_2);
create_snapshot_test!(array_horn_copy2);
create_snapshot_test!(array_hybr_add);
create_snapshot_test!(array_hybr_nest_1);
create_snapshot_test!(array_hybr_nest_2);
create_snapshot_test!(array_hybr_nest_3);
create_snapshot_test!(array_hybr_nest_4);
create_snapshot_test!(array_hybr_nest_5);
create_snapshot_test!(array_hybr_sum);
create_snapshot_test!(array_index_compl);
create_snapshot_test!(array_init_addvar);
create_snapshot_test!(array_init_addvar2);
create_snapshot_test!(array_init_addvar3);
create_snapshot_test!(array_init_addvar4);
create_snapshot_test!(array_init_addvar5);
create_snapshot_test!(array_init_addvar6);
create_snapshot_test!(array_init_addvar7);
create_snapshot_test!(array_init_and_copy);
create_snapshot_test!(array_init_and_copy_const);
create_snapshot_test!(array_init_and_copy_inverse);
create_snapshot_test!(array_init_batches);
create_snapshot_test!(array_init_batches_const);
create_snapshot_test!(array_init_batches_ind);
create_snapshot_test!(array_init_both_ends);
create_snapshot_test!(array_init_both_ends2);
create_snapshot_test!(array_init_both_ends_multiple);
create_snapshot_test!(array_init_both_ends_multiple_sum);
create_snapshot_test!(array_init_both_ends_simpl);
create_snapshot_test!(array_init_both_ends_simpl_const);
create_snapshot_test!(array_init_const);
create_snapshot_test!(array_init_const_const);
create_snapshot_test!(array_init_const_ind);
create_snapshot_test!(array_init_depend);
create_snapshot_test!(array_init_depend_incr);
create_snapshot_test!(array_init_disj);
create_snapshot_test!(array_init_disj_const);
create_snapshot_test!(array_init_doubl);
create_snapshot_test!(array_init_doubl2);
create_snapshot_test!(array_init_doubl3);
create_snapshot_test!(array_init_double);
create_snapshot_test!(array_init_double_const);
create_snapshot_test!(array_init_drop);
create_snapshot_test!(array_init_increm);
create_snapshot_test!(array_init_increm_const);
create_snapshot_test!(array_init_increm_twice);
create_snapshot_test!(array_init_increm_twice_const);
create_snapshot_test!(array_init_increm_two_arrs);
create_snapshot_test!(array_init_increm_two_arrs_antisym);
create_snapshot_test!(array_init_increm_two_arrs_antisym_const);
create_snapshot_test!(array_init_increm_two_arrs_const);
create_snapshot_test!(array_init_ite);
create_snapshot_test!(array_init_ite_dupl);
create_snapshot_test!(array_init_ite_jump);
create_snapshot_test!(array_init_ite_jump_const);
create_snapshot_test!(array_init_ite_jump_two);
create_snapshot_test!(array_init_ite_jump_two_const);
create_snapshot_test!(array_init_monot_ind);
create_snapshot_test!(array_init_nondet_var_mult);
create_snapshot_test!(array_init_nondet_vars);
create_snapshot_test!(array_init_nondet_vars2);
create_snapshot_test!(array_init_nondet_vars_plus_ind);
create_snapshot_test!(array_init_pair_sum);
create_snapshot_test!(array_init_pair_sum_const);
create_snapshot_test!(array_init_pair_symmetr);
create_snapshot_test!(array_init_pair_symmetr2);
create_snapshot_test!(array_init_pair_symmetr3);
create_snapshot_test!(array_init_pair_symmetr4);
create_snapshot_test!(array_init_reverse);
create_snapshot_test!(array_init_reverse_const);
create_snapshot_test!(array_init_reverse_mult);
create_snapshot_test!(array_init_select);
create_snapshot_test!(array_init_select_copy);
create_snapshot_test!(array_init_symmetr_swap);
create_snapshot_test!(array_init_symmetr_swap_const);
create_snapshot_test!(array_init_tuples);
create_snapshot_test!(array_init_tuples_relative);
create_snapshot_test!(array_init_upto_nondet);
create_snapshot_test!(array_init_var);
create_snapshot_test!(array_init_var_ind);
create_snapshot_test!(array_init_var_plus_ind);
create_snapshot_test!(array_init_var_plus_ind2);
create_snapshot_test!(array_init_var_plus_ind3);
create_snapshot_test!(array_max_min);
create_snapshot_test!(array_max_min_approx);
create_snapshot_test!(array_max_min_shift);
create_snapshot_test!(array_max_reverse_min);
create_snapshot_test!(array_min);
create_snapshot_test!(array_min_and_copy);
create_snapshot_test!(array_min_and_copy_inverse);
create_snapshot_test!(array_min_and_copy_shift);
create_snapshot_test!(array_min_and_copy_shift_sum);
create_snapshot_test!(array_min_and_copy_shift_sum_add);
create_snapshot_test!(array_min_const);
create_snapshot_test!(array_min_ind);
create_snapshot_test!(array_min_max);
create_snapshot_test!(array_min_max_const);
create_snapshot_test!(array_min_swap);
create_snapshot_test!(array_min_swap_and_shift);
create_snapshot_test!(array_min_swap_const);
create_snapshot_test!(array_nest_split_01);
create_snapshot_test!(array_nest_split_02);
create_snapshot_test!(array_nest_split_03);
create_snapshot_test!(array_nest_split_04);
create_snapshot_test!(array_nest_split_05);
create_snapshot_test!(array_nonlin_init_depend);
create_snapshot_test!(array_nonlin_init_mult);
create_snapshot_test!(array_nonlin_square);
create_snapshot_test!(array_partial_init);
create_snapshot_test!(array_single_elem);
create_snapshot_test!(array_single_elem_const);
create_snapshot_test!(array_single_elem_increm);
create_snapshot_test!(array_split_01);
create_snapshot_test!(array_split_02);
create_snapshot_test!(array_split_03);
create_snapshot_test!(array_split_04);
create_snapshot_test!(array_split_05);
create_snapshot_test!(array_split_06);
create_snapshot_test!(array_split_07);
create_snapshot_test!(array_split_08);
create_snapshot_test!(array_split_09);
create_snapshot_test!(array_split_10);
create_snapshot_test!(array_split_11);
create_snapshot_test!(array_split_12);
create_snapshot_test!(array_split_13);
create_snapshot_test!(array_split_14);
create_snapshot_test!(array_split_15);
create_snapshot_test!(array_split_16);
create_snapshot_test!(array_split_17);
create_snapshot_test!(array_split_18);
create_snapshot_test!(array_split_19);
create_snapshot_test!(array_split_20);
create_snapshot_test!(array_split_21);
create_snapshot_test!(array_standard_copy4);
create_snapshot_test!(array_standard_partition);
create_snapshot_test!(array_standard_password);
create_snapshot_test!(array_tiling_pnr2);
create_snapshot_test!(array_tiling_pnr3);
create_snapshot_test!(array_tiling_pnr4);
create_snapshot_test!(array_tiling_pnr5);
create_snapshot_test!(array_tiling_poly1);
create_snapshot_test!(array_tiling_poly2);
create_snapshot_test!(array_tiling_poly3);
create_snapshot_test!(array_tiling_poly4);
create_snapshot_test!(array_tiling_poly5);
create_snapshot_test!(array_tiling_poly6);
create_snapshot_test!(array_tiling_pr2);
create_snapshot_test!(array_tiling_pr3);
create_snapshot_test!(array_tiling_pr4);
create_snapshot_test!(array_tiling_pr5);
create_snapshot_test!(array_tiling_rew);
create_snapshot_test!(array_tiling_rewnif);
create_snapshot_test!(array_tiling_rewnifrev);
create_snapshot_test!(array_tiling_rewnifrev2);
create_snapshot_test!(array_tiling_rewrev);
create_snapshot_test!(array_tiling_skipped);
create_snapshot_test!(array_tiling_tcpy);
create_snapshot_test!(array_tiling_tcpy2);
create_snapshot_test!(array_tiling_tcpy3);
create_snapshot_test!(array_tripl_access_init);
create_snapshot_test!(array_tripl_access_init_const);
create_snapshot_test!(array_two_counters_add);
create_snapshot_test!(array_two_counters_init_const);
create_snapshot_test!(array_two_counters_init_var);
create_snapshot_test!(array_two_counters_max_subtr);
create_snapshot_test!(array_two_counters_min_max);
create_snapshot_test!(array_two_counters_min_max_prog);
create_snapshot_test!(array_two_counters_replace);
create_snapshot_test!(array_two_counters_sum);
create_snapshot_test!(array_zero_sum_m2);
