mod snapshot_tests;

use yardbird::{
    self,
    cost_functions::best_symbol_cost_factory,
    model_from_options,
    strategies::{Abstract, ProofStrategy},
    Driver, YardbirdOptions,
};

macro_rules! create_integration_test {
    ($test_name:ident, $example_name:literal, $num_instances:literal) => {
        #[test]
        fn $test_name() {
            let options = YardbirdOptions::from_filename($example_name.into());
            let vmt_model = model_from_options(&options);
            let ctx = z3::Context::new(&z3::Config::new());
            let mut driver = Driver::new(&ctx, vmt_model);
            let strat: Box<dyn ProofStrategy<_>> =
                Box::new(Abstract::new(10, false, best_symbol_cost_factory));
            let res = driver.check_strategy(options.depth, strat).unwrap();
            assert!(
                res.used_instances.len() == $num_instances,
                "{} != {}",
                res.used_instances.len(),
                $num_instances
            );
        }
    };
}

create_integration_test!(test_array_init_var, "examples/array_init_var.vmt", 4);
create_integration_test!(test_array_copy, "examples/array_copy.vmt", 5);
create_integration_test!(test_array_init_const, "examples/array_init_const.vmt", 12);
