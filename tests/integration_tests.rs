mod snapshot_tests;

use yardbird::{self, model_from_options, Driver, YardbirdOptions};

macro_rules! create_integration_test {
    ($test_name:ident, $example_name:literal, $num_instances:literal) => {
        #[test]
        fn $test_name() {
            let options = YardbirdOptions::from_filename($example_name.into());
            let vmt_model = model_from_options(&options);
            let driver = Driver::new(&options, &z3::Config::new(), vmt_model);
            let res = driver.check_to_depth(options.depth, 10).unwrap();
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
