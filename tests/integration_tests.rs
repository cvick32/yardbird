mod snapshot_tests;

use yardbird::{self, model_from_options, proof_loop, YardbirdOptions};

macro_rules! create_integration_test {
    ($test_name:ident, $example_name:literal, $num_instances:literal) => {
        #[test]
        fn $test_name() {
            let options = YardbirdOptions {
                filename: $example_name.into(),
                depth: 10,
                bmc_count: 2,
                print_vmt: false,
                interpolate: false,
            };
            let abstract_vmt_model = model_from_options(&options);
            let res = proof_loop(&options, abstract_vmt_model).unwrap();
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
