pub use smt2parser::vmt::VMTModel;
pub use vmt_macros::{ensures, generate_test};
pub use vmtil;
use yardbird::{cost_functions::best_symbol_cost_factory, strategies::Abstract, Driver};

pub struct RunModelArgs {
    pub builder: vmtil::VmtilBuilder,
    pub depth: u16,
    pub debug_vmt: bool,
    pub should_fail: bool,
    pub logger: Option<log::Level>,
}

impl Default for RunModelArgs {
    fn default() -> Self {
        Self {
            builder: vmtil::VmtilBuilder::default(),
            depth: 10,
            debug_vmt: false,
            should_fail: false,
            logger: None,
        }
    }
}

pub fn run_model(
    RunModelArgs {
        builder,
        depth,
        debug_vmt,
        should_fail,
        logger,
    }: RunModelArgs,
) -> bool {
    if let Some(level) = logger {
        yardbird::logger::init_logger(level);
    }

    let model = builder.build_model(debug_vmt);
    let cfg = z3::Config::new();
    let context = z3::Context::new(&cfg);
    let mut driver = Driver::new(&context, model);

    let strat = Box::new(Abstract::new(depth, false, best_symbol_cost_factory));

    match driver.check_strategy(depth, strat) {
        Ok(res) => {
            println!("Used Instances: \n{}", res.get_instantiations_string());
            !res.used_instances.is_empty() && !debug_vmt && !should_fail
        }
        Err(e) => {
            println!("Err: {e}");
            should_fail && !debug_vmt
        }
    }
}
