use std::{io::Write, path::PathBuf};

use env_logger::Env;

fn file_info(record: &log::Record) -> Option<String> {
    let filename = record.file()?;
    let lineno = record.line()?;
    let path = PathBuf::from(filename);

    let file_style = anstyle::Style::new().dimmed().italic();
    if path.is_relative() {
        Some(format!(" {file_style}{filename}:{lineno}{file_style:#}"))
    } else {
        let module = record.module_path()?;
        Some(format!(" {file_style}{module}{file_style:#}"))
    }
}

pub fn init_logger(level: log::Level, line_numbers: bool) {
    env_logger::Builder::from_env(
        Env::default().filter_or("RUST_LOG", format!("{level},egg=off,z3=off")),
    )
    .format(move |buf, record| {
        let style = buf.default_level_style(record.level());
        let file_info = file_info(record).unwrap_or_default();
        if line_numbers {
            writeln!(
                buf,
                "[{style}{}{style:#}{file_info}] {}",
                record.level(),
                record.args()
            )
        } else {
            writeln!(
                buf,
                "[{style}{}{style:#}] {}",
                record.level(),
                record.args()
            )
        }
    })
    .init();
}
