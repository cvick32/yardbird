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

pub fn init_logger(level: log::Level) {
    env_logger::Builder::from_env(
        Env::default().filter_or("RUST_LOG", format!("{level},egg=off,z3=off")),
    )
    .format(|buf, record| {
        let style = buf.default_level_style(record.level());
        let file_info = file_info(record).unwrap_or_default();
        writeln!(
            buf,
            "[{style}{}{style:#}{file_info}] {}",
            record.level(),
            record.args()
        )
    })
    .init();
}
