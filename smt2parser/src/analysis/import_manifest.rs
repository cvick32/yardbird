use serde::{Deserialize, Serialize};
use std::path::PathBuf;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ImportedBenchmark {
    pub source_path: PathBuf,
    pub relative_path: PathBuf,
    pub destination_path: PathBuf,
    pub family: String,
    pub incrementality: String,
}
