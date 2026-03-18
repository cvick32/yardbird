//! Training data logging infrastructure for Yardbird.
//!
//! This module provides logging of term selection decisions to a Postgres database
//! for training neural models on instantiation decisions.
//!
//! Enable with `--features training` and use `--train --database-url <url>` flags.

mod config;
#[cfg(feature = "training")]
mod db;
mod logger;
mod schema;
mod term_features;
pub mod term_hash;

pub use config::TrainingConfig;
pub use logger::{NoOpLogger, TrainingLogger};
pub use schema::{CandidateRecord, DecisionRecord, IndexedInstantiationRecord};
pub use term_features::TermFeatures;
pub use term_hash::{canonical_term_hash, canonical_term_hash_from_string};

#[cfg(feature = "training")]
pub use db::DbConnection;
#[cfg(feature = "training")]
pub use logger::PostgresLogger;
