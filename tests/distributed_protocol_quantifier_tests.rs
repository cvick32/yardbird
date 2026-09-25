use std::{
    fs::{self, File},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Duration, Instant},
};

fn protocol_files() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/distributed_protocols");
    let mut files = Vec::new();
    for directory in fs::read_dir(root).unwrap().flatten() {
        if !directory.path().is_dir() {
            continue;
        }
        for entry in fs::read_dir(directory.path()).unwrap().flatten() {
            if entry
                .path()
                .extension()
                .is_some_and(|extension| extension == "vmt")
                && !entry
                    .file_name()
                    .to_string_lossy()
                    .ends_with(".encoding.vmt")
            {
                files.push(entry.path());
            }
        }
    }
    files.sort();
    files
}

fn check_protocol(file: &Path, depth: u16) {
    let directory = tempfile::tempdir().unwrap();
    let stdout = directory.path().join("stdout.json");
    let stderr = directory.path().join("stderr.log");
    let capture = directory.path().join("capture");
    let mut child = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "--filename",
            file.to_str().unwrap(),
            "--strategy",
            "abstract",
            "--depth",
            &depth.to_string(),
            "--json-output",
            "--track-instantiations",
            "--solver-capture-dir",
            capture.to_str().unwrap(),
        ])
        .env("RUST_LOG", "off")
        .stdout(Stdio::from(File::create(&stdout).unwrap()))
        .stderr(Stdio::from(File::create(&stderr).unwrap()))
        .spawn()
        .unwrap();
    // Ground-instance enumeration is substantially slower without optimization.
    // Keep the release benchmark budget while allowing ordinary `cargo test`.
    let timeout_secs = if cfg!(debug_assertions) { 300 } else { 60 };
    let deadline = Instant::now() + Duration::from_secs(timeout_secs);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!(
                "{} did not finish depth {depth} within {timeout_secs} seconds",
                file.display()
            );
        }
        std::thread::sleep(Duration::from_millis(25));
    };
    assert!(
        status.success(),
        "{}: {}",
        file.display(),
        fs::read_to_string(stderr).unwrap()
    );
    let result: serde_json::Value = serde_json::from_slice(&fs::read(stdout).unwrap()).unwrap();
    assert_eq!(result["counterexample"], false, "{}", file.display());
    assert_eq!(
        result["unsat_events"].as_array().unwrap().len(),
        usize::from(depth),
        "{}",
        file.display()
    );
    assert_eq!(
        result["solver_statistics"]["stats"]["concrete_validation_checks"],
        0,
        "{}",
        file.display()
    );
    let transcript = fs::read_to_string(capture.join("solver-session.smt2")).unwrap();
    for binder in ["(forall ", "(exists ", "(lambda "] {
        assert!(
            !transcript.contains(binder),
            "{} sent {binder} to the solver",
            file.display()
        );
    }
}

#[test]
fn lambda_free_companions_parse_and_match_the_original_inventory() {
    let files = protocol_files();
    assert!(
        files.len() >= 30,
        "distributed protocol inventory unexpectedly shrank"
    );
    // Pointwise array definitions add universal constraints. Some companions
    // exhaust the bounded runtime even at depth zero, so parsing/equivalence
    // coverage must not silently assert that all of them are quickly solvable.
    for original in files {
        let encoded = original.with_extension("encoding.vmt");
        let source = fs::read_to_string(&encoded).unwrap();
        assert!(!source.contains("(lambda "), "{}", encoded.display());
        smt2parser::vmt::VMTModel::from_path(&encoded)
            .unwrap_or_else(|error| panic!("{}: {error:?}", encoded.display()));
    }
}

#[test]
fn lambda_free_database_companion_uses_only_ground_solver_assertions() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/distributed_protocols");
    check_protocol(
        &root.join("client_server_db_ae/client_server_db_ae.encoding.vmt"),
        5,
    );
}

#[test]
fn background_quantifiers_supply_initial_and_later_frame_instances() {
    let directory = tempfile::tempdir().unwrap();
    let file = directory.path().join("background.vmt");
    fs::write(
        &file,
        "(declare-sort S 0)
        (declare-fun p (S) Bool)
        (declare-fun a () (Array S Int))
        (declare-fun a_next () (Array S Int))
        (declare-fun x () Int)
        (declare-fun x_next () Int)
        (declare-fun k () S)
        (define-fun .a () (Array S Int) (! a :next a_next))
        (define-fun .x () Int (! x :next x_next))
        (define-fun init () Bool (! (= x 0) :init true))
        (define-fun trans () Bool (! (= x_next (+ x 1)) :trans true))
        (define-fun prop () Bool
          (! (and (p k) (= (select a k) x)) :invar-property 0))
        (assert (forall ((i S)) (p i)))
        (assert (forall ((i S)) (= (select a i) x)))",
    )
    .unwrap();
    check_protocol(&file, 3);
}

#[test]
fn database_chain_replication_uses_background_axioms_through_a_transition() {
    check_protocol(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join(
            "examples/distributed_protocols/database_chain_replication/database_chain_replication.vmt",
        ),
        2,
    );
}
