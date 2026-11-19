//! Credential-free JSONL test client, using the real Rust binary and solver.
use serde_json::{json, Value};
use std::{
    io::{BufRead, BufReader, Write},
    process::{Child, ChildStdin, Command, Stdio},
    sync::mpsc::{self, Receiver},
    time::Duration,
};

pub struct Session {
    child: Child,
    input: ChildStdin,
    responses: Receiver<Value>,
    sequence: usize,
    pub epoch: Value,
    pub ready: Value,
    pub last_command: Value,
}
impl Session {
    pub fn new(fixture: &str, depth: u16, pause: u16, assisted: bool) -> Self {
        let mut child = Command::new(env!("CARGO_BIN_EXE_yardbird"))
            .args([
                "-f",
                &format!("tests/fixtures/{fixture}.vmt"),
                "-d",
                &depth.to_string(),
                "--agent-stdio",
                "--agent-pause-depth",
                &pause.to_string(),
                "--agent-control",
                if assisted { "assisted" } else { "explicit" },
                "--wall-timeout-secs",
                "30",
            ])
            .env("RUST_LOG", "error")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap();
        let input = child.stdin.take().unwrap();
        let output = child.stdout.take().unwrap();
        let (sender, responses) = mpsc::channel();
        std::thread::spawn(move || {
            for line in BufReader::new(output).lines() {
                let Ok(line) = line else { break };
                let message = serde_json::from_str(&line).expect("JSONL server response");
                if sender.send(message).is_err() {
                    break;
                }
            }
        });
        let mut session = Self {
            child,
            input,
            responses,
            sequence: 0,
            epoch: Value::Null,
            ready: Value::Null,
            last_command: Value::Null,
        };
        session.ready = session.receive();
        assert_eq!(session.ready["event"], "ready");
        let paused = session.receive();
        assert_eq!(paused["event"], "paused", "{paused}");
        session.epoch = paused["paused"]["epoch"].clone();
        session
    }
    pub fn receive(&self) -> Value {
        self.responses
            .recv_timeout(Duration::from_secs(35))
            .expect("bounded protocol response")
    }
    pub fn send(&mut self, command: &Value) -> Value {
        serde_json::to_writer(&mut self.input, command).unwrap();
        writeln!(self.input).unwrap();
        self.input.flush().unwrap();
        self.receive()
    }
    pub fn invoke(&mut self, op: &str, mut args: Value) -> Value {
        self.sequence += 1;
        args["v"] = json!(0);
        args["id"] = json!(format!("c{}", self.sequence));
        args["op"] = json!(op);
        if args.get("epoch").is_none() {
            args["epoch"] = self.epoch.clone();
        }
        self.last_command = args.clone();
        let reply = self.send(&args);
        assert_eq!(reply["id"], args["id"]);
        assert_eq!(reply["op"], op);
        if reply["ok"] == true {
            self.epoch = reply["epoch"].clone();
        }
        reply
    }
    pub fn call(&mut self, op: &str, args: Value) -> Value {
        let reply = self.invoke(op, args);
        assert_eq!(reply["ok"], true, "{reply}");
        reply["result"].clone()
    }
    pub fn terminal(&mut self, reason: &str) {
        assert_eq!(self.receive()["reason"], reason);
        assert!(self.child.wait().unwrap().success());
    }
    pub fn stop(&mut self) {
        self.call("stop", json!({}));
        self.terminal("stopped");
    }
}
impl Drop for Session {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}
pub fn term_id(snapshot: &Value, expression: &str) -> Value {
    snapshot["terms"]
        .as_array()
        .unwrap()
        .iter()
        .find(|t| t["expression"] == expression)
        .unwrap()["id"]
        .clone()
}
