import { execFile } from "node:child_process";
import { readFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { promisify } from "node:util";
import { Router } from "express";

const execFileAsync = promisify(execFile);
const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.resolve(__dirname, "../../../../../");
const MAIN_EVAL = path.join(REPO_ROOT, "main_eval.py");
const MAIN_EVAL_ROOT = path.join(REPO_ROOT, "benchmark_results", "main_eval");
const RUNS_INDEX = path.join(MAIN_EVAL_ROOT, "runs_index.json");

const router = Router();

type EvalEnvironment = "local" | "aws" | "lab";

interface LaunchLabOptions {
  proxmoxApiUrl?: string;
  proxmoxTokenId?: string;
  proxmoxTokenSecret?: string;
  proxmoxNode?: string;
  proxmoxInsecure?: boolean;
  workerTemplate?: string;
  workerUser?: string;
  workerSshKey?: string;
  workerSshPublicKey?: string;
  r2Bucket?: string;
  r2EndpointUrl?: string;
  r2Region?: string;
  r2Prefix?: string;
  keepVms?: boolean;
}

interface LaunchRequest {
  env: EvalEnvironment;
  benchmarkTypes: string[];
  name?: string;
  config?: string;
  lab?: LaunchLabOptions;
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null;
}

function parseLaunchRequest(body: unknown): LaunchRequest {
  if (!isRecord(body)) {
    throw new Error("Request body must be an object");
  }
  const env = body.env;
  if (env !== "local" && env !== "aws" && env !== "lab") {
    throw new Error("env must be local, aws, or lab");
  }
  const benchmarkTypes = body.benchmarkTypes;
  if (
    !Array.isArray(benchmarkTypes) ||
    benchmarkTypes.length === 0 ||
    !benchmarkTypes.every((item) => typeof item === "string" && item.trim())
  ) {
    throw new Error("benchmarkTypes must be a non-empty string array");
  }

  const lab = isRecord(body.lab) ? body.lab : {};
  return {
    env,
    benchmarkTypes: benchmarkTypes.map((item) => item.trim()),
    name: typeof body.name === "string" && body.name.trim() ? body.name.trim() : undefined,
    config:
      typeof body.config === "string" && body.config.trim()
        ? body.config.trim()
        : undefined,
    lab: {
      proxmoxApiUrl: stringValue(lab.proxmoxApiUrl),
      proxmoxTokenId: stringValue(lab.proxmoxTokenId),
      proxmoxTokenSecret: stringValue(lab.proxmoxTokenSecret),
      proxmoxNode: stringValue(lab.proxmoxNode),
      proxmoxInsecure: lab.proxmoxInsecure === true,
      workerTemplate: stringValue(lab.workerTemplate),
      workerUser: stringValue(lab.workerUser),
      workerSshKey: stringValue(lab.workerSshKey),
      workerSshPublicKey: stringValue(lab.workerSshPublicKey),
      r2Bucket: stringValue(lab.r2Bucket),
      r2EndpointUrl: stringValue(lab.r2EndpointUrl),
      r2Region: stringValue(lab.r2Region),
      r2Prefix: stringValue(lab.r2Prefix),
      keepVms: lab.keepVms === true,
    },
  };
}

function stringValue(value: unknown): string | undefined {
  return typeof value === "string" && value.trim() ? value.trim() : undefined;
}

function validateRunId(runId: string): void {
  if (!/^[A-Za-z0-9_.-]+$/.test(runId)) {
    throw new Error("Invalid run id");
  }
}

function manifestPath(runId: string): string {
  validateRunId(runId);
  return path.join(MAIN_EVAL_ROOT, runId, "run.json");
}

async function readJsonFile(filePath: string): Promise<unknown> {
  const raw = await readFile(filePath, "utf8");
  return JSON.parse(raw);
}

async function readManifest(runId: string): Promise<unknown> {
  return readJsonFile(manifestPath(runId));
}

function addOptionalArg(args: string[], flag: string, value: string | undefined): void {
  if (value) args.push(flag, value);
}

function launchArgs(request: LaunchRequest): string[] {
  const args = ["--env", request.env];
  for (const benchmarkType of request.benchmarkTypes) {
    args.push("--benchmark-type", benchmarkType);
  }
  addOptionalArg(args, "--name", request.name);
  addOptionalArg(args, "--config", request.config);

  if (request.env === "lab") {
    const lab = request.lab ?? {};
    addOptionalArg(args, "--lab-proxmox-api-url", lab.proxmoxApiUrl);
    addOptionalArg(args, "--lab-proxmox-token-id", lab.proxmoxTokenId);
    addOptionalArg(args, "--lab-proxmox-token-secret", lab.proxmoxTokenSecret);
    addOptionalArg(args, "--lab-proxmox-node", lab.proxmoxNode);
    addOptionalArg(args, "--lab-worker-template", lab.workerTemplate);
    addOptionalArg(args, "--lab-worker-user", lab.workerUser);
    addOptionalArg(args, "--lab-worker-ssh-key", lab.workerSshKey);
    addOptionalArg(args, "--lab-worker-ssh-public-key", lab.workerSshPublicKey);
    addOptionalArg(args, "--lab-r2-bucket", lab.r2Bucket);
    addOptionalArg(args, "--lab-r2-endpoint-url", lab.r2EndpointUrl);
    addOptionalArg(args, "--lab-r2-region", lab.r2Region);
    addOptionalArg(args, "--lab-r2-prefix", lab.r2Prefix);
    if (lab.proxmoxInsecure) args.push("--lab-proxmox-insecure");
    if (lab.keepVms) args.push("--lab-keep-vms");
  }

  return args;
}

async function runMainEval(args: string[]) {
  const result = await execFileAsync("python3", [MAIN_EVAL, ...args], {
    cwd: REPO_ROOT,
    env: process.env,
    maxBuffer: 20 * 1024 * 1024,
    timeout: 30 * 60 * 1000,
  });
  return {
    stdout: result.stdout,
    stderr: result.stderr,
  };
}

function errorMessage(error: unknown): string {
  if (error instanceof Error) return error.message;
  return String(error);
}

// GET /api/eval-runs
router.get("/", async (_req, res) => {
  try {
    const index = await readJsonFile(RUNS_INDEX).catch(() => ({ runs: [] }));
    res.json(index);
  } catch (err) {
    console.error("GET /api/eval-runs error:", err);
    res.status(500).json({ error: "Internal server error" });
  }
});

// POST /api/eval-runs
router.post("/", async (req, res) => {
  try {
    const request = parseLaunchRequest(req.body);
    const command = await runMainEval(launchArgs(request));
    const index = await readJsonFile(RUNS_INDEX).catch(() => ({ runs: [] }));
    res.status(201).json({ command, index });
  } catch (err) {
    console.error("POST /api/eval-runs error:", err);
    res.status(400).json({ error: errorMessage(err) });
  }
});

// GET /api/eval-runs/:runId
router.get("/:runId", async (req, res) => {
  try {
    res.json(await readManifest(req.params.runId));
  } catch (err) {
    console.error("GET /api/eval-runs/:runId error:", err);
    res.status(404).json({ error: errorMessage(err) });
  }
});

// POST /api/eval-runs/:runId/refresh
router.post("/:runId/refresh", async (req, res) => {
  try {
    validateRunId(req.params.runId);
    const command = await runMainEval(["--run-id", req.params.runId, "--status"]);
    const manifest = await readManifest(req.params.runId);
    res.json({ command, manifest });
  } catch (err) {
    console.error("POST /api/eval-runs/:runId/refresh error:", err);
    res.status(400).json({ error: errorMessage(err) });
  }
});

// POST /api/eval-runs/:runId/download-report
router.post("/:runId/download-report", async (req, res) => {
  try {
    validateRunId(req.params.runId);
    const command = await runMainEval([
      "--run-id",
      req.params.runId,
      "--generate-report",
    ]);
    const manifest = await readManifest(req.params.runId);
    res.json({ command, manifest });
  } catch (err) {
    console.error("POST /api/eval-runs/:runId/download-report error:", err);
    res.status(400).json({ error: errorMessage(err) });
  }
});

// POST /api/eval-runs/:runId/subruns/:subrunIndex/teardown
router.post("/:runId/subruns/:subrunIndex/teardown", async (req, res) => {
  try {
    validateRunId(req.params.runId);
    const subrunIndex = Number(req.params.subrunIndex);
    if (!Number.isInteger(subrunIndex) || subrunIndex < 0) {
      throw new Error("subrunIndex must be a non-negative integer");
    }
    const command = await runMainEval([
      "--run-id",
      req.params.runId,
      "--teardown-subrun-index",
      String(subrunIndex),
    ]);
    const manifest = await readManifest(req.params.runId);
    res.json({ command, manifest });
  } catch (err) {
    console.error("POST /api/eval-runs/:runId/subruns/:subrunIndex/teardown error:", err);
    res.status(400).json({ error: errorMessage(err) });
  }
});

export default router;
