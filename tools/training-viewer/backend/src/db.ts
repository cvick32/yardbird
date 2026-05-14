import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import type { NextFunction, Request, Response } from "express";
import pg, { type QueryResult, type QueryResultRow } from "pg";

export type TrainingDatabaseId = "local" | "lab";

export interface TrainingDatabaseOption {
  id: TrainingDatabaseId;
  label: string;
  configured: boolean;
}

declare global {
  namespace Express {
    interface Request {
      trainingDatabase?: TrainingDatabaseId;
    }
  }
}

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.resolve(__dirname, "../../../../");

function loadRepoEnv(): void {
  try {
    const envFile = readFileSync(path.join(REPO_ROOT, ".env"), "utf8");
    for (const line of envFile.split(/\r?\n/)) {
      const match = /^(?:export\s+)?([A-Za-z_][A-Za-z0-9_]*)=(.*)$/.exec(
        line.trim(),
      );
      if (!match || process.env[match[1]] != null) continue;

      let value = match[2].trim();
      const quote = value[0];
      if (
        (quote === "\"" || quote === "'") &&
        value[value.length - 1] === quote
      ) {
        value = value.slice(1, -1);
      } else {
        value = value.replace(/\s+#.*$/, "");
      }
      process.env[match[1]] = value;
    }
  } catch (err) {
    if (
      typeof err === "object" &&
      err !== null &&
      "code" in err &&
      err.code === "ENOENT"
    ) {
      return;
    }
    console.warn("Unable to load repository .env:", err);
  }
}

loadRepoEnv();

const databaseConfig: Record<
  TrainingDatabaseId,
  { label: string; connectionString?: string }
> = {
  local: {
    label: "Local yardbird",
    connectionString:
      process.env.YARDBIRD_DATABASE_URL || process.env.DATABASE_URL,
  },
  lab: {
    label: "Lab training",
    connectionString: process.env.LAB_DATABASE_URL,
  },
};

const pools = new Map<TrainingDatabaseId, pg.Pool>();

class DatabaseSelectionError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "DatabaseSelectionError";
  }
}

function parseDatabaseId(value: unknown): TrainingDatabaseId {
  const requested = Array.isArray(value) ? value[0] : value;
  if (requested == null || requested === "") return "local";
  if (requested === "local" || requested === "lab") return requested;
  throw new DatabaseSelectionError("db must be local or lab");
}

function databaseIdFromRequest(req: Request): TrainingDatabaseId {
  const databaseId = parseDatabaseId(
    req.query.db ?? req.header("x-training-database"),
  );
  if (!databaseConfig[databaseId].connectionString) {
    throw new DatabaseSelectionError(
      `${databaseConfig[databaseId].label} database is not configured`,
    );
  }
  return databaseId;
}

function poolForDatabase(databaseId: TrainingDatabaseId): pg.Pool {
  const existing = pools.get(databaseId);
  if (existing) return existing;

  const config = databaseConfig[databaseId];
  if (!config.connectionString) {
    throw new DatabaseSelectionError(
      `${config.label} database is not configured`,
    );
  }

  const pool = new pg.Pool({
    connectionString: config.connectionString,
    max: 5,
  });
  pool.on("error", (err) => {
    console.error(`${config.label} database pool error:`, err);
  });
  pools.set(databaseId, pool);
  return pool;
}

export function getTrainingDatabaseOptions(): TrainingDatabaseOption[] {
  return (Object.keys(databaseConfig) as TrainingDatabaseId[]).map((id) => ({
    id,
    label: databaseConfig[id].label,
    configured: Boolean(databaseConfig[id].connectionString),
  }));
}

export function trainingDatabaseMiddleware(
  req: Request,
  res: Response,
  next: NextFunction,
): void {
  try {
    req.trainingDatabase = databaseIdFromRequest(req);
    next();
  } catch (err) {
    const message = err instanceof Error ? err.message : String(err);
    res.status(400).json({ error: message });
  }
}

export function queryForRequest<T extends QueryResultRow = QueryResultRow>(
  req: Request,
  text: string,
  values?: unknown[],
): Promise<QueryResult<T>> {
  const databaseId = req.trainingDatabase ?? databaseIdFromRequest(req);
  return poolForDatabase(databaseId).query<T>(text, values);
}
