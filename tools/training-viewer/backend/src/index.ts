import express from "express";
import cors from "cors";
import benchmarksRouter from "./routes/benchmarks.js";
import {
  getTrainingDatabaseOptions,
  trainingDatabaseMiddleware,
} from "./db.js";
import evalRunsRouter from "./routes/evalRuns.js";
import runsRouter from "./routes/runs.js";

const app = express();
const port = process.env.PORT || 3001;

app.use(cors());
app.use(express.json());

app.get("/api/training-databases", (_req, res) => {
  res.json(getTrainingDatabaseOptions());
});

app.use("/api/benchmarks", trainingDatabaseMiddleware, benchmarksRouter);
app.use("/api/runs", trainingDatabaseMiddleware, runsRouter);
app.use("/api/eval-runs", evalRunsRouter);

app.get("/api/openapi.json", (_req, res) => {
  res.json({
    openapi: "3.1.0",
    info: {
      title: "Yardbird Training Viewer API",
      version: "0.1.0",
    },
    paths: {
      "/api/eval-runs": {
        get: {
          summary: "List main_eval runs",
        },
        post: {
          summary: "Launch a new main_eval run",
        },
      },
      "/api/eval-runs/{runId}": {
        get: {
          summary: "Read a main_eval run manifest",
        },
      },
      "/api/eval-runs/{runId}/refresh": {
        post: {
          summary: "Refresh a run status through main_eval",
        },
      },
      "/api/eval-runs/{runId}/download-report": {
        post: {
          summary: "Download artifacts and generate the report for a completed run",
        },
      },
      "/api/eval-runs/{runId}/subruns/{subrunIndex}/teardown": {
        post: {
          summary: "Destroy one completed or failed lab worker VM",
        },
      },
      "/api/training-databases": {
        get: {
          summary: "List selectable training databases",
        },
      },
    },
    components: {
      schemas: {
        EvalEnvironment: {
          type: "string",
          enum: ["local", "aws", "lab"],
        },
        EvalStatus: {
          type: "string",
          enum: ["RUNNING", "COMPLETED", "FAILED"],
        },
      },
    },
  });
});

app.listen(port, () => {
  console.log(`Backend listening on http://localhost:${port}`);
});
