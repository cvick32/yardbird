import express from "express";
import cors from "cors";
import benchmarksRouter from "./routes/benchmarks.js";
import runsRouter from "./routes/runs.js";

const app = express();
const port = process.env.PORT || 3001;

app.use(cors());
app.use(express.json());

app.use("/api/benchmarks", benchmarksRouter);
app.use("/api/runs", runsRouter);

app.listen(port, () => {
  console.log(`Backend listening on http://localhost:${port}`);
});
