import { Router } from "express";
import { queryForRequest } from "../db.js";

const router = Router();

// GET /api/benchmarks
router.get("/", async (_req, res) => {
  try {
    const { rows } = await queryForRequest(_req, `
      SELECT
        name,
        COUNT(*)::int AS run_count,
        MAX(created_at) AS latest_run,
        COUNT(*) FILTER (WHERE success = true)::int AS success_count,
        COUNT(*) FILTER (WHERE success = false)::int AS failure_count,
        ARRAY_AGG(DISTINCT cost_function) AS cost_functions
      FROM benchmarks
      GROUP BY name
      ORDER BY MAX(created_at) DESC
    `);
    res.json(rows);
  } catch (err) {
    console.error("GET /api/benchmarks error:", err);
    res.status(500).json({ error: "Internal server error" });
  }
});

// GET /api/benchmarks/:name/runs
router.get("/:name/runs", async (req, res) => {
  try {
    const { rows } = await queryForRequest(
      req,
      `
      SELECT
        b.id, b.cost_function, b.success, b.total_refinements, b.total_time_ms, b.created_at,
        (SELECT COUNT(*)::int FROM decisions d WHERE d.benchmark_id = b.id) AS decision_count,
        (SELECT COUNT(*)::int FROM abstract_instantiations ai WHERE ai.benchmark_id = b.id) AS abstract_count,
        (SELECT COUNT(*)::int FROM indexed_instantiations ii WHERE ii.benchmark_id = b.id) AS indexed_count,
        CASE
          WHEN (SELECT COUNT(*) FROM indexed_instantiations ii WHERE ii.benchmark_id = b.id) = 0 THEN NULL
          ELSE ROUND(
            100.0 * (SELECT COUNT(*) FROM indexed_instantiations ii WHERE ii.benchmark_id = b.id AND ii.in_unsat_core)
            / (SELECT COUNT(*) FROM indexed_instantiations ii WHERE ii.benchmark_id = b.id)
          , 1)
        END AS core_pct
      FROM benchmarks b
      WHERE b.name = $1
      ORDER BY b.created_at DESC
      `,
      [req.params.name],
    );
    res.json(rows);
  } catch (err) {
    console.error("GET /api/benchmarks/:name/runs error:", err);
    res.status(500).json({ error: "Internal server error" });
  }
});

export default router;
