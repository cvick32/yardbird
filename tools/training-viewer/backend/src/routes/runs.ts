import { Router } from "express";
import pool from "../db.js";

const router = Router();

// GET /api/runs/:id/summary
router.get("/:id/summary", async (req, res) => {
  try {
    const id = req.params.id;

    const benchmarkRes = await pool.query(
      `SELECT * FROM benchmarks WHERE id = $1`,
      [id],
    );
    if (benchmarkRes.rows.length === 0) {
      res.status(404).json({ error: "Run not found" });
      return;
    }

    const countsRes = await pool.query(
      `
      SELECT
        (SELECT COUNT(*)::int FROM decisions WHERE benchmark_id = $1) AS decision_count,
        (SELECT COUNT(*)::int FROM candidates WHERE decision_id IN (SELECT id FROM decisions WHERE benchmark_id = $1)) AS candidate_count,
        (SELECT COUNT(*)::int FROM abstract_instantiations WHERE benchmark_id = $1) AS abstract_count,
        (SELECT COUNT(*)::int FROM abstract_instantiations WHERE benchmark_id = $1 AND in_unsat_core) AS abstract_core_count,
        (SELECT COUNT(*)::int FROM indexed_instantiations WHERE benchmark_id = $1) AS indexed_count,
        (SELECT COUNT(*)::int FROM indexed_instantiations WHERE benchmark_id = $1 AND in_unsat_core) AS indexed_core_count,
        (SELECT COUNT(*)::int FROM core_appearances WHERE benchmark_id = $1) AS core_appearance_count
      `,
      [id],
    );

    res.json({
      benchmark: benchmarkRes.rows[0],
      counts: countsRes.rows[0],
    });
  } catch (err) {
    console.error("GET /api/runs/:id/summary error:", err);
    res.status(500).json({ error: "Internal server error" });
  }
});

// GET /api/runs/:id/decisions
router.get("/:id/decisions", async (req, res) => {
  try {
    const { rows } = await pool.query(
      `
      SELECT
        d.id, d.decision_key, d.bmc_depth, d.axiom_name, d.slot_index, d.created_at,
        COUNT(c.id)::int AS candidate_count,
        COUNT(c.id) FILTER (WHERE c.was_chosen)::int AS chosen_count,
        (COUNT(c.id) FILTER (WHERE c.was_chosen) != 1) AS has_bad_decision_shape
      FROM decisions d
      LEFT JOIN candidates c ON c.decision_id = d.id
      WHERE d.benchmark_id = $1
      GROUP BY d.id
      ORDER BY d.bmc_depth, d.id
      `,
      [req.params.id],
    );
    res.json(rows);
  } catch (err) {
    console.error("GET /api/runs/:id/decisions error:", err);
    res.status(500).json({ error: "Internal server error" });
  }
});

// GET /api/runs/:id/decisions/:decisionId/candidates
router.get("/:id/decisions/:decisionId/candidates", async (req, res) => {
  try {
    const { rows } = await pool.query(
      `
      SELECT * FROM candidates
      WHERE decision_id = $1
      ORDER BY was_chosen DESC, current_cost ASC
      `,
      [req.params.decisionId],
    );
    res.json(rows);
  } catch (err) {
    console.error("GET candidates error:", err);
    res.status(500).json({ error: "Internal server error" });
  }
});

// GET /api/runs/:id/abstract-instantiations
router.get("/:id/abstract-instantiations", async (req, res) => {
  try {
    const { rows } = await pool.query(
      `
      SELECT
        ai.*,
        (SELECT COUNT(*)::int FROM abstract_instantiation_decisions aid
         WHERE aid.abstract_instantiation_id = ai.id) AS decision_link_count
      FROM abstract_instantiations ai
      WHERE ai.benchmark_id = $1
      ORDER BY ai.bmc_depth, ai.refinement_step
      `,
      [req.params.id],
    );
    res.json(rows);
  } catch (err) {
    console.error("GET abstract-instantiations error:", err);
    res.status(500).json({ error: "Internal server error" });
  }
});

// GET /api/runs/:id/indexed-instantiations
router.get("/:id/indexed-instantiations", async (req, res) => {
  try {
    const { rows } = await pool.query(
      `
      SELECT
        ii.*,
        (ii.abstract_instantiation_db_id IS NOT NULL) AS has_abstract_link
      FROM indexed_instantiations ii
      WHERE ii.benchmark_id = $1
      ORDER BY ii.depth, ii.unroll_index
      `,
      [req.params.id],
    );
    res.json(rows);
  } catch (err) {
    console.error("GET indexed-instantiations error:", err);
    res.status(500).json({ error: "Internal server error" });
  }
});

// GET /api/runs/:id/provenance
router.get("/:id/provenance", async (req, res) => {
  try {
    const { rows } = await pool.query(
      `
      SELECT
        d.id AS decision_id, d.axiom_name, d.bmc_depth AS decision_depth, d.slot_index,
        ai.id AS abstract_id, ai.term AS abstract_term, ai.in_unsat_core AS abstract_in_core,
        ai.axiom_name AS abstract_axiom, ai.bmc_depth AS abstract_depth, ai.refinement_step,
        ii.id AS indexed_id, ii.term AS indexed_term, ii.in_unsat_core AS indexed_in_core,
        ii.depth AS indexed_depth, ii.label AS indexed_label
      FROM decisions d
      JOIN abstract_instantiation_decisions aid ON aid.decision_id = d.id
      JOIN abstract_instantiations ai ON ai.id = aid.abstract_instantiation_id
      LEFT JOIN indexed_instantiations ii ON ii.abstract_instantiation_db_id = ai.id
      WHERE d.benchmark_id = $1
      ORDER BY d.bmc_depth, d.id, ai.id, ii.depth
      `,
      [req.params.id],
    );
    res.json(rows);
  } catch (err) {
    console.error("GET provenance error:", err);
    res.status(500).json({ error: "Internal server error" });
  }
});

export default router;
