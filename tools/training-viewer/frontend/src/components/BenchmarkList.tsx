import { useEffect, useState } from "react";
import { useNavigate, useParams } from "react-router-dom";
import { api } from "../api";
import { useTrainingDatabase } from "../trainingDatabase";
import type { BenchmarkSummary, TrainingDatabaseId } from "../types";

export default function BenchmarkList() {
  const [benchmarkState, setBenchmarkState] = useState<{
    database: TrainingDatabaseId | null;
    benchmarks: BenchmarkSummary[];
  }>({ database: null, benchmarks: [] });
  const [search, setSearch] = useState("");
  const [filterSuccess, setFilterSuccess] = useState<string>("all");
  const [filterCost, setFilterCost] = useState<string>("all");
  const navigate = useNavigate();
  const { benchmarkName } = useParams();
  const { selectedDatabase, options, setSelectedDatabase } =
    useTrainingDatabase();

  useEffect(() => {
    let cancelled = false;
    api
      .benchmarks(selectedDatabase)
      .then((data) => {
        if (!cancelled) {
          setBenchmarkState({ database: selectedDatabase, benchmarks: data });
        }
      })
      .catch((err) => {
        console.error("Unable to load benchmarks:", err);
        if (!cancelled) {
          setBenchmarkState({ database: selectedDatabase, benchmarks: [] });
        }
      });
    return () => {
      cancelled = true;
    };
  }, [selectedDatabase]);

  const loading = benchmarkState.database !== selectedDatabase;
  const benchmarks = loading ? [] : benchmarkState.benchmarks;

  const allCostFunctions = [
    ...new Set(benchmarks.flatMap((b) => b.cost_functions)),
  ].sort();

  const filtered = benchmarks.filter((b) => {
    if (search && !b.name.toLowerCase().includes(search.toLowerCase()))
      return false;
    if (filterSuccess === "success" && b.success_count === 0) return false;
    if (filterSuccess === "failure" && b.failure_count === 0) return false;
    if (filterCost !== "all" && !b.cost_functions.includes(filterCost))
      return false;
    return true;
  });

  return (
    <div className="pane pane-left">
      <div className="pane-title-row">
        <h2>Benchmarks</h2>
        <select
          aria-label="Training database"
          className="db-select"
          value={selectedDatabase}
          onChange={(event) =>
            setSelectedDatabase(event.target.value as TrainingDatabaseId)
          }
        >
          {options.map((option) => (
            <option
              key={option.id}
              value={option.id}
              disabled={!option.configured}
            >
              {option.configured
                ? option.label
                : `${option.label} unavailable`}
            </option>
          ))}
        </select>
      </div>
      <button className="nav-link-btn" onClick={() => navigate("/eval-runs")}>
        Eval Runs
      </button>
      {loading ? (
        <div className="empty">Loading...</div>
      ) : (
        <>
          <input
            type="text"
            placeholder="Search benchmarks..."
            value={search}
            onChange={(e) => setSearch(e.target.value)}
            className="search-input"
          />
          <div className="filter-row">
            <select
              value={filterSuccess}
              onChange={(e) => setFilterSuccess(e.target.value)}
            >
              <option value="all">All results</option>
              <option value="success">Has success</option>
              <option value="failure">Has failure</option>
            </select>
            <select
              value={filterCost}
              onChange={(e) => setFilterCost(e.target.value)}
            >
              <option value="all">All cost fns</option>
              {allCostFunctions.map((cf) => (
                <option key={cf} value={cf}>
                  {cf}
                </option>
              ))}
            </select>
          </div>
          <div className="benchmark-list">
            {filtered.map((b) => (
              <div
                key={b.name}
                className={`benchmark-item ${b.name === benchmarkName ? "active" : ""}`}
                onClick={() =>
                  navigate(`/benchmarks/${encodeURIComponent(b.name)}`)
                }
              >
                <div className="benchmark-name" title={b.name}>
                  {b.name.split("/").pop()}
                </div>
                <div className="benchmark-meta">
                  <span>{b.run_count} runs</span>
                  <span className="success-badge">
                    {b.success_count}/{b.run_count}
                  </span>
                  <span className="cost-tags">
                    {b.cost_functions.map((cf) => (
                      <span key={cf} className="tag">
                        {cf}
                      </span>
                    ))}
                  </span>
                </div>
              </div>
            ))}
            {filtered.length === 0 && (
              <div className="empty">No benchmarks match filters</div>
            )}
          </div>
        </>
      )}
    </div>
  );
}
