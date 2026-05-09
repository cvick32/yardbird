import { useEffect, useState } from "react";
import { useNavigate, useParams } from "react-router-dom";
import { api } from "../api";
import type { BenchmarkSummary } from "../types";

export default function BenchmarkList() {
  const [benchmarks, setBenchmarks] = useState<BenchmarkSummary[]>([]);
  const [search, setSearch] = useState("");
  const [filterSuccess, setFilterSuccess] = useState<string>("all");
  const [filterCost, setFilterCost] = useState<string>("all");
  const [loading, setLoading] = useState(true);
  const navigate = useNavigate();
  const { benchmarkName } = useParams();

  useEffect(() => {
    api.benchmarks().then((data) => {
      setBenchmarks(data);
      setLoading(false);
    });
  }, []);

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

  if (loading) return <div className="pane pane-left">Loading...</div>;

  return (
    <div className="pane pane-left">
      <h2>Benchmarks</h2>
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
            onClick={() => navigate(`/benchmarks/${encodeURIComponent(b.name)}`)}
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
    </div>
  );
}
