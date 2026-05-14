import { useEffect, useState } from "react";
import { useParams, useNavigate } from "react-router-dom";
import { api } from "../api";
import { useTrainingDatabase } from "../trainingDatabase";
import type { TrainingDatabaseId } from "../types";
import type { RunSummary } from "../types";

type SortKey = keyof RunSummary;

export default function RunList() {
  const { benchmarkName, runId } = useParams();
  const navigate = useNavigate();
  const [runState, setRunState] = useState<{
    benchmarkName: string | null;
    database: TrainingDatabaseId;
    runs: RunSummary[];
  }>({ benchmarkName: null, database: "local", runs: [] });
  const [sortKey, setSortKey] = useState<SortKey>("created_at");
  const [sortAsc, setSortAsc] = useState(false);
  const { selectedDatabase } = useTrainingDatabase();

  useEffect(() => {
    if (!benchmarkName) return;
    api.runs(benchmarkName, selectedDatabase).then((data) => {
      setRunState({ benchmarkName, database: selectedDatabase, runs: data });
    });
  }, [benchmarkName, selectedDatabase]);

  if (!benchmarkName) {
    return (
      <div className="pane pane-middle">
        <div className="empty">Select a benchmark</div>
      </div>
    );
  }

  const handleSort = (key: SortKey) => {
    if (key === sortKey) setSortAsc(!sortAsc);
    else {
      setSortKey(key);
      setSortAsc(true);
    }
  };

  const loading =
    benchmarkName != null &&
    (runState.benchmarkName !== benchmarkName ||
      runState.database !== selectedDatabase);
  const runs = loading ? [] : runState.runs;

  const sorted = [...runs].sort((a, b) => {
    const av = a[sortKey];
    const bv = b[sortKey];
    if (av == null && bv == null) return 0;
    if (av == null) return 1;
    if (bv == null) return -1;
    const cmp = av < bv ? -1 : av > bv ? 1 : 0;
    return sortAsc ? cmp : -cmp;
  });

  const formatTime = (ms: number | null) => {
    if (ms == null) return "-";
    if (ms < 1000) return `${ms}ms`;
    return `${(ms / 1000).toFixed(1)}s`;
  };

  const sortIndicator = (key: SortKey) =>
    sortKey === key ? (sortAsc ? " ^" : " v") : "";

  if (loading) return <div className="pane pane-middle">Loading runs...</div>;

  return (
    <div className="pane pane-middle">
      <h2 title={benchmarkName}>{benchmarkName.split("/").pop()}</h2>
      <div className="run-count">{runs.length} runs</div>
      <div className="table-scroll">
        <table>
          <thead>
            <tr>
              <th onClick={() => handleSort("cost_function")}>
                Cost Fn{sortIndicator("cost_function")}
              </th>
              <th onClick={() => handleSort("success")}>
                OK{sortIndicator("success")}
              </th>
              <th onClick={() => handleSort("total_refinements")}>
                Refine{sortIndicator("total_refinements")}
              </th>
              <th onClick={() => handleSort("total_time_ms")}>
                Time{sortIndicator("total_time_ms")}
              </th>
              <th onClick={() => handleSort("decision_count")}>
                Dec{sortIndicator("decision_count")}
              </th>
              <th onClick={() => handleSort("abstract_count")}>
                Abs{sortIndicator("abstract_count")}
              </th>
              <th onClick={() => handleSort("indexed_count")}>
                Idx{sortIndicator("indexed_count")}
              </th>
              <th onClick={() => handleSort("core_pct")}>
                Core %{sortIndicator("core_pct")}
              </th>
            </tr>
          </thead>
          <tbody>
            {sorted.map((r) => (
              <tr
                key={r.id}
                className={`clickable ${String(r.id) === runId ? "active" : ""}`}
                onClick={() =>
                  navigate(
                    `/benchmarks/${encodeURIComponent(benchmarkName)}/runs/${r.id}`,
                  )
                }
              >
                <td>
                  <span className="tag">{r.cost_function}</span>
                </td>
                <td>
                  {r.success === true
                    ? "Y"
                    : r.success === false
                      ? "N"
                      : "-"}
                </td>
                <td>{r.total_refinements ?? "-"}</td>
                <td>{formatTime(r.total_time_ms)}</td>
                <td>{r.decision_count}</td>
                <td>{r.abstract_count}</td>
                <td>{r.indexed_count}</td>
                <td>{r.core_pct != null ? `${r.core_pct}%` : "-"}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </div>
  );
}
