import { useEffect, useState } from "react";
import { useParams, useNavigate } from "react-router-dom";
import { api } from "../api";
import type {
  RunDetail as RunDetailType,
  Decision,
  AbstractInstantiation,
  IndexedInstantiation,
  ProvenanceRow,
} from "../types";
import DecisionTable from "./DecisionTable";
import AbstractTable from "./AbstractTable";
import IndexedTable from "./IndexedTable";
import ProvenanceView from "./ProvenanceView";

type Tab = "decisions" | "abstract" | "indexed" | "provenance";

export default function RunDetail() {
  const { runId, benchmarkName } = useParams();
  const navigate = useNavigate();
  const [detail, setDetail] = useState<RunDetailType | null>(null);
  const [tab, setTab] = useState<Tab>("decisions");
  const [decisions, setDecisions] = useState<Decision[] | null>(null);
  const [abstracts, setAbstracts] = useState<AbstractInstantiation[] | null>(null);
  const [indexed, setIndexed] = useState<IndexedInstantiation[] | null>(null);
  const [provenance, setProvenance] = useState<ProvenanceRow[] | null>(null);
  const [loading, setLoading] = useState(false);

  const id = runId ? parseInt(runId) : null;

  useEffect(() => {
    if (id == null) return;
    setLoading(true);
    setDecisions(null);
    setAbstracts(null);
    setIndexed(null);
    setProvenance(null);
    api.runSummary(id).then((data) => {
      setDetail(data);
      setLoading(false);
    });
  }, [id]);

  // Load tab data on demand
  useEffect(() => {
    if (id == null) return;
    if (tab === "decisions" && decisions == null) {
      api.decisions(id).then(setDecisions);
    } else if (tab === "abstract" && abstracts == null) {
      api.abstractInstantiations(id).then(setAbstracts);
    } else if (tab === "indexed" && indexed == null) {
      api.indexedInstantiations(id).then(setIndexed);
    } else if (tab === "provenance" && provenance == null) {
      api.provenance(id).then(setProvenance);
    }
  }, [id, tab, decisions, abstracts, indexed, provenance]);

  const goBack = () => {
    if (benchmarkName) {
      navigate(`/benchmarks/${encodeURIComponent(benchmarkName)}`);
    }
  };

  if (loading || !detail) {
    return (
      <div className="pane pane-right">
        <div className="detail-header">
          <button className="back-btn" onClick={goBack}>&larr; Runs</button>
        </div>
        Loading run detail...
      </div>
    );
  }

  const { benchmark, counts } = detail;
  const formatTime = (ms: number | null) => {
    if (ms == null) return "-";
    if (ms < 1000) return `${ms}ms`;
    return `${(ms / 1000).toFixed(1)}s`;
  };

  return (
    <div className="pane pane-right">
      <div className="detail-header">
        <button className="back-btn" onClick={goBack}>&larr; Runs</button>
        <h2>Run #{benchmark.id}</h2>
      </div>
      <div className="summary-cards">
        <div className="card">
          <div className="card-label">Cost Function</div>
          <div className="card-value">{benchmark.cost_function}</div>
        </div>
        <div className="card">
          <div className="card-label">Success</div>
          <div className="card-value">
            {benchmark.success === true
              ? "Yes"
              : benchmark.success === false
                ? "No"
                : "-"}
          </div>
        </div>
        <div className="card">
          <div className="card-label">Refinements</div>
          <div className="card-value">
            {benchmark.total_refinements ?? "-"}
          </div>
        </div>
        <div className="card">
          <div className="card-label">Time</div>
          <div className="card-value">
            {formatTime(benchmark.total_time_ms)}
          </div>
        </div>
        <div className="card">
          <div className="card-label">Decisions</div>
          <div className="card-value">{counts.decision_count}</div>
        </div>
        <div className="card">
          <div className="card-label">Candidates</div>
          <div className="card-value">{counts.candidate_count}</div>
        </div>
        <div className="card">
          <div className="card-label">Abstract</div>
          <div className="card-value">
            {counts.abstract_count}
            {counts.abstract_core_count > 0 && (
              <span className="core-count">
                {" "}
                ({counts.abstract_core_count} core)
              </span>
            )}
          </div>
        </div>
        <div className="card">
          <div className="card-label">Indexed</div>
          <div className="card-value">
            {counts.indexed_count}
            {counts.indexed_core_count > 0 && (
              <span className="core-count">
                {" "}
                ({counts.indexed_core_count} core)
              </span>
            )}
          </div>
        </div>
        <div className="card">
          <div className="card-label">Core Terms</div>
          <div className="card-value">{counts.core_appearance_count}</div>
        </div>
      </div>

      <div className="tabs">
        <button
          className={tab === "decisions" ? "tab active" : "tab"}
          onClick={() => setTab("decisions")}
        >
          Decisions
        </button>
        <button
          className={tab === "abstract" ? "tab active" : "tab"}
          onClick={() => setTab("abstract")}
        >
          Abstract
        </button>
        <button
          className={tab === "indexed" ? "tab active" : "tab"}
          onClick={() => setTab("indexed")}
        >
          Indexed
        </button>
        <button
          className={tab === "provenance" ? "tab active" : "tab"}
          onClick={() => setTab("provenance")}
        >
          Provenance
        </button>
      </div>

      <div className="tab-content">
        {tab === "decisions" &&
          (decisions ? (
            <DecisionTable decisions={decisions} runId={id!} />
          ) : (
            "Loading..."
          ))}
        {tab === "abstract" &&
          (abstracts ? <AbstractTable rows={abstracts} /> : "Loading...")}
        {tab === "indexed" &&
          (indexed ? <IndexedTable rows={indexed} /> : "Loading...")}
        {tab === "provenance" &&
          (provenance ? (
            <ProvenanceView rows={provenance} />
          ) : (
            "Loading..."
          ))}
      </div>
    </div>
  );
}
