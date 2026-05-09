import { useEffect, useState, Fragment } from "react";
import { api } from "../api";
import type { Decision, Candidate } from "../types";

function CandidateList({
  runId,
  decisionId,
}: {
  runId: number;
  decisionId: number;
}) {
  const [candidates, setCandidates] = useState<Candidate[] | null>(null);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    api.candidates(runId, decisionId).then((data) => {
      setCandidates(data);
      setLoading(false);
    });
  }, [runId, decisionId]);

  if (loading || !candidates)
    return (
      <tr>
        <td colSpan={6}>Loading candidates...</td>
      </tr>
    );

  return (
    <tr className="candidate-header">
      <td colSpan={6}>
        <table className="candidate-table">
          <thead>
            <tr>
              <th>Term</th>
              <th>Cost</th>
              <th>AST</th>
              <th>Chosen</th>
              <th>Const</th>
              <th>Var</th>
              <th>Prop</th>
              <th>Trans</th>
              <th>Frame</th>
            </tr>
          </thead>
          <tbody>
            {candidates.map((c) => (
              <tr
                key={c.id}
                className={c.was_chosen ? "chosen-candidate" : ""}
              >
                <td className="term-cell" title={c.term}>
                  {c.term}
                </td>
                <td>{c.current_cost}</td>
                <td>{c.ast_size}</td>
                <td>{c.was_chosen ? "Y" : ""}</td>
                <td>{c.is_constant ? "Y" : ""}</td>
                <td>{c.is_variable ? "Y" : ""}</td>
                <td>{c.in_property_vocab ? "Y" : ""}</td>
                <td>{c.in_transition_vocab ? "Y" : ""}</td>
                <td>{c.frame_index ?? ""}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </td>
    </tr>
  );
}

export default function DecisionTable({
  decisions,
  runId,
}: {
  decisions: Decision[];
  runId: number;
}) {
  const [expandedId, setExpandedId] = useState<number | null>(null);

  return (
    <div className="table-scroll">
      <table>
        <thead>
          <tr>
            <th>Depth</th>
            <th>Axiom</th>
            <th>Slot</th>
            <th>Candidates</th>
            <th>Chosen</th>
            <th>Key</th>
          </tr>
        </thead>
        <tbody>
          {decisions.map((d) => (
            <Fragment key={d.id}>
              <tr
                className={`clickable ${d.has_bad_decision_shape ? "bad-shape" : ""}`}
                onClick={() =>
                  setExpandedId(expandedId === d.id ? null : d.id)
                }
              >
                <td>{d.bmc_depth}</td>
                <td>{d.axiom_name}</td>
                <td>{d.slot_index}</td>
                <td>{d.candidate_count}</td>
                <td>{d.chosen_count}</td>
                <td className="term-cell">{d.decision_key ?? ""}</td>
              </tr>
              {expandedId === d.id && (
                <CandidateList runId={runId} decisionId={d.id} />
              )}
            </Fragment>
          ))}
        </tbody>
      </table>
    </div>
  );
}
