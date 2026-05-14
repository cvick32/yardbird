import { useEffect, useState, Fragment } from "react";
import { api } from "../api";
import type { Decision, Candidate, TrainingDatabaseId } from "../types";

function CandidateList({
  runId,
  decisionId,
  database,
}: {
  runId: number;
  decisionId: number;
  database: TrainingDatabaseId;
}) {
  const [candidateState, setCandidateState] = useState<{
    runId: number;
    decisionId: number;
    database: TrainingDatabaseId;
    candidates: Candidate[];
  } | null>(null);

  useEffect(() => {
    api.candidates(runId, decisionId, database).then((data) => {
      setCandidateState({
        runId,
        decisionId,
        database,
        candidates: data,
      });
    });
  }, [runId, decisionId, database]);

  const candidates =
    candidateState?.runId === runId &&
    candidateState.decisionId === decisionId &&
    candidateState.database === database
      ? candidateState.candidates
      : null;

  if (!candidates)
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
  database,
}: {
  decisions: Decision[];
  runId: number;
  database: TrainingDatabaseId;
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
                <CandidateList
                  runId={runId}
                  decisionId={d.id}
                  database={database}
                />
              )}
            </Fragment>
          ))}
        </tbody>
      </table>
    </div>
  );
}
