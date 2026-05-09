import type { ProvenanceRow } from "../types";

export default function ProvenanceView({ rows }: { rows: ProvenanceRow[] }) {
  // Group by decision
  const grouped = new Map<
    number,
    { decision: ProvenanceRow; abstracts: Map<number, { abstract: ProvenanceRow; indexed: ProvenanceRow[] }> }
  >();

  for (const row of rows) {
    if (!grouped.has(row.decision_id)) {
      grouped.set(row.decision_id, { decision: row, abstracts: new Map() });
    }
    const entry = grouped.get(row.decision_id)!;
    if (!entry.abstracts.has(row.abstract_id)) {
      entry.abstracts.set(row.abstract_id, { abstract: row, indexed: [] });
    }
    if (row.indexed_id != null) {
      entry.abstracts.get(row.abstract_id)!.indexed.push(row);
    }
  }

  if (rows.length === 0) {
    return <div className="empty">No provenance data for this run</div>;
  }

  return (
    <div className="provenance-view">
      {[...grouped.entries()].map(([decId, { decision, abstracts }]) => (
        <div key={decId} className="provenance-group">
          <div className="provenance-decision">
            <strong>Decision {decId}</strong>: {decision.axiom_name} @ depth{" "}
            {decision.decision_depth}, slot {decision.slot_index}
          </div>
          {[...abstracts.entries()].map(
            ([absId, { abstract: abs, indexed }]) => (
              <div key={absId} className="provenance-abstract">
                <div
                  className={`provenance-abstract-header ${abs.abstract_in_core ? "in-core" : ""}`}
                >
                  Abstract {absId}: {abs.abstract_axiom} @ depth{" "}
                  {abs.abstract_depth}, refine {abs.refinement_step}
                  {abs.abstract_in_core && (
                    <span className="core-badge">CORE</span>
                  )}
                </div>
                <div className="term-cell provenance-term">
                  {abs.abstract_term}
                </div>
                {indexed.length > 0 && (
                  <div className="provenance-indexed-list">
                    {indexed.map((ix) => (
                      <div
                        key={ix.indexed_id}
                        className={`provenance-indexed ${ix.indexed_in_core ? "in-core" : ""}`}
                      >
                        <span className="indexed-label">
                          {ix.indexed_label}
                        </span>{" "}
                        depth {ix.indexed_depth}
                        {ix.indexed_in_core && (
                          <span className="core-badge">CORE</span>
                        )}
                        <div className="term-cell">{ix.indexed_term}</div>
                      </div>
                    ))}
                  </div>
                )}
              </div>
            ),
          )}
        </div>
      ))}
    </div>
  );
}
