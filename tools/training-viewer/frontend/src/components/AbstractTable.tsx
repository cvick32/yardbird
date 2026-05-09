import type { AbstractInstantiation } from "../types";

export default function AbstractTable({
  rows,
}: {
  rows: AbstractInstantiation[];
}) {
  return (
    <div className="table-scroll">
      <table>
        <thead>
          <tr>
            <th>Depth</th>
            <th>Refine</th>
            <th>Axiom</th>
            <th>Term</th>
            <th>Core</th>
            <th>Decisions</th>
          </tr>
        </thead>
        <tbody>
          {rows.map((r) => (
            <tr key={r.id} className={r.in_unsat_core ? "in-core" : ""}>
              <td>{r.bmc_depth}</td>
              <td>{r.refinement_step}</td>
              <td>{r.axiom_name}</td>
              <td className="term-cell" title={r.term}>
                {r.term}
              </td>
              <td>{r.in_unsat_core ? "Y" : ""}</td>
              <td>{r.decision_link_count}</td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
}
