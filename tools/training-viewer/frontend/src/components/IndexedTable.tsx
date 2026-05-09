import type { IndexedInstantiation } from "../types";

export default function IndexedTable({
  rows,
}: {
  rows: IndexedInstantiation[];
}) {
  return (
    <div className="table-scroll">
      <table>
        <thead>
          <tr>
            <th>Depth</th>
            <th>Unroll</th>
            <th>Label</th>
            <th>Term</th>
            <th>Core</th>
            <th>Abstract</th>
          </tr>
        </thead>
        <tbody>
          {rows.map((r) => (
            <tr key={r.id} className={r.in_unsat_core ? "in-core" : ""}>
              <td>{r.depth}</td>
              <td>{r.unroll_index}</td>
              <td>{r.label}</td>
              <td className="term-cell" title={r.term}>
                {r.term}
              </td>
              <td>{r.in_unsat_core ? "Y" : ""}</td>
              <td>{r.has_abstract_link ? "Y" : ""}</td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
}
