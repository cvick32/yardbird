"""Small Typst rendering helpers shared by report sections."""

from __future__ import annotations

import json


def typst_cell(value: object, *, bold: bool = False) -> str:
    weight = 'weight: "bold", ' if bold else ""
    encoded = json.dumps(str(value), ensure_ascii=False)
    return f"[#text({weight}{encoded})]"


def typst_table(
    headers: list[str],
    rows: list[list[object]],
    *,
    columns: str,
    size: str = "8pt",
) -> str:
    lines = [
        f"#text(size: {size})[",
        "  #table(",
        f"    columns: {columns},",
        "    inset: (x: 4pt, y: 3pt),",
        "    stroke: 0.3pt + luma(205),",
        "    table.header(",
    ]
    lines.extend(f"      {typst_cell(header, bold=True)}," for header in headers)
    lines.extend(["    ),"])
    for row in rows:
        lines.extend(f"    {typst_cell(value)}," for value in row)
    lines.extend(["  )", "]"])
    return "\n".join(lines)
