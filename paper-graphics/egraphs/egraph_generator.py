#!/usr/bin/env python3
"""
Generate a TikZ e-graph diagram (egg-paper style) from JSON.

Usage:
  python make_tikz_egraph.py diagram.json -o out.tex
  python make_tikz_egraph.py diagram.json -o fragment.tex

JSON schema
{
  "nodes": [
    {"id":"mul", "label":"*",  "x":0,   "y":0},
    {"id":"a",   "label":"a",  "x":-1,  "y":-1},
    {"id":"two", "label":"2",  "x":1,   "y":-1},
    {"id":"div", "label":"/",  "x":0,   "y":1.4}
  ],
  "edges": [["a","mul"], ["two","mul"], ["mul","div"]],
  "eclasses": [["a","two","mul"], ["div"]],
  "caption": "(a) Initial e-graph contains $(a\\times2)/2$",
  "scale": 1.0
}


Coordinates are in arbitrary units; tweak with "scale".
"""

import argparse
import json
import sys
from pathlib import Path

PREAMBLE = r"""
\documentclass[tikz,border=5pt]{standalone}
\usepackage{amsmath}
\usepackage{tikz}
\usetikzlibrary{arrows.meta,positioning,fit,calc}
\begin{document}
"""

POSTAMBLE = r"""
\end{document}
"""

# TikZ styles used across diagrams
PICTURE_HEADER = r"""
\begin{tikzpicture}[
  x=1cm, y=1cm,
  >=Latex,
  node/.style={draw, rounded corners, minimum size=4mm, inner sep=2pt},
  ebox/.style={draw, dashed, rounded corners, inner sep=4pt},
  elabel/.style={font=\scriptsize, inner sep=1pt}
]
"""

PICTURE_FOOTER = r"""
\end{tikzpicture}
"""


def tex_escape(s: str) -> str:
    # minimal escaping for node labels/captions
    return (
        s.replace("\\", r"\\")
        .replace("&", r"\&")
        .replace("%", r"\%")
        .replace("#", r"\#")
        .replace("{", r"\{")
        .replace("}", r"\}")
    )


def emit_single_diagram(diag: dict, x_offset_cm: float = 0.0) -> str:
    scale = float(diag.get("scale", 1.0))
    nodes = diag.get("nodes", [])
    edges = diag.get("edges", [])
    eclasses = diag.get("eclasses", [])
    caption = diag.get("caption", "")

    # Map of node id -> tikz coordinate string
    coord = {}
    for n in nodes:
        nid = n["id"]
        x = float(n.get("x", 0.0)) * scale + x_offset_cm
        y = float(n.get("y", 0.0)) * scale
        coord[nid] = f"({x:.4f},{y:.4f})"

    out = []
    out.append(r"\begin{figure}[htbp]")
    out.append(r"\centering")
    out.append(PICTURE_HEADER)

    # Place nodes
    for n in nodes:
        nid = n["id"]
        lbl = tex_escape(n.get("label", nid))
        out.append(rf"\node[node] ({nid}) at {coord[nid]} {{{lbl}}};")

    out.append("")  # spacer

    # E-class dashed boxes using fit
    for i, group in enumerate(eclasses, start=1):
        # Only include nodes that exist
        ids = [g for g in group if g in coord]
        if not ids:
            continue
        inside = " ".join(f"({g})" for g in ids)
        out.append(rf"\node[ebox, fit={inside}] (EClass{i}) {{}};")
        # Add label to bottom right of e-class box, offset outside
        out.append(
            rf"\node[elabel, anchor=north west] at ($(EClass{i}.south west)+(-0.2,0.0)$) {{$E_{{{i}}}$}};"
        )

    out.append("")

    # Edges (arrowed) - connect to eclass borders instead of nodes
    # First, build a mapping from node id to its eclass name
    node_to_eclass = {}
    for i, group in enumerate(eclasses, start=1):
        for node_id in group:
            if node_id in coord:
                node_to_eclass[node_id] = f"EClass{i}"

    for u, v in edges:
        if u in coord and v in coord:
            # Use eclass border if available, otherwise fall back to node
            v_target = node_to_eclass.get(v, v)
            out.append(rf"\draw[->] ({u}) -- ({v_target});")

    out.append(PICTURE_FOOTER)

    # LaTeX figure caption (outside tikzpicture)
    if caption:
        cap = tex_escape(caption)
        out.append(rf"\caption{{{cap}}}")

    out.append(r"\end{figure}")
    return "\n".join(out)


def width_of_panel(diag: dict) -> float:
    """Rough width in cm to offset next panel (bbox-free, uses coord extents)."""
    nodes = diag.get("nodes", [])
    scale = float(diag.get("scale", 1.0))
    if not nodes:
        return 0.0
    xs = [float(n.get("x", 0.0)) * scale for n in nodes]
    w = (max(xs) - min(xs)) if xs else 0.0
    # add padding for ebox + arrowheads
    return max(w + 3.0, 4.0)


def main():
    ap = argparse.ArgumentParser(
        description="Generate a TikZ e-graph diagram from JSON."
    )
    ap.add_argument("json_file", help="Input JSON file (single diagram or panels).")
    ap.add_argument("-o", "--output", help="Output .tex file (default: stdout).")
    args = ap.parse_args()

    data = json.loads(Path(args.json_file).read_text())
    content = emit_single_diagram(data, x_offset_cm=0.0)
    content = content.replace("\\\\", "\\")

    if args.output:
        Path(args.output).write_text(content)
    else:
        sys.stdout.write(content)


if __name__ == "__main__":
    main()
