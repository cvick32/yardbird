"""Dependency-free SVG charts for instrumentation strategy aggregates."""

from __future__ import annotations

import html
from pathlib import Path


def write_instrumentation_chart(
    path: Path,
    strategies: list[dict],
    *,
    kind: str,
) -> Path:
    width = 1200
    label_width = 300
    chart_width = 820
    top = 100
    row_height = 45
    height = top + max(1, len(strategies)) * row_height + 45

    if kind == "external":
        title = "Median captured-session replay time by strategy"
        first_label, second_label = "Stock external", "Instrumented external"
        first_color, second_color = "#5084c4", "#c44e52"
        values = [
            (
                row["metrics"]["stock_external_median_ns"],
                row["metrics"]["instrumented_external_median_ns"],
            )
            for row in strategies
        ]
    elif kind == "breakdown":
        title = "Median instrumented Z3 internal time by strategy"
        first_label, second_label = "Array envelope", "Non-array residual"
        first_color, second_color = "#4ea397", "#dd8452"
        values = [
            (
                row["metrics"]["array_envelope_median_ns"],
                row["metrics"]["non_array_residual_median_ns"],
            )
            for row in strategies
        ]
    else:
        raise ValueError(f"Unknown instrumentation chart kind: {kind}")

    maximum = max((first + second for first, second in values), default=1)
    if kind == "external":
        maximum = max((max(first, second) for first, second in values), default=1)
    maximum = max(maximum, 1)
    scale = chart_width / maximum

    lines = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="white"/>',
        _svg_text(
            12, 32, title, font_family="sans-serif", font_size="30", font_weight="bold"
        ),
        f'<rect x="{label_width}" y="39" width="12" height="12" fill="{first_color}"/>',
        _svg_text(
            label_width + 18, 64, first_label, font_family="sans-serif", font_size="20"
        ),
        f'<rect x="{label_width + 195}" y="39" width="12" height="12" fill="{second_color}"/>',
        _svg_text(
            label_width + 213,
            64,
            second_label,
            font_family="sans-serif",
            font_size="20",
        ),
    ]
    _add_axis(lines, label_width, chart_width, top, height, maximum)
    for row, (strategy, values_row) in enumerate(zip(strategies, values)):
        _add_strategy_row(
            lines,
            row,
            strategy,
            values_row,
            kind=kind,
            label_width=label_width,
            top=top,
            row_height=row_height,
            scale=scale,
            colors=(first_color, second_color),
        )
    lines.append("</svg>")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


def _add_axis(lines, label_width, chart_width, top, height, maximum) -> None:
    for fraction in (0.0, 0.5, 1.0):
        x = label_width + chart_width * fraction
        lines.append(
            f'<line x1="{x:.1f}" y1="{top - 8}" x2="{x:.1f}" y2="{height - 30}" stroke="#dddddd" stroke-width="1"/>'
        )
        lines.append(
            _svg_text(
                x,
                height - 10,
                f"{maximum * fraction / 1_000_000:.2f}ms",
                font_family="sans-serif",
                font_size="16",
                text_anchor="middle",
                fill="#555555",
            )
        )


def _add_strategy_row(
    lines,
    row,
    strategy,
    values,
    *,
    kind,
    label_width,
    top,
    row_height,
    scale,
    colors,
) -> None:
    first, second = values
    first_color, second_color = colors
    y = top + row * row_height
    label = f"{strategy['strategy_label']} ({strategy['session_count']} sessions)"
    lines.append(
        _svg_text(
            label_width - 8,
            y + 17,
            label,
            font_family="sans-serif",
            font_size="18",
            text_anchor="end",
        )
    )
    if kind == "external":
        lines.extend(
            [
                f'<rect x="{label_width}" y="{y + 5}" width="{first * scale:.2f}" height="9" fill="{first_color}"/>',
                f'<rect x="{label_width}" y="{y + 17}" width="{second * scale:.2f}" height="9" fill="{second_color}"/>',
            ]
        )
    else:
        first_width = first * scale
        lines.extend(
            [
                f'<rect x="{label_width}" y="{y + 8}" width="{first_width:.2f}" height="16" fill="{first_color}"/>',
                f'<rect x="{label_width + first_width:.2f}" y="{y + 8}" width="{second * scale:.2f}" height="16" fill="{second_color}"/>',
            ]
        )


def _svg_text(x: float, y: float, value: str, **attributes: object) -> str:
    attrs = " ".join(
        f'{name.replace("_", "-")}="{item}"' for name, item in attributes.items()
    )
    return f'<text x="{x}" y="{y}" {attrs}>{html.escape(value)}</text>'
