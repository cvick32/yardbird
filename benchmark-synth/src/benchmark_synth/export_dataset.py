"""Dataset export entry points."""

from __future__ import annotations

from pathlib import Path
import json


def export_placeholder(output_file: Path) -> None:
    payload = {
        "status": "not_implemented",
        "message": "dataset export is scaffolded but not implemented in the first slice",
    }
    output_file.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
