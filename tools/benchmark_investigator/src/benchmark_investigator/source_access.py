"""Read/search only the source files recorded in the campaign manifest."""

from pathlib import Path

from .artifacts import contained, sha256


class SourceAccess:
    def __init__(self, root: Path, files: dict[str, str]):
        self.root = root.resolve()
        self.files = files

    def path(self, name: str) -> Path:
        path = contained(self.root, name)
        relative = path.relative_to(self.root).as_posix()
        if relative not in self.files:
            raise ValueError("Only pinned source files can be inspected")
        if sha256(path) != self.files[relative]:
            raise ValueError(f"Pinned source changed: {relative}")
        return path

    def read(self, name: str, start: int, end: int) -> dict:
        if not 1 <= start <= end < start + 200:
            raise ValueError("Read range must be 1–200 lines")
        lines = self.path(name).read_text(errors="replace").splitlines()
        text = "\n".join(
            f"{i + 1}: {line}" for i, line in enumerate(lines) if start <= i + 1 <= end
        )
        return {"path": name, "text": text[:16000], "truncated": len(text) > 16000}

    def search(self, query: str) -> dict:
        if not query or len(query) > 500:
            raise ValueError("Search requires 1–500 characters")
        matches = []
        for name in sorted(self.files):
            for number, line in enumerate(
                self.path(name).read_text(errors="replace").splitlines(), 1
            ):
                if query.casefold() in line.casefold():
                    matches.append({"path": name, "line": number, "text": line[:400]})
                    if len(matches) >= 40:
                        return {"matches": matches, "truncated": True}
        return {"matches": matches, "truncated": False}
