#!/usr/bin/env python3
"""Scan the Lean sources for forbidden constructs.

Scans Erdos821.lean, every file under Erdos821/ and Verification/, and Challenge.lean for `sorry`,
`admit`, `axiom` declarations, `native_decide`, `implemented_by`, `extern`, `unsafe` and options that
weaken kernel checking. Comments and string literals are skipped.

Challenge.lean states the target with `sorry`, as a Comparator challenge module does; that `sorry`
is expected and only listed.

Exit 0 when nothing else is found; 2 when the only other hits are `sorry` (an open proof); 1 when any
other construct is found.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PATTERNS = [
    ("sorry", re.compile(r"\bsorry\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("axiom-declaration", re.compile(r"^\s*(?:private\s+|protected\s+)*axiom\b")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("implemented_by", re.compile(r"\bimplemented_by\b")),
    ("extern", re.compile(r"\bextern\b")),
    ("unsafe", re.compile(r"\bunsafe\b")),
    ("kernel-option", re.compile(r"\bdebug\.skipKernelTC\b")),
]
EXPECTED_SORRY = ("Challenge.lean",)


def code_only(text):
    """Blank out comments and string literals, keeping line numbers."""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append("\n" * text.count("\n", i, j))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append("\n" * text.count("\n", i, j))
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out).splitlines()


def files():
    found = [ROOT / "Challenge.lean", ROOT / "Erdos821.lean"]
    for d in ("Erdos821", "Verification"):
        found += sorted((ROOT / d).rglob("*.lean"))
    return found


def main() -> int:
    other = sorry = expected = 0
    for path in files():
        rel = path.relative_to(ROOT).as_posix()
        for i, line in enumerate(code_only(path.read_text(encoding="utf-8")), 1):
            for kind, rx in PATTERNS:
                if not rx.search(line):
                    continue
                if kind == "sorry" and rel.startswith(EXPECTED_SORRY):
                    expected += 1
                    continue
                print(f"{rel}:{i}: {kind}: {line.strip()}")
                if kind == "sorry":
                    sorry += 1
                else:
                    other += 1
    print(f"forbidden constructs: {other}; unexpected sorry: {sorry}; "
          f"expected sorry in {', '.join(EXPECTED_SORRY)}: {expected}")
    return 1 if other else 2 if sorry else 0


if __name__ == "__main__":
    raise SystemExit(main())
