#!/usr/bin/env python3
"""Check the axiom report of Erdos821.erdos_821 in a captured `#print axioms` log.

Exit 0 when the theorem depends exactly on propext, Classical.choice and Quot.sound; 2 when it also
depends on sorryAx (an open proof) and on nothing else outside that set; 1 otherwise, including a
missing, repeated or unparsable report.
"""
import re
import sys
from pathlib import Path

EXPECTED = {"propext", "Classical.choice", "Quot.sound"}
OPEN = "sorryAx"
TARGET = "Erdos821.erdos_821"
# Lean may wrap a long axiom list over several lines.
REPORT = re.compile(r"'(?P<name>[^'\n]+)' depends on axioms:\s*\[(?P<axioms>[^\]]*)\]")
NO_AXIOMS = re.compile(r"'(?P<name>[^'\n]+)' does not depend on any axioms")


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} AXIOM_LOG", file=sys.stderr)
        return 1
    log = Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace")
    reports = [(m.group("name"), m.group("axioms")) for m in REPORT.finditer(log)]
    reports += [(m.group("name"), "") for m in NO_AXIOMS.finditer(log)]
    if len(reports) != 1 or reports[0][0] != TARGET:
        print(f"FAIL: expected exactly one axiom report, for {TARGET}; found {[r[0] for r in reports]}",
              file=sys.stderr)
        return 1
    axioms = {a.strip() for a in reports[0][1].split(",") if a.strip()}
    print(f"axioms of {TARGET}: {', '.join(sorted(axioms)) or '(none)'}")
    unexpected = axioms - EXPECTED - {OPEN}
    if unexpected:
        print(f"FAIL: axioms outside propext, Classical.choice, Quot.sound: {', '.join(sorted(unexpected))}",
              file=sys.stderr)
        return 1
    if OPEN in axioms:
        print(f"OPEN: {TARGET} depends on sorryAx; the proof is incomplete.", file=sys.stderr)
        return 2
    if axioms != EXPECTED:
        print(f"FAIL: expected exactly {sorted(EXPECTED)}", file=sys.stderr)
        return 1
    print("PASS: exactly propext, Classical.choice and Quot.sound.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
