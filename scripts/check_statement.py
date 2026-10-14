#!/usr/bin/env python3
"""Check that Erdos821.erdos_821 in Erdos821.Theorem has the statement of Challenge.lean.

Elaborates Challenge.lean and, in a separate Lean run (both declare the same names), the module
Erdos821.Theorem. Each run prints with `set_option pp.all true` the type of Erdos821.erdos_821 and the
definition Erdos821.g. The two outputs must be identical. Exit 0 when they are, 1 otherwise.
Run after `lake build Erdos821 Challenge`.
"""
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
QUERIES = ["set_option pp.all true", "#check @Erdos821.erdos_821", "#print Erdos821.g"]


def printed(header):
    fd, p = tempfile.mkstemp(prefix=".check_statement_", suffix=".lean", dir=ROOT)
    with os.fdopen(fd, "w") as f:
        f.write("\n".join(header + QUERIES) + "\n")
    try:
        r = subprocess.run(["lake", "env", "lean", p], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.unlink(p)
    lines = re.sub(r"^.*?:\d+:\d+: ", "", r.stdout, flags=re.M).splitlines()
    keep = [l for l in lines if not l.startswith("warning") and "declaration uses 'sorry'" not in l]
    return r.returncode, "\n".join(keep).strip()


def main() -> int:
    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8").splitlines()
    rc1, a = printed(challenge)
    rc2, b = printed(["import Erdos821.Theorem"])
    same = rc1 == 0 and rc2 == 0 and a == b and "Erdos821.erdos_821" in a
    print(f"challenge exit {rc1}, Erdos821.Theorem exit {rc2}, pp.all outputs identical: {a == b}")
    if not same:
        print("--- Challenge.lean\n" + a[-3000:] + "\n--- Erdos821.Theorem\n" + b[-3000:])
        return 1
    print("PASS: Erdos821.erdos_821 and Erdos821.g agree with Challenge.lean.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
