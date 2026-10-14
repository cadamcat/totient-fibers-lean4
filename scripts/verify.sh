#!/usr/bin/env bash
# Build Erdos821.erdos_821, compare its statement with Challenge.lean, scan the sources for forbidden
# constructs and check the theorem's axioms.
#
# Exit 0: every check passed and the theorem depends exactly on propext, Classical.choice and
# Quot.sound. Exit 2: the proof is still open (sorryAx, or an unexpected sorry in the sources).
# Exit 1: any other failure (build, statement mismatch, another axiom, a forbidden construct).
set -uo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
result_dir=.lake/verification-results
mkdir -p "$result_dir"

lake build Erdos821 Challenge Verification || { echo "verify: FAIL (build)" >&2; exit 1; }

status=0
note() {  # keep the most serious status: 1 over 2 over 0
  if [ "$1" -eq 1 ] || { [ "$1" -eq 2 ] && [ "$status" -eq 0 ]; }; then status=$1; fi
}

python3 scripts/check_statement.py; note $?
python3 scripts/check_forbidden.py; note $?

axiom_log="$result_dir/axioms.log"
if lake env lean Verification/Axioms.lean >"$axiom_log" 2>&1; then
  cat "$axiom_log"
  python3 scripts/check_axioms.py "$axiom_log"; note $?
else
  cat "$axiom_log"; note 1
fi

case $status in
  0) echo "verify: PASS" ;;
  2) echo "verify: OPEN (the proof still depends on sorry)" >&2 ;;
  *) echo "verify: FAIL" >&2 ;;
esac
exit "$status"
