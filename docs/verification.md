# Verification record

Checks of release v1.0.0, commit `dfce35707a67fce7362cb2bd95af8b80a0b0373e`, on 2026-10-14. The run started from a fresh clone of this repository, followed the [build steps in the README](../README.md#build-and-verify) and used 12 threads on the author's Mac; `lake update` ended with OpenAI's expected `iut` hook error, which the README describes, and the patch script and the Mathlib cache then exited 0. Later releases change only comments, documentation and `Challenge.json`; no Lean statement or proof differs from v1.0.0.

| Check | Command | Result |
| --- | --- | --- |
| Build | `lake build` | exit 0, 9940 jobs |
| Axioms | `#print axioms Erdos821.erdos_821` | `'Erdos821.erdos_821' depends on axioms: [propext, Classical.choice, Quot.sound]` |
| Kernel replay | `lake env leanchecker --fresh Erdos821.Theorem` | exit 0 |
| Comparator | `Challenge.json` with `definition_names` empty, nanoda enabled | exit 0: "nanoda kernel accepts the solution", "Lean default kernel accepts the solution", "Your solution is okay!" |

Comparator compares `Erdos821.erdos_821` and the definition `Erdos821.g` against [Challenge.lean](../Challenge.lean), which uses Mathlib definitions only and states Formal Conjectures' `g` and the right-hand side of its `erdos_821`, with `totient` written as `Nat.totient`. It was not run against an export of the Formal Conjectures repository.

Tool versions: Comparator `ca04cfc72b550331658ec314bf47685281bfd4bf`, lean4export `076e8e57707e813375e8f9da8bf989799ace9680`, nanoda_lib `3a2407216ee84a75f9e1aead6803d0578be06ae7`. Comparator ran with its development `fake-landrun.sh`, not the Landrun sandbox.

## Controls

- nanoda accepted a correct proof and rejected a proof by `sorry` (exit 1) and an export with a tampered numeral (exit 101).
- No Comparator run with a deliberately changed challenge was made for this repository.

## Configuration

Releases v1.0.0 to v1.0.2 ship `Challenge.json` with `"enable_nanoda": false`; the run above used the same file with `"enable_nanoda": true`, and since v1.0.3 that is the shipped setting. `definition_names` has been empty in every release, so Comparator compares the body of `g` as well as its type. `scripts/verify.sh` compares `g` and the statement with `Challenge.lean` at `pp.all` in every release.
