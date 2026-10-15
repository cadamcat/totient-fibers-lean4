# Large totient fibers (Erdős Problem 821), in Lean 4

For every `ε > 0` there are infinitely many `n` with more than `n^(1-ε)` solutions `m` of `φ(m) = n`. This resolves Erdős's conjecture on the largest fibers of Euler's totient function ([Erdős Problem #821](https://www.erdosproblems.com/821)), in the form stated by Formal Conjectures' `erdos_821` with the answer `True`.

- **Author:** Yao Xu ([@cadamcat](https://github.com/cadamcat)); see [authors and attribution](AUTHORS.md).
- **Mathematical result:** OpenAI, [*Weighted dilation graphs, smooth shifted primes and totient fibers*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/paper.pdf), Theorem 1.1, derived from Theorem 1.2 (smooth shifted primes).
- Developed with AI assistance; all proofs are verified by the Lean 4 kernel.

## Main result

```lean
namespace Erdos821

/-- The number of `m` with `φ(m) = n`. -/
noncomputable def g (n : ℕ) : ℕ :=
  {m : ℕ | Nat.totient m = n}.ncard

theorem erdos_821 :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite
```

The theorem is in [Erdos821/Theorem.lean](Erdos821/Theorem.lean); [Challenge.lean](Challenge.lean) states it in Mathlib vocabulary only, and [Challenge.json](Challenge.json) configures [Comparator](https://github.com/leanprover/comparator) to compare the two. The definitions `g` and `Statement` used by the proof are in [Erdos821/Challenge.lean](Erdos821/Challenge.lean).

### Relation to Formal Conjectures

Formal Conjectures states `erdos_821 : answer(sorry) ↔ ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite` (`FormalConjectures/ErdosProblems/821.lean`, commit `317647fa3fc24ae900a50382186da1d22e4ea398`). The theorem here is its right-hand side, so it proves the statement with the answer `True`. Clause by clause:

| Clause | Formal Conjectures | Here |
| --- | --- | --- |
| fiber count | `{m : ℕ \| totient m = n}.ncard` (with `open Nat`) | `{m : ℕ \| Nat.totient m = n}.ncard`, the same term |
| quantifier | `∀ ε > (0 : ℝ)` | same |
| comparison | `(g n : ℝ) > (n : ℝ) ^ (1 - ε)`, real power | same |
| conclusion | `Set.Infinite` | same |
| answer | `answer(sorry)` | `True` |

Both count `m = 0` and `n = 0`. Since `φ 0 = 0`, the value `m = 0` lies only in the fiber of `n = 0`, so `g 0 = 1`; one value of `n` cannot change whether the set is infinite. Every fiber is finite, so `ncard` is the true count. [Erdos821/Fidelity/FormalConjectures.lean](Erdos821/Fidelity/FormalConjectures.lean) proves, with Formal Conjectures' definitions copied verbatim, that the target is equivalent to `erdos_821` with `answer(True)`, and also to the paper's Theorem 1.1, which counts only `m ≥ 1` and `n ≥ 1`.

## Build and verify

Requirements: Git, Python 3, and [elan](https://github.com/leanprover/elan), with `lake` on `PATH`. From the repository root:

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI's `lake update` hook may exit with an error beginning `iut: Lake resolved an unexpected checkout at …` after it has resolved the dependencies and written `lake-manifest.json`. Run the patch script next: it applies OpenAI's Lean 4.34.1 compatibility patches to the fetched packages and can be run again after another `lake update`.

Then:

```sh
./scripts/verify.sh
```

The script builds the library, the challenge and [Verification](Verification), checks that the elaborated statement of `Erdos821.erdos_821` and the definition `g` (printed with `pp.all`) agree with `Challenge.lean`, scans every Lean source for `sorry`, `admit`, added axioms, `native_decide`, `implemented_by`, `extern` and unsafe code, and requires `Erdos821.erdos_821` to depend exactly on `propext`, `Classical.choice` and `Quot.sound`. It exits with status 0 when every check passes, 2 when the proof still depends on `sorry`, and 1 on any other failure. Recorded outputs of a fresh-clone build of v1.0.0, its axiom check, kernel replay and Comparator are in [docs/verification.md](docs/verification.md).

[Verification/NonVacuity.lean](Verification/NonVacuity.lean) checks that the predicate is not trivial on concrete values (`g 4 = 4 > 4^(1/2)`, while `g 3 = 0`), that every fiber is finite, and that Formal Conjectures' statement and the paper's Theorem 1.1 follow from the theorem; the kernel evaluations are in [Erdos821/Fidelity/Examples.lean](Erdos821/Fidelity/Examples.lean). The target is a closed proposition with no hypotheses, so there is nothing else to instantiate.

## How the proof is organized

The formal proof follows the paper. [Erdos821/Supply.lean](Erdos821/Supply.lean) states Theorem 1.2: for every `0 < δ < 1/4` and `σ > 0`, eventually at least `x^(1-σ)` primes `p` with `2x < p ≤ 5x` have every prime factor of `p - 1` at most `x^δ`. [Erdos821/Assembly.lean](Erdos821/Assembly.lean) derives Erdős 821 from it (the paper's §8), using OpenAI's finite fiber bound. [Erdos821/Blueprint/](Erdos821/Blueprint) fixes ten package interfaces P1–P10 for the proof of Theorem 1.2, and [Erdos821/Final/Assembly.lean](Erdos821/Final/Assembly.lean) assembles the package proofs into `Erdos821.Final.statement`.

The `Blueprint` modules state each package interface as a proposition (`X_statement`); each package proves it as a theorem, and `Erdos821.Final.packageInterfaces` assembles those proofs. The only `sorry` in the repository is the one in `Challenge.lean`, which Comparator requires.

| Package | Paper | Interface |
| --- | --- | --- |
| P1 | §2 preliminary estimates: prime estimates, harmonic characters, divisor moments, mean values, derivative tests, Fourier separation | `classical_inputs` |
| P2 | §2 block sieve | `sieve_inputs` |
| P3 | §3 transference for dilation graphs | `transference_inputs` |
| P4 | §4 small ideal kernels | `ideal_inputs` |
| P5 | §5 lifted shifted correlations | `shifted_cancellation` |
| P6 | §6 Type II estimate | `typeII_estimate` |
| P7 | §7 candidate geometry, bounds and Type I estimate | `candidate_geometry`, `candidate_bounds`, `candidate_typeI` |
| P8 | §7 proxies and densities | `proxy_inputs` |
| P9 | §7 balanced rough bound | `balanced_rough_bound` |
| P10 | §7 prime extraction and the count of primes | `prime_extraction`, `count_from_weighted_mass` |

The library has 939 modules. Directories are named after their package (`P<k>…`) or carry an earlier section label (`S2…` for P3, `S34…` for P4, `S56…` for P6, `S9…` for P9, `S10…` for P10):

| Package | Directories (modules) |
| --- | --- |
| P1 | `Classical/` (5), `P1/` (4) |
| P2 | `P2Rough/` (1), `Prelim/` (17) |
| P3 | `P3/` (2), `P3Adj/` (7), `P3Birth/` (1), `P3Clean/` (60), `P3Edge/` (28), `P3Final/` (1), `P3GW/` (1), `P3High/` (11), `P3Live/` (3), `P3LowRank/` (4), `P3Mark/` (1), `P3Pair/` (1), `P3Phys/` (1), `P3Rare/` (3), `P3Restore/` (3), `P3Rows/` (1), `P3Span/` (1), `P3Sum/` (1), `P3Tail/` (2), `S2/` (88), `S2Contr/` (1), `S2Empty/` (12), `S2Full/` (1), `S2Gpar/` (1), `S2High/` (10), `S2Hist/` (1), `S2Ltrans/` (1), `S2Nondiv/` (1), `S2Packet/` (1), `S2Phys/` (1), `S2Resid/` (1), `S2Root/` (2), `S2Tail/` (1) |
| P4 | `P4Bridge/` (11), `P4Cancel/` (4), `P4Cell/` (1), `P4Char/` (1), `P4Count/` (1), `P4Frame/` (1), `P4Independent/` (1), `P4Marg/` (1), `P4Probe/` (43), `P4Proj/` (1), `P4Rat/` (2), `P4Shared/` (1), `S34/` (58) |
| P5 | `P5/` (170), `P5CellCost/` (1), `P5Div/` (1), `P5Energy/` (6), `P5FourierArcProof/` (1), `P5Gram/` (2), `P5Log/` (1), `P5MarkedEnergy/` (26), `P5Mellin/` (3), `P5Minor/` (1), `P5MinorAdapter/` (2), `P5SmoothSquare/` (1) |
| P6 | `P6Cut/` (1), `P6Maj/` (1), `P6Mass/` (1), `P6Off/` (55), `P6Reidx/` (1), `P6Slot/` (1), `P6Split/` (1), `P6Sq/` (2), `P6Sum/` (1), `S56/` (72) |
| P7 | `P7/` (28), `P7Band/` (3), `P7Char/` (11), `P7Free/` (2), `P7HQ/` (1), `P7Place/` (1), `P7Prefix/` (1), `P7TypeI/` (1), `P7Win/` (1) |
| P8 | `P8/` (35), `P8Grid/` (4), `P8Int/` (1), `P8Low/` (1), `P8Np/` (1), `P8Res/` (1), `P8Tail/` (1) |
| P9 | `P9/` (20), `S9/` (13), `S9Budget/` (1), `S9Div/` (1), `S9Mask/` (3), `S9Norm/` (1) |
| P10 | `Count/` (1), `P10/` (2), `S10/` (5), `S10Bfac/` (1), `S10Brough/` (1), `S10Cover/` (1), `S10Prime/` (2), `S10Sharp/` (2) |
| statement, interfaces, assembly, shared lemmas | `Assembly.lean` (1), `Blueprint/` (18), `Challenge.lean` (1), `Fidelity/` (2), `Final/` (1), `Leaves/` (7), `Leaves.lean` (1), `Prelim.lean` (1), `Supply.lean` (1), `Theorem.lean` (1) |

## Fixed dependencies

- Lean `v4.34.1`, selected by [lean-toolchain](lean-toolchain).
- [Mathlib](https://github.com/leanprover-community/mathlib4), commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- OpenAI's [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean), commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- The remaining dependency revisions, pinned by OpenAI's library, are fixed in [lake-manifest.json](lake-manifest.json).

## Mathematical references

- OpenAI, [*Weighted dilation graphs, smooth shifted primes and totient fibers*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/paper.pdf), September 24, 2026.
- [Erdős Problem #821](https://www.erdosproblems.com/821).
- C. Pomerance, *Popular values of Euler's function*, Mathematika 27 (1980), 84–89, which formulates the conjecture as `C = 1` for the supremum `C` of the exponents `c` with `g(n) > n^c` infinitely often.

## License

Apache-2.0; see [LICENSE](LICENSE), [NOTICE](NOTICE), and [third-party attribution](THIRD_PARTY.md).
