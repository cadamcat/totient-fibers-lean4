# Third-party code and mathematical sources

## OpenAI's Lean library

This project depends on [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean), commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/`, under the Apache-2.0 license. The upstream repository has no NOTICE file. Lake fetches the library as a Git dependency ([lakefile.lean](lakefile.lean)); no OpenAI source file is copied into this repository.

The project imports these modules of the library directly (`grep -rn '^import OAI' Erdos821` lists the importing files):

- `OAI.NumberTheory.EgyptianFractions.CorrelationPhase`
- `OAI.NumberTheory.EgyptianFractions.DiscreteFirstDerivative`
- `OAI.NumberTheory.EgyptianFractions.DiscreteSecondDerivative`
- `OAI.NumberTheory.EgyptianFractions.ReciprocalDerivatives`
- `OAI.NumberTheory.EgyptianFractions.SecondDifference`
- `OAI.NumberTheory.PrimeGaps.AdditiveSieve`
- `OAI.NumberTheory.PrimeGaps.Main`
- `OAI.NumberTheory.PrimeGaps.MangoldtBounds`
- `OAI.NumberTheory.PrimeGaps.MultiplicativeSieve`
- `OAI.NumberTheory.PrimeGaps.OrthantIntegrals`
- `OAI.NumberTheory.TotientFibers.FiniteFiber`
- `OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalTheorem`
- `OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquare`

`OAI.NumberTheory.TotientFibers.FiniteFiber` supplies the finite totient fiber bound used in the derivation of Erdős 821 from the smooth shifted-prime theorem; the other modules supply analytic number theory estimates used by the packages.

## Other Lean packages

The project imports `PrimeNumberTheoremAnd.Erdos970.MertensClassical` from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (commit `c39a751132c88b6e8080b74c74023fd95b3d8be0`, Apache-2.0) for Mertens' theorems; OpenAI's library pins this package.

The project uses [Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612), commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, under the Apache-2.0 license. OpenAI's library pins Mathlib and further Lean packages, and applies its Lean 4.34.1 compatibility patches to some of them (`scripts/apply-oai-patches.sh`); [lake-manifest.json](lake-manifest.json) records the exact revisions. These packages are fetched by Lake, not redistributed here, and their licenses and notices remain with them.

Lean is selected by [lean-toolchain](lean-toolchain) and installed separately.

## Formal Conjectures

The definition `g` and the proposition of `Erdos821.erdos_821` come from Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/317647fa3fc24ae900a50382186da1d22e4ea398/FormalConjectures/ErdosProblems/821.lean), file `FormalConjectures/ErdosProblems/821.lean`, commit `317647fa3fc24ae900a50382186da1d22e4ea398`, Copyright 2026 The Formal Conjectures Authors, under the Apache-2.0 license:

| Copied into | Change |
| --- | --- |
| `Erdos821/Fidelity/FormalConjectures.lean` | `g` and the right-hand side of `erdos_821` verbatim; `answer(sorry)` replaced by `True` |
| `Challenge.lean`, `Erdos821/Challenge.lean` | `totient` written as `Nat.totient` (Formal Conjectures has `open Nat`); the statement is the right-hand side of `erdos_821`, its answer being `True` |

`Erdos821.Fidelity.statement_iff_formalConjectures` proves that the target is equivalent to the copied statement with `answer(True)`.

## Mathematical sources

The formalized result is OpenAI, [*Weighted dilation graphs, smooth shifted primes and totient fibers*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/paper.pdf), Theorem 1.1, derived in its §8 from Theorem 1.2 (for every fixed `0 < δ < 1/4`, at least `x^(1-o(1))` primes `p` with `2x < p ≤ 5x` have every prime factor of `p - 1` at most `x^δ`). It resolves Erdős Problem 821. The repository formalizes the result and does not claim new mathematics.
