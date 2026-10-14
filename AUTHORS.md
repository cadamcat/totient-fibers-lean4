# Authors and attribution

Yao Xu ([@cadamcat](https://github.com/cadamcat)) is the author and maintainer of this formalization project. The author planned, dispatched and reviewed the work, set its acceptance criteria (only the standard axioms, fidelity of the target statement, checking by the Lean kernel) and decided on its publication.

The mathematical theorem was proved by OpenAI, in the paper [*Weighted dilation graphs, smooth shifted primes and totient fibers*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/paper.pdf). It resolves Erdős's conjecture on the largest fibers of Euler's totient function (Erdős Problem 821). This repository formalizes the theorem; it does not claim a new mathematical solution. The formal proof follows the paper and uses results from OpenAI's Lean library, among them the finite totient fiber bound and prime estimates in arithmetic progressions.

AI coding agents wrote the Lean code under acceptance criteria set by the author. Model agreement was not treated as verification: the resulting proofs and their dependencies were checked by the Lean kernel.

The project uses Mathlib, OpenAI's `openai/math` library and the packages it pins, and a definition copied from Google DeepMind's Formal Conjectures. Their authors and licenses are credited in [THIRD_PARTY.md](THIRD_PARTY.md) and [NOTICE](NOTICE).
