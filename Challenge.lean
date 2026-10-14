import Mathlib

/-!
# Erdős Problem 821 (challenge statement)

Let `g n` be the number of natural numbers `m` with `φ m = n`. For every `ε > 0`, infinitely many `n`
satisfy `g n > n ^ (1 - ε)`.

This file states the theorem in Mathlib vocabulary only. The definition `g` is copied from Formal
Conjectures (`FormalConjectures/ErdosProblems/821.lean`, Apache-2.0), with `Nat.totient` written in
full, and the proposition is the right-hand side of its `erdos_821` with the answer `True`.
`Erdos821/Theorem.lean` proves a theorem of the same name and statement; `Challenge.json` configures
Comparator to compare the two.
-/

namespace Erdos821

/-- The number of `m` with `φ(m) = n`. -/
noncomputable def g (n : ℕ) : ℕ :=
  {m : ℕ | Nat.totient m = n}.ncard

theorem erdos_821 :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  sorry

end Erdos821
