import Mathlib

/-!
# Erdős Problem 821 (JSP-000677)

Let `g n` be the number of natural numbers `m` with `φ(m) = n`. For `n ≥ 1` these `m` are positive;
since `φ 0 = 0`, the only extra case is `g 0 = 1`. For every `ε > 0` there are infinitely many `n`
with `g n > n ^ (1 - ε)`.

The statement follows Formal Conjectures' `Erdos821.erdos_821` (Apache-2.0), with the answer `True`.
-/

namespace Erdos821

/-- The number of `m` with `φ(m) = n`. -/
noncomputable def g (n : ℕ) : ℕ :=
  {m : ℕ | Nat.totient m = n}.ncard

/-- Erdős 821: for every `ε > 0`, infinitely many `n` satisfy `g n > n ^ (1 - ε)`. -/
def Statement : Prop :=
  ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite

end Erdos821
