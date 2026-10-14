import Erdos821

/-!
# Non-vacuity and fidelity checks

`Erdos821.Statement` has no hypotheses: it is a closed proposition about Mathlib's `Nat.totient`, so
there is nothing to instantiate. The checks below show instead that its predicate is neither trivially
true nor trivially false on concrete values, that the counting function `g` is the true fiber size,
and that the proved theorem is Formal Conjectures' `erdos_821` with the answer `True`. The kernel
evaluations themselves are in `Erdos821/Fidelity/Examples.lean`.
-/

namespace Erdos821

open Fidelity

/-- `g 4 = 4`: the fiber of `4` is `{5, 8, 10, 12}`. -/
example : g 4 = 4 := Examples.g_four

/-- Every fiber is finite, so `Set.ncard` counts it exactly. -/
example (n : ℕ) : {m : ℕ | Nat.totient m = n}.Finite := Source.totient_fiber_finite n

/-- The predicate holds at `n = 4` for `ε = 1/2`: `g 4 = 4 > 4 ^ (1/2) = 2`. -/
example : (4 : ℕ) ∈ {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - (1 / 2 : ℝ))} := by
  show ((g 4 : ℕ) : ℝ) > ((4 : ℕ) : ℝ) ^ (1 - (1 / 2 : ℝ))
  rw [Examples.g_four]
  have h : ((4 : ℕ) : ℝ) ^ (1 - (1 / 2 : ℝ)) = 2 := by
    rw [show (1 : ℝ) - 1 / 2 = ((2 : ℕ) : ℝ)⁻¹ by norm_num, show ((4 : ℕ) : ℝ) = (2 : ℝ) ^ (2 : ℕ) by
      norm_num, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
  rw [h]; norm_num

/-- The theorem is the closed proposition `Statement`. -/
example : Statement := erdos_821

/-- Formal Conjectures' `erdos_821`, with `answer(True)` and its own copy of `g`, follows. -/
example : FormalConjectures.erdos_821_answer_true :=
  statement_iff_formalConjectures.mp erdos_821

/-- The source paper's Theorem 1.1, which counts only `m ≥ 1` and `n ≥ 1`, follows. -/
example : Source.Theorem_1_1 := Source.statement_iff_theorem_1_1.mp erdos_821

end Erdos821
