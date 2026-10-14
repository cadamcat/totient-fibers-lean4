import Mathlib

noncomputable section
open scoped BigOperators

namespace Erdos821.P6Off

/-- Choose the saving before summing the fixed logarithmic numbers of dyads
and shifts. This is the final power bookkeeping in the off-diagonal reduction. -/
theorem sum_dyads_shifts_bound (x ell A C K : ℝ) (hx : 0 ≤ x) (hell : 0 < ell) (hK : 0 ≤ K)
    (js : Finset ℕ) (ks : Finset ℤ) (Z : ℕ → ℝ) (F : ℕ → ℤ → ℂ)
    (hjcount : (js.card : ℝ) ≤ ell ^ (2 : ℕ))
    (hkcount : (ks.card : ℝ) ≤ ell ^ C)
    (hZ : ∀ j ∈ js, Z j ≤ x * ell ^ C)
    (hF : ∀ j ∈ js, ∀ k ∈ ks, ‖F j k‖ ≤ K * Z j * ell ^ (-(A + 2 * C + 2))) :
    ‖∑ j ∈ js, ∑ k ∈ ks, F j k‖ ≤ K * x * ell ^ (-A) := by
  have hpoint : ∀ j ∈ js, ∀ k ∈ ks, ‖F j k‖ ≤ K * x * ell ^ (-(A + C + 2)) := by
    intro j hj k hk
    apply (hF j hj k hk).trans
    calc
      _ ≤ K * (x * ell ^ C) * ell ^ (-(A + 2 * C + 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hZ j hj) hK)
          (Real.rpow_nonneg hell.le _)
      _ = _ := by
        have heq : ell ^ C * ell ^ (-(A + 2 * C + 2)) = ell ^ (-(A + C + 2)) := by
          rw [← Real.rpow_add hell]
          congr 1 <;> ring
        calc
          _ = K * x * (ell ^ C * ell ^ (-(A + 2 * C + 2))) := by ring
          _ = _ := by rw [heq]
  have hQ : 0 ≤ K * x * ell ^ (-(A + C + 2)) := by positivity
  calc
    _ ≤ ∑ j ∈ js, ‖∑ k ∈ ks, F j k‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ js, ∑ k ∈ ks, ‖F j k‖ :=
      Finset.sum_le_sum (fun j _ => norm_sum_le _ _)
    _ ≤ ∑ _j ∈ js, ∑ _k ∈ ks, K * x * ell ^ (-(A + C + 2)) :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun k hk => hpoint j hj k hk))
    _ = ((js.card : ℝ) * (ks.card : ℝ)) * (K * x * ell ^ (-(A + C + 2))) := by simp; ring
    _ ≤ (ell ^ (2 : ℕ) * ell ^ C) * (K * x * ell ^ (-(A + C + 2))) := by
      apply mul_le_mul_of_nonneg_right _ hQ
      exact mul_le_mul hjcount hkcount (by positivity) (by positivity)
    _ = _ := by
      have heq : ell ^ (2 : ℕ) * ell ^ C * ell ^ (-(A + C + 2)) = ell ^ (-A) := by
        rw [← Real.rpow_two, ← Real.rpow_add hell, ← Real.rpow_add hell]
        congr 1 <;> ring
      calc
        _ = K * x * (ell ^ (2 : ℕ) * ell ^ C * ell ^ (-(A + C + 2))) := by ring
        _ = _ := by rw [heq]


end Erdos821.P6Off
