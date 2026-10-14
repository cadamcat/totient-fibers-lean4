import Erdos821.P6Off.Precision

noncomputable section
open Filter

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic

theorem eventually_log_rpow_le_x_rpow (A b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, L x ^ A ≤ x ^ b := by
  have hsmall := isLittleO_log_rpow_rpow_atTop A hb
  have hbound : ∀ᶠ x : ℝ in atTop, ‖Real.log x ^ A‖ ≤ ‖x ^ b‖ := by
    simpa using hsmall.bound (c := 1) zero_lt_one
  filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L x := Real.log_pos hx1
  exact (le_abs_self (L x ^ A)).trans (by
    simpa only [L, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hxpos b)] using hx)

/-- Fixed scalar Fourier factors can be absorbed by increasing the power
bound once; that increase occurs before the discrepancy exponent. -/
theorem eventually_frequency_power (C Cf : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ rho t : ℝ,
      |rho| ≤ L x ^ C → |t| ≤ L x ^ Cf →
        |rho + 2 * Real.pi * t| ≤ L x ^ (max C Cf + 1) := by
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  filter_upwards [hL.eventually (eventually_ge_atTop (1 + 2 * Real.pi))] with x hx
  have hL1 : 1 ≤ L x := by linarith [Real.pi_pos]
  have hLpos : 0 < L x := by linarith
  intro rho t hrho ht
  have hC : L x ^ C ≤ L x ^ max C Cf :=
    Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)
  have hCf : L x ^ Cf ≤ L x ^ max C Cf :=
    Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _)
  calc
    _ ≤ |rho| + |2 * Real.pi * t| := abs_add_le _ _
    _ = |rho| + (2 * Real.pi) * |t| := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    _ ≤ (1 + 2 * Real.pi) * L x ^ max C Cf := by
      have ht' := ht.trans hCf
      have hrho' := hrho.trans hC
      nlinarith [mul_le_mul_of_nonneg_left ht' (by positivity : 0 ≤ 2 * Real.pi)]
    _ ≤ L x ^ max C Cf * L x := by
      have h := mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hLpos.le (max C Cf))
      nlinarith
    _ = _ := by simpa only [Real.rpow_one] using (Real.rpow_add hLpos (max C Cf) 1).symm


end Erdos821.P6Off
