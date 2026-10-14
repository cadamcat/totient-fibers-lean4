import Erdos821.S56.BandSize

noncomputable section
open Filter
open scoped Topology

namespace Erdos821.S56Core
open Erdos821.Blueprint.Analytic

theorem loglog_le_small_log (b K0 : ℝ) (hb : 0 < b) (hK0 : 0 ≤ K0) :
    ∀ᶠ x : ℝ in atTop, K0 * T x ≤ (b / 2) * L x := by
  have hc : 0 < b / (2 * (K0 + 1)) := by positivity
  have hevent := tendsto_L.eventually (Real.isLittleO_log_id_atTop.def hc)
  filter_upwards [hevent, tendsto_L.eventually (eventually_ge_atTop 1)] with x hx hL
  have hT : 0 ≤ T x := Real.log_nonneg hL
  change ‖T x‖ ≤ b / (2 * (K0 + 1)) * ‖L x‖ at hx
  simp only [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hL), abs_of_nonneg hT] at hx
  have hbound : T x ≤ b / (2 * (K0 + 1)) * L x := hx
  have hfactor : K0 * (b / (2 * (K0 + 1))) ≤ b / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (K0 + 1))).mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_left hbound hK0).trans
    (by simpa [mul_assoc] using mul_le_mul_of_nonneg_right hfactor (zero_le_one.trans hL))

/-- E=U L^(-K₀) stays at least one uniformly in the balanced U range. -/
theorem eventually_splitting_scale (b K0 : ℝ) (hb : 0 < b) (hK0 : 0 ≤ K0) :
    ∀ᶠ x : ℝ in atTop, ∀ U : ℝ, x ^ b ≤ U →
      1 ≤ U * L x ^ (-K0) := by
  filter_upwards [loglog_le_small_log b K0 hb hK0, eventually_gt_atTop 1] with x hx hx1
  intro U hU
  have hxpos : 0 < x := zero_lt_one.trans hx1
  have hL : 0 < L x := Real.log_pos hx1
  have hUpos : 0 < U := (Real.rpow_pos_of_pos hxpos b).trans_le hU
  have hlogU := Real.log_le_log (Real.rpow_pos_of_pos hxpos b) hU
  rw [Real.log_rpow hxpos] at hlogU
  have hEpos : 0 < U * L x ^ (-K0) := mul_pos hUpos (Real.rpow_pos_of_pos hL _)
  have hlogE : 0 ≤ Real.log (U * L x ^ (-K0)) := by
    rw [Real.log_mul hUpos.ne' (Real.rpow_pos_of_pos hL _).ne', Real.log_rpow hL]
    change K0 * Real.log (L x) ≤ b / 2 * Real.log x at hx
    have hlogx : 0 < Real.log x := hL
    nlinarith [mul_pos hb hlogx]
  exact (Real.log_nonneg_iff hEpos).mp hlogE


end Erdos821.S56Core
