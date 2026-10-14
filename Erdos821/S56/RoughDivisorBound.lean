import Erdos821.P5Div.Basic
import Erdos821.S56.BandSize

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint.Analytic

/-- The rough-divisor factor lost while discarding a large group part has
only exp(O(sqrt L)) growth, below the Rankin exponential saving. -/
theorem rough_divisor_exp_bound (x : ℝ) (hx : 5 ≤ x) (N : ℕ)
    (hN : 0 < N) (hNx : (N : ℝ) ≤ 5 * x) :
    (((N.divisors.filter (rough (W x))).card : ℕ) : ℝ) ≤
      Real.exp (2 * Real.sqrt (L x)) := by
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hL : 0 < L x := Real.log_pos hx1
  have hs : 0 < Real.sqrt (L x) := Real.sqrt_pos.mpr hL
  have hW : 1 < W x := by
    change 1 < Real.exp (Real.sqrt (L x))
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hs
  have hraw := Erdos821.P5Div.RoughDivisorCountTask_proof (W x) N hW hN
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlog5 : Real.log 5 ≤ L x := Real.log_le_log (by norm_num) hx
  have hlogN : Real.log (N : ℝ) ≤ 2 * L x := by
    have h := Real.log_le_log (by exact_mod_cast hN : (0 : ℝ) < N) hNx
    rw [Real.log_mul (by norm_num) hxpos.ne'] at h
    change Real.log (N : ℝ) ≤ Real.log 5 + L x at h
    linarith
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog2N : Real.log 2 * Real.log (N : ℝ) ≤ 2 * L x := by
    have h := mul_le_mul_of_nonneg_right hlog2 hlogN0
    linarith
  have hsquare := Real.sq_sqrt hL.le
  have hexp : Real.log 2 * Real.log (N : ℝ) / Real.log (W x) ≤ 2 * Real.sqrt (L x) := by
    rw [W, Real.log_exp]
    apply (div_le_iff₀ hs).mpr
    nlinarith
  exact hraw.trans (Real.exp_le_exp.mpr hexp)


end Erdos821.S56Core
