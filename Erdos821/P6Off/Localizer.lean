import Erdos821.P6Off.PulledCutoff
import Erdos821.P6Off.Discrepancy
import Erdos821.P6Off.Twists

noncomputable section
open scoped BigOperators ContDiff

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic

def logBump : ContDiffBump (0 : Fin 3 → ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def logLocalizer : (Fin 3 → ℝ) → ℝ := logBump

def logCoordinates (U Z m m' z : ℝ) : Fin 3 → ℝ :=
  ![Real.log (m / U), Real.log (m' / U), Real.log (z / Z)]

theorem logLocalizer_contDiff : ContDiff ℝ ∞ logLocalizer := logBump.contDiff

theorem logLocalizer_support : Function.support logLocalizer ⊆ Metric.closedBall 0 2 := by
  rw [logLocalizer, logBump.support_eq]
  exact Metric.ball_subset_closedBall

theorem logLocalizer_compact : HasCompactSupport logLocalizer := logBump.hasCompactSupport

theorem logLocalizer_derivative_bounds :
    ∃ bounds : ℕ → ℝ, (∀ j, 0 ≤ bounds j) ∧
      ∀ j y, ‖iteratedFDeriv ℝ j logLocalizer y‖ ≤ bounds j := by
  have hb (j : ℕ) := logLocalizer_compact.exists_bound_iteratedFDeriv
    logLocalizer_contDiff j
  choose bounds hpos hb using hb
  exact ⟨bounds, hpos, fun j y => hb j j le_rfl y⟩

theorem abs_log_le_one {u : ℝ} (hlo : 1 / 2 ≤ u) (hhi : u ≤ 2) : |Real.log u| ≤ 1 := by
  have hpos : 0 < u := by linarith
  have hinv : u⁻¹ ≤ 2 := by
    calc
      _ ≤ (1 / 2 : ℝ)⁻¹ := by gcongr
      _ = 2 := by norm_num
  exact abs_le.mpr ⟨by linarith [Real.one_sub_inv_le_log_of_pos hpos],
    by linarith [Real.log_le_sub_one_of_pos hpos]⟩

theorem logLocalizer_one (U Z m m' z : ℝ)
    (hm : 1 / 2 ≤ m / U ∧ m / U ≤ 2)
    (hm' : 1 / 2 ≤ m' / U ∧ m' / U ≤ 2)
    (hz : 1 / 2 ≤ z / Z ∧ z / Z ≤ 2) :
    logLocalizer (logCoordinates U Z m m' z) = 1 := by
  apply logBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  fin_cases i <;> simp only [logCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Real.norm_eq_abs]
  · exact abs_log_le_one hm.1 hm.2
  · exact abs_log_le_one hm'.1 hm'.2
  · exact abs_log_le_one hz.1 hz.2

/-- Fourier separation leaves exactly the pulled-back weights on the ranges in use. -/
theorem pulledCutoff_on_ranges (U V Z E m m' z : ℝ) (k : ℤ) (etae etan : ℝ → ℝ)
    (hU : 0 < U) (hZ : 0 < Z) (hm : 0 < m) (hm' : 0 < m') (hz : 0 < z)
    (hloc : logLocalizer (logCoordinates U Z m m' z) = 1) :
    pulledCutoff U V Z E k etae etan logLocalizer (logCoordinates U Z m m' z) =
      (etae ((m' - m) / (2 * k * E)) *
        etan ((m' - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) := by
  have he1 : U * Real.exp (Real.log (m / U)) = m := by
    rw [Real.exp_log (div_pos hm hU)]
    field_simp
  have he2 : U * Real.exp (Real.log (m' / U)) = m' := by
    rw [Real.exp_log (div_pos hm' hU)]
    field_simp
  have he3 : Z * Real.exp (Real.log (z / Z)) = z := by
    rw [Real.exp_log (div_pos hz hZ)]
    field_simp
  have hloc' : logLocalizer ![Real.log (m / U), Real.log (m' / U), Real.log (z / Z)] = 1 := hloc
  simp [pulledCutoff, logCoordinates, he1, he2, he3, hloc']


end Erdos821.P6Off
