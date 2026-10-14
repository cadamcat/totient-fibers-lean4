import Erdos821.P6Off.Task

noncomputable section
open scoped BigOperators ContDiff

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic

/-- A fixed smooth transition from scale one-half to scale one. -/
def dyadicStep (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1)

/-- A fixed smooth dyadic partition function supported in [1/2,2]. -/
def dyadicCutoff (t : ℝ) : ℝ := dyadicStep t - dyadicStep (t / 2)

theorem dyadicCutoff_contDiff : ContDiff ℝ ∞ dyadicCutoff := by
  unfold dyadicCutoff dyadicStep
  fun_prop

theorem dyadicCutoff_support : Function.support dyadicCutoff ⊆ Set.Icc (1 / 2) 2 := by
  intro t ht
  have hne : dyadicCutoff t ≠ 0 := ht
  constructor
  · by_contra h
    have ht : t < 1 / 2 := lt_of_not_ge h
    apply hne
    unfold dyadicCutoff dyadicStep
    rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    ring
  · by_contra h
    have ht : 2 < t := lt_of_not_ge h
    apply hne
    unfold dyadicCutoff dyadicStep
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith)]
    ring

theorem dyadicCutoff_compact : HasCompactSupport dyadicCutoff :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc dyadicCutoff_support

/-- Fixed bounds for every derivative, chosen independently of all analytic precisions. -/
theorem dyadicCutoff_derivative_bounds :
    ∃ bounds : ℕ → ℝ, (∀ j, 0 ≤ bounds j) ∧
      ∀ j y, ‖iteratedDeriv j dyadicCutoff y‖ ≤ bounds j := by
  have hb (j : ℕ) := dyadicCutoff_compact.exists_bound_iteratedFDeriv
    dyadicCutoff_contDiff j
  choose bounds hpos hb using hb
  exact ⟨bounds, hpos, fun j y => by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hb j j le_rfl y⟩

/-- The finite partition telescopes exactly. -/
theorem dyadicCutoff_sum (z Z : ℝ) (hZ : Z ≠ 0) (N : ℕ) :
    (∑ j ∈ Finset.range N, dyadicCutoff (z / (Z * 2 ^ j))) =
      dyadicStep (z / Z) - dyadicStep (z / (Z * 2 ^ N)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, dyadicCutoff]
    have heq : z / (Z * 2 ^ N) / 2 = z / (Z * 2 ^ (N + 1)) := by
      rw [pow_succ]
      field_simp
    rw [heq]
    ring

/-- Partition of unity on every positive range covered by the chosen dyads. -/
theorem dyadicCutoff_sum_one (z Z : ℝ) (hZ : 0 < Z) (N : ℕ)
    (hlow : Z ≤ z) (hhigh : z ≤ Z * 2 ^ N / 2) :
    (∑ j ∈ Finset.range N, dyadicCutoff (z / (Z * 2 ^ j))) = 1 := by
  rw [dyadicCutoff_sum z Z hZ.ne' N]
  unfold dyadicStep
  have hlow' : 1 ≤ z / Z := (le_div_iff₀ hZ).mpr (by simpa using hlow)
  have hhigh' : z / (Z * 2 ^ N) ≤ 1 / 2 :=
    (div_le_iff₀ (mul_pos hZ (by positivity))).mpr (by linarith)
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring


end Erdos821.P6Off
