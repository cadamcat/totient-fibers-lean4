import Erdos821.S56.NextBand
import Erdos821.S56.GeometricScales
import Erdos821.S56.Transitions

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def processedFactor (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (delta : ProcessedIndex D x jstar → Bool) : ℕ :=
  ∏ i, if delta i then (z (processedSlot D x jstar i)).val else 1

theorem processed_factor_pos (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (delta : ProcessedIndex D x jstar → Bool) :
    0 < processedFactor D z delta := by
  apply Finset.prod_pos
  intro i _
  cases delta i <;> simp [slot_value_pos D z (processedSlot D x jstar i)]

theorem log_processed_factor (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (delta : ProcessedIndex D x jstar → Bool) :
    Real.log (processedFactor D z delta) =
      ∑ i, if delta i then processedLog D z i else 0 := by
  have hp (i : ProcessedIndex D x jstar) : (0 : ℝ) < (z (processedSlot D x jstar i)).val := by
    exact_mod_cast slot_value_pos D z (processedSlot D x jstar i)
  simp only [processedFactor, Nat.cast_prod]
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro i _
    cases delta i <;> simp [processedLog]
  · intro i _
    cases delta i <;> simp [(hp i).ne']

theorem processed_factor_residual (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (target : ℝ) (delta : ProcessedIndex D x jstar → Bool) :
    Erdos821.S56.residual target (processedLog D z) delta (pureIndices D x jstar).card =
      target - Real.log (processedFactor D z delta) := by
  simp only [Erdos821.S56.residual, log_processed_factor]
  have heq : Finset.univ.filter (fun t : ProcessedIndex D x jstar =>
      t.val < (pureIndices D x jstar).card) = Finset.univ :=
    Finset.filter_eq_self.mpr (fun t _ => t.isLt)
  rw [heq]

theorem literal_clipped_partition (D : BandData) (hD : D.Valid) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (hL : 0 < L x) (target : ℝ) (ht : 0 ≤ target)
    (hinit : target ≤ (∑ i, processedLog D z i) + (D.c₂ + 1) * D.scale x (D.last x)) :
    (∑ delta : ProcessedIndex D x jstar → Bool,
      clippedBranchMass (pureIndices D x jstar).card target
        (processedLog D z) (processedScale D x jstar) (argumentRadius D) delta) = 1 := by
  have hc2 : 0 < D.c₂ := hD.2.1.trans hD.2.2.1
  have hterm : 0 ≤ (D.c₂ + 1) * D.scale x (D.last x) :=
    mul_nonneg (by linarith) (scale_pos D hD x hL _).le
  apply clipped_branch_partition
  exact branch_argument_bound _ target _ _ _ _ ht hterm hinit
    (processed_log_pos D hD z hL) (processed_room D hD z hL) (processed_argument_cap D hD z hL)

/-- Every retained factor lies within the terminal logarithmic allowance of
the requested size. The allowance and transition radius contain no K₀. -/
theorem literal_allocation_range (D : BandData) (hD : D.Valid) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (hL : 0 < L x) (target : ℝ) (ht : 0 ≤ target)
    (hinit : target ≤ (∑ i, processedLog D z i) + (D.c₂ + 1) * D.scale x (D.last x))
    (delta : ProcessedIndex D x jstar → Bool)
    (hmass : 0 < clippedBranchMass (pureIndices D x jstar).card target
      (processedLog D z) (processedScale D x jstar) (argumentRadius D) delta) :
    Real.exp (target - (D.c₂ + 1) * D.scale x (D.last x)) ≤ (processedFactor D z delta : ℝ) ∧
      (processedFactor D z delta : ℝ) ≤ Real.exp target := by
  have hc2 : 0 < D.c₂ := hD.2.1.trans hD.2.2.1
  have hterm : 0 ≤ (D.c₂ + 1) * D.scale x (D.last x) :=
    mul_nonneg (by linarith) (scale_pos D hD x hL _).le
  have hv := processed_log_pos D hD z hL
  have hroom := processed_room D hD z hL
  have harg := branch_argument_bound _ target _ _ _ _ ht hterm hinit hv hroom
    (processed_argument_cap D hD z hL)
  rw [clipped_branch_eq _ _ _ _ _ _ (harg delta)] at hmass
  have hgamma : ∀ t, 0 ≤ Real.smoothTransition t ∧ Real.smoothTransition t ≤ 1 ∧
      (t ≤ 0 → Real.smoothTransition t = 0) ∧ (1 ≤ t → Real.smoothTransition t = 1) :=
    fun t => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t,
      Real.smoothTransition.zero_of_nonpos, Real.smoothTransition.one_of_one_le⟩
  obtain ⟨hlo, hhi⟩ := Erdos821.S56.branch_range_proved _ target _ _ _ Real.smoothTransition
    ht hterm hinit hv hgamma hroom delta hmass
  rw [processed_factor_residual] at hlo hhi
  have hp : (0 : ℝ) < processedFactor D z delta := by exact_mod_cast processed_factor_pos D z delta
  constructor
  · calc
      _ ≤ Real.exp (Real.log (processedFactor D z delta)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log hp
  · calc
      _ = Real.exp (Real.log (processedFactor D z delta)) := (Real.exp_log hp).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)


end Erdos821.S56Core
