import Erdos821.S56.SlotSplitTasks
import Erdos821.S56.FourierCost
import Erdos821.S56.SmoothAllocation

noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

theorem integral_box_prod (n : ℕ) (R : ℝ) (g : Fin n → ℝ → ℂ) :
    (∫ xi in {xi : Fin n → ℝ | ∀ i, ‖xi i‖ ≤ R}, ∏ i, g i (xi i)) =
      ∏ i, ∫ xi in {xi : ℝ | ‖xi‖ ≤ R}, g i xi := by
  have hbox : {xi : Fin n → ℝ | ∀ i, ‖xi i‖ ≤ R} =
      Set.pi Set.univ (fun _ : Fin n => {xi : ℝ | ‖xi‖ ≤ R}) := by
    ext xi
    simp
  rw [hbox, volume_pi, Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod g

theorem truncated_branch_fourier_identity (n : ℕ) (R target : ℝ)
    (v s : Fin n → ℝ) (a : Bool → ℝ → ℂ) (delta : Fin n → Bool) :
    (∏ i, ∫ xi in {xi : ℝ | ‖xi‖ ≤ R},
      a (delta i) xi * e (xi * ((Erdos821.S56.residual target v delta i.val-v i)/s i))) =
    ∫ xi in {xi : Fin n → ℝ | ∀ i, ‖xi i‖ ≤ R},
      branchFourierCoefficient n a delta xi * e (target*∑ i, xi i/s i) *
        ∏ i, e (Erdos821.S56.slotFrequency s xi delta i*v i) := by
  rw [← integral_box_prod]
  apply integral_congr_ae
  filter_upwards with xi
  simp only [Finset.prod_mul_distrib]
  have hsep := slot_phase_separation n target v s xi delta
  simp only [mul_div_assoc] at hsep
  rw [hsep]
  simp only [branchFourierCoefficient, mul_assoc]

theorem processed_phase_mellin (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (delta : ProcessedIndex D x jstar → Bool)
    (xi : ProcessedIndex D x jstar → ℝ) :
    (∏ i, e (Erdos821.S56.slotFrequency (processedScale D x jstar) xi delta i *
      processedLog D z i)) =
    ∏ i, mellin (z (processedSlot D x jstar i)).val
      (2*Real.pi*Erdos821.S56.slotFrequency (processedScale D x jstar) xi delta i) := by
  apply Finset.prod_congr rfl
  intro i _
  unfold e Erdos821.Blueprint.Analytic.mellin processedLog
  congr 1
  push_cast
  ring


end Erdos821.P6Off
