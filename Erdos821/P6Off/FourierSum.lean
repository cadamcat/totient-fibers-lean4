import Erdos821.P6Off.PulledCutoff

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic

@[simp] theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by
  simp [Blueprint.Analytic.e, Complex.norm_exp]

def frequencySum {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (y : ι → (Fin 3 → ℝ)) (xi : Fin 3 → ℝ) : ℂ :=
  ∑ i ∈ s, w i * e (∑ j, xi j * y i j)

theorem continuous_frequencySum {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (y : ι → (Fin 3 → ℝ)) : Continuous (frequencySum s w y) := by
  unfold frequencySum Blueprint.Analytic.e
  fun_prop

theorem norm_frequencySum_le {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (y : ι → (Fin 3 → ℝ)) (xi : Fin 3 → ℝ) :
    ‖frequencySum s w y xi‖ ≤ ∑ i ∈ s, ‖w i‖ := by
  simpa [frequencySum, norm_mul] using
    (norm_sum_le s (fun i => w i * e (∑ j, xi j * y i j)))

theorem integrable_frequencySum_mul {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (y : ι → (Fin 3 → ℝ)) (a : (Fin 3 → ℝ) → ℂ) (ha : Integrable a) :
    Integrable (fun xi => a xi * frequencySum s w y xi) :=
  ha.mul_bdd (continuous_frequencySum s w y).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_frequencySum_le s w y))

/-- A finite weighted sum may be passed through the exact Fourier integral. -/
theorem finite_Fourier_sum {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (y : ι → (Fin 3 → ℝ)) (F a : (Fin 3 → ℝ) → ℂ) (ha : Integrable a)
    (hF : ∀ t, F t = ∫ xi, a xi * e (∑ j, xi j * t j)) :
    (∑ i ∈ s, w i * F (y i)) = ∫ xi, a xi * frequencySum s w y xi := by
  have hphase_cont (i : ι) : Continuous (fun xi : Fin 3 → ℝ => e (∑ j, xi j * y i j)) := by
    unfold Blueprint.Analytic.e
    fun_prop
  have hphase (i : ι) : Integrable (fun xi : Fin 3 → ℝ => a xi * e (∑ j, xi j * y i j)) :=
    ha.mul_bdd (hphase_cont i).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ => le_of_eq (norm_e _)))
  calc
    _ = ∑ i ∈ s, ∫ xi, w i * (a xi * e (∑ j, xi j * y i j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hF, integral_const_mul]
    _ = ∫ xi, ∑ i ∈ s, w i * (a xi * e (∑ j, xi j * y i j)) :=
      (integral_finsetSum s (fun i _ => (hphase i).const_mul (w i))).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun xi => by
        simp only [frequencySum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring)

/-- The Fourier main range uses its correlation bound; the complement uses
an absolute finite-sum bound. Both pieces read the same coefficient measure. -/
theorem frequency_integral_bound {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (y : ι → (Fin 3 → ℝ)) (a : (Fin 3 → ℝ) → ℂ) (ha : Integrable a)
    (S : Set (Fin 3 → ℝ)) (hS : MeasurableSet S) (M : ℝ)
    (hmain : ∀ xi ∈ S, ‖frequencySum s w y xi‖ ≤ M) :
    ‖∫ xi, a xi * frequencySum s w y xi‖ ≤
      (∫ xi in S, ‖a xi‖) * M +
        (∫ xi in Sᶜ, ‖a xi‖) * ∑ i ∈ s, ‖w i‖ := by
  have hglobal := integrable_frequencySum_mul s w y a ha
  rw [← integral_add_compl hS hglobal]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      _ ≤ ∫ xi in S, ‖a xi‖ * M := norm_integral_le_of_norm_le
        (ha.norm.integrableOn.mul_const M) (by
          filter_upwards [ae_restrict_mem hS] with xi hxi
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hmain xi hxi) (norm_nonneg _))
      _ = _ := integral_mul_const M _
  · calc
      _ ≤ ∫ xi in Sᶜ, ‖a xi‖ * ∑ i ∈ s, ‖w i‖ := norm_integral_le_of_norm_le
        (ha.norm.integrableOn.mul_const _) (Filter.Eventually.of_forall (fun xi => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_frequencySum_le s w y xi) (norm_nonneg _)))
      _ = _ := integral_mul_const _ _


end Erdos821.P6Off
