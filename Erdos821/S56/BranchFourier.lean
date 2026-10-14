import Erdos821.S56.Transitions
import Erdos821.S56.SlotFrequencies

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint.Analytic

theorem e_add (s t : ℝ) : e (s + t) = e s * e t := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem e_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    e (∑ i ∈ s, f i) = ∏ i ∈ s, e (f i) := by
  unfold e
  rw [← Complex.exp_sum]
  congr 1
  simp [Finset.sum_mul, Finset.mul_sum, mul_assoc]

theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by simp [e, Complex.norm_exp]

theorem slot_phase_separation (n : ℕ) (target : ℝ) (v s xi : Fin n → ℝ)
    (delta : Fin n → Bool) :
    (∏ i, e (xi i * (Erdos821.S56.residual target v delta i.val - v i) / s i)) =
      e (target * ∑ i, xi i / s i) *
        ∏ t, e (Erdos821.S56.slotFrequency s xi delta t * v t) := by
  rw [← e_sum, Erdos821.S56.slot_frequency_sum, e_add, e_sum]

def branchFourierCoefficient (n : ℕ) (a : Bool → ℝ → ℂ)
    (delta : Fin n → Bool) (xi : Fin n → ℝ) : ℂ := ∏ i, a (delta i) (xi i)

theorem branch_coefficient_integrable (n : ℕ) (a : Bool → ℝ → ℂ)
    (ha : ∀ b, Integrable (a b)) (delta : Fin n → Bool) :
    Integrable (branchFourierCoefficient n a delta) :=
  Integrable.fintype_prod (fun i => ha (delta i))

theorem branch_coefficient_mass (n : ℕ) (a : Bool → ℝ → ℂ)
    (delta : Fin n → Bool) :
    (∫ xi : Fin n → ℝ, ‖branchFourierCoefficient n a delta xi‖) =
      ∏ i, ∫ xi : ℝ, ‖a (delta i) xi‖ := by
  simp only [branchFourierCoefficient, norm_prod]
  exact integral_fintype_prod_volume_eq_prod (fun (i : Fin n) (xi : ℝ) => ‖a (delta i) xi‖)

/-- Fixed one-variable transition coefficients are tensored, so the number
of slots may grow with x without changing a Fourier-separation constant. -/
theorem branch_fourier_identity (n : ℕ) (R target : ℝ) (v s : Fin n → ℝ)
    (a : Bool → ℝ → ℂ)
    (ha : ∀ b t, (transition R b t : ℂ) = ∫ xi, a b xi * e (xi * t))
    (delta : Fin n → Bool) :
    (clippedBranchMass n target v s R delta : ℂ) =
      ∫ xi : Fin n → ℝ, branchFourierCoefficient n a delta xi *
        e (target * ∑ i, xi i / s i) *
          ∏ t, e (Erdos821.S56.slotFrequency s xi delta t * v t) := by
  simp only [clippedBranchMass, Complex.ofReal_prod]
  simp_rw [ha]
  rw [← integral_fintype_prod_volume_eq_prod]
  apply integral_congr_ae
  filter_upwards with xi
  simp only [Finset.prod_mul_distrib]
  have hsep := slot_phase_separation n target v s xi delta
  simp only [mul_div_assoc] at hsep
  rw [hsep]
  simp only [branchFourierCoefficient, mul_assoc]

theorem transition_fourier_coefficients (R : ℝ) :
    ∃ a : Bool → ℝ → ℂ,
      (∀ b, Integrable (a b)) ∧
      (∀ b n, Integrable (fun xi => ‖xi‖ ^ n * ‖a b xi‖)) ∧
      ∀ b t, (transition R b t : ℂ) = ∫ xi, a b xi * e (xi * t) := by
  have h (b : Bool) : ∃ a : ℝ → ℂ, MeasureTheory.Integrable a ∧
      (∀ n : ℕ, Integrable (fun xi => ‖xi‖ ^ n * ‖a xi‖)) ∧
      ∀ t, (transition R b t : ℂ) = ∫ xi, a xi * e (xi * t) := by
    have hd : ContDiff ℝ ∞ (fun t => (transition R b t : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (transition_smooth R b)
    have hc : HasCompactSupport (fun t => (transition R b t : ℂ)) :=
      (transition_compact R b).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    exact fixed_fourier _ hd hc
  choose a ha hm heq using h
  exact ⟨a, ha, hm, heq⟩

theorem branch_total_mass (n : ℕ) (a : Bool → ℝ → ℂ) :
    (∑ delta : Fin n → Bool, ∫ xi : Fin n → ℝ, ‖branchFourierCoefficient n a delta xi‖) =
      ((∫ xi : ℝ, ‖a false xi‖) + ∫ xi : ℝ, ‖a true xi‖) ^ n := by
  simp_rw [branch_coefficient_mass]
  simpa [add_comm] using
    (Fintype.sum_pow (fun b : Bool => ∫ xi : ℝ, ‖a b xi‖) n).symm


end Erdos821.S56Core
