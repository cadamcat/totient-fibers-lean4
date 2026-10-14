import Erdos821.S9.AssignmentHarmonic
import Erdos821.P7.FreeCoordinate

noncomputable section
open scoped BigOperators
namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P9Core

theorem assignmentCoefficient_nonneg (C : CandidateData) (x : ℝ) :
    0 ≤ assignmentCoefficient C x := by
  unfold assignmentCoefficient listNormalizer
  apply mul_nonneg
  · positivity
  · apply Finset.prod_nonneg
    intro g hg
    apply inv_nonneg.mpr
    unfold mass
    positivity

theorem assignmentModulus_pos (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (m : MicroAssignments C x jstar) (marks : GlobalMarkChoices (C.bands.groups x)) :
    0 < assignmentModulus C x jstar m marks := by
  apply Nat.mul_pos
  · exact Finset.prod_pos (fun s _ => Erdos821.P7Core.slotValue_pos C.bands (m s))
  · exact Finset.prod_pos (fun g _ =>
      ((C.bands.groups x).prime g _ (marks g).property).pos)

theorem assignmentModulus_le_x_one_twentieth
    (C : CandidateData) (δ x : ℝ) (jstar : ℕ) (hC : C.Geometry δ)
    (hAdm : Admissible C.bands.geometry x (C.bands.groups x))
    (hx : 1 < x) (hL : 1 ≤ L x)
    (hLpow : 2000 * C.bands.geometry.C₀ ≤ L x ^ (1 / 2 : ℝ))
    (m : MicroAssignments C x jstar) (marks : GlobalMarkChoices (C.bands.groups x)) :
    (assignmentModulus C x jstar m marks : ℝ) ≤ x ^ (1 / 20 : ℝ) := by
  classical
  let G := C.bands.groups x
  let u := globalMarkProduct G marks
  let divisors : MarkChoices G u := fun g => ⟨(marks g).val,
    Finset.mem_filter.mpr ⟨(marks g).property,
      Finset.dvd_prod_of_mem (fun g => (marks g).val) (Finset.mem_univ g)⟩⟩
  have heq : markProduct G u divisors = globalMarkProduct G marks := rfl
  have h := candidate_micro_mark_product_le_x_one_twentieth C δ x jstar u
    hC hAdm hx hL hLpow m divisors
  change ((microAssignmentProduct C x jstar m * markProduct G u divisors : ℕ) : ℝ) ≤
    x ^ (1 / 20 : ℝ) at h
  rw [heq] at h
  exact h

theorem assignment_coefficient_sum_le
    (C : CandidateData) (x H : ℝ) (jstar : ℕ)
    (hmass : ∀ g, 0 < mass (C.bands.groups x) g)
    (hsize : ∀ (m : MicroAssignments C x jstar)
      (marks : GlobalMarkChoices (C.bands.groups x)),
      (assignmentModulus C x jstar m marks : ℝ) ≤ H) :
    (∑ m : MicroAssignments C x jstar,
      ∑ marks : GlobalMarkChoices (C.bands.groups x), assignmentCoefficient C x) ≤
      H * microHarmonicMass C x jstar := by
  classical
  rw [← assignment_harmonic_sum C x jstar hmass]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  apply Finset.sum_le_sum
  intro marks ht
  have hD : (0 : ℝ) < assignmentModulus C x jstar m marks := by
    exact_mod_cast assignmentModulus_pos C x jstar m marks
  have hquot : 0 ≤ assignmentCoefficient C x /
      (assignmentModulus C x jstar m marks : ℝ) :=
    div_nonneg (assignmentCoefficient_nonneg C x) hD.le
  calc
    assignmentCoefficient C x = (assignmentModulus C x jstar m marks : ℝ) *
        (assignmentCoefficient C x / (assignmentModulus C x jstar m marks : ℝ)) := by
      field_simp
    _ ≤ H * (assignmentCoefficient C x /
        (assignmentModulus C x jstar m marks : ℝ)) :=
      mul_le_mul_of_nonneg_right (hsize m marks) hquot

theorem assignment_modulus_coefficient_sum_le
    (C : CandidateData) (x H : ℝ) (jstar : ℕ) (hH : 0 ≤ H)
    (hmass : ∀ g, 0 < mass (C.bands.groups x) g)
    (hsize : ∀ (m : MicroAssignments C x jstar)
      (marks : GlobalMarkChoices (C.bands.groups x)),
      (assignmentModulus C x jstar m marks : ℝ) ≤ H) :
    (∑ m : MicroAssignments C x jstar,
      ∑ marks : GlobalMarkChoices (C.bands.groups x),
        assignmentCoefficient C x * (assignmentModulus C x jstar m marks : ℝ)) ≤
      H ^ 2 * microHarmonicMass C x jstar := by
  classical
  calc
    _ ≤ H * (∑ m : MicroAssignments C x jstar,
        ∑ marks : GlobalMarkChoices (C.bands.groups x), assignmentCoefficient C x) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro marks ht
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hsize m marks)
        (assignmentCoefficient_nonneg C x)
    _ ≤ H * (H * microHarmonicMass C x jstar) :=
      mul_le_mul_of_nonneg_left (assignment_coefficient_sum_le C x H jstar hmass hsize) hH
    _ = H ^ 2 * microHarmonicMass C x jstar := by ring

end Erdos821.S56Core

