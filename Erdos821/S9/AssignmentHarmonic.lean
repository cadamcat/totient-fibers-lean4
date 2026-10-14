import Erdos821.S9.AssignmentModel
import Erdos821.P9.AssignmentBounds

noncomputable section
open scoped BigOperators
open Filter
namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P9Core

theorem global_mark_normalized_harmonic_sum (G : PrimeGroups)
    (hmass : ∀ g, 0 < mass G g) :
    (∑ marks : GlobalMarkChoices G,
      (∏ g, (mass G g)⁻¹) / (globalMarkProduct G marks : ℝ)) = 1 := by
  classical
  have hterm (marks : GlobalMarkChoices G) :
      (∏ g, (mass G g)⁻¹) / (globalMarkProduct G marks : ℝ) =
        ∏ g, (mass G g)⁻¹ * ((marks g).val : ℝ)⁻¹ := by
    simp [globalMarkProduct, div_eq_mul_inv, Nat.cast_prod,
      Finset.prod_inv_distrib, Finset.prod_mul_distrib]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun g (p : GlobalMarkOption G g) =>
    (mass G g)⁻¹ * (p.val : ℝ)⁻¹)]
  have hgroup (g : Fin G.size) :
      (∑ p : GlobalMarkOption G g, (mass G g)⁻¹ * (p.val : ℝ)⁻¹) = 1 := by
    rw [← Finset.mul_sum]
    have hsum : (∑ p : GlobalMarkOption G g, (p.val : ℝ)⁻¹) = mass G g := by
      simpa only [mass, one_div] using
        Finset.sum_coe_sort (G.primes g) (fun p : ℕ => (p : ℝ)⁻¹)
    rw [hsum, inv_mul_cancel₀ (hmass g).ne']
  simp only [hgroup, Finset.prod_const_one]

theorem assignment_harmonic_sum (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (hmass : ∀ g, 0 < mass (C.bands.groups x) g) :
    (∑ m : MicroAssignments C x jstar,
      ∑ marks : GlobalMarkChoices (C.bands.groups x),
        assignmentCoefficient C x / (assignmentModulus C x jstar m marks : ℝ)) =
      microHarmonicMass C x jstar := by
  classical
  let F : ℝ := listNormalizer C.bands x * (Fintype.card (MacroSlotIndex C)).factorial
  have hterm (m : MicroAssignments C x jstar)
      (marks : GlobalMarkChoices (C.bands.groups x)) :
      assignmentCoefficient C x / (assignmentModulus C x jstar m marks : ℝ) =
        (F * (microAssignmentProduct C x jstar m : ℝ)⁻¹) *
          ((∏ g, (mass (C.bands.groups x) g)⁻¹) /
            (globalMarkProduct (C.bands.groups x) marks : ℝ)) := by
    simp only [assignmentCoefficient, assignmentModulus, Nat.cast_mul,
      div_eq_mul_inv, mul_inv_rev, F]
    ring
  simp_rw [hterm, ← Finset.mul_sum,
    global_mark_normalized_harmonic_sum _ hmass, mul_one]
  rw [← Finset.mul_sum, micro_assignment_harmonic_mass]
  rfl

theorem microHarmonicMass_le_harmonicQ_eventually
    (hc : ClassicalInputs) (C : CandidateData) (δ : ℝ) (hC : C.Geometry δ)
    (jstar : ℕ) (hj : C.micro ≤ jstar) :
    ∀ᶠ x : ℝ in atTop,
      microHarmonicMass C x jstar ≤
        ((Fintype.card (MacroSlotIndex C)).factorial : ℝ) *
          (12 : ℝ) ^ (C.micro * C.bands.r₀) * C.bands.harmonicQ x jstar := by
  exact normalized_micro_harmonic_le_harmonicQ_eventually C δ jstar hC hj hc.mertens.2

end Erdos821.S56Core

