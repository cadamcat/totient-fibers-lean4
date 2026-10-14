import Erdos821.S9.AssignmentMoments
import Erdos821.S9.PairBudgetTask
import Erdos821.Blueprint.Balanced

noncomputable section
open scoped BigOperators
open Filter
namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P9Core
attribute [local instance] Classical.propDecidable

def assignmentPrimeLower (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (m : MicroAssignments C x jstar) (marks : GlobalMarkChoices (C.bands.groups x)) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ assignmentModulus C x jstar m marks →
    L x ^ (20 : ℕ) ≤ (p : ℝ)

def assignmentSiftedAverage (C : CandidateData) (x M N : ℝ) (jstar : ℕ)
    (m : MicroAssignments C x jstar) (marks : GlobalMarkChoices (C.bands.groups x)) : ℝ :=
  ∑ allow : PermissionIndex (assignmentMaskPrimes C x marks) → Bool,
    permissionMaskProbability (assignmentMaskPrimes C x marks) C.bands.geometry.q allow *
      (pairBudgetData C x M N (assignmentModulus C x jstar m marks)
        (assignmentMaskPrimes C x marks) (assignmentModulus_pos C x jstar m marks) allow).sifted

def assignmentSiftedSum (C : CandidateData) (x M N : ℝ) (jstar : ℕ) : ℝ :=
  ∑ m : MicroAssignments C x jstar,
    ∑ marks : GlobalMarkChoices (C.bands.groups x),
      if assignmentPrimeLower C x jstar m marks then
        assignmentCoefficient C x * assignmentSiftedAverage C x M N jstar m marks
      else 0

def AssignmentSiftedBridgeTask : Prop :=
  ∀ (δ : ℝ) (C : CandidateData), C.Geometry δ → C.Bounds δ →
    ∃ B : ℝ, 0 < B ∧ ∀ jstar : ℕ, C.j₀ ≤ jstar →
      ∀ᶠ x : ℝ in atTop, ∀ M N : ℝ,
        balancedRoughSum C x M N jstar ≤ B * assignmentSiftedSum C x M N jstar

end Erdos821.S56Core
