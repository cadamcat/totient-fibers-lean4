import Erdos821.S9.AssignmentMoments

noncomputable section
open scoped BigOperators
namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P9Core

theorem mask_sieve_average_bound {α : Type*} [Fintype α]
    (prob count comp : α → ℝ) (K X B E HP : ℝ)
    (hprob : ∀ t, 0 ≤ prob t) (hsum : ∑ t, prob t = 1)
    (hK : 0 ≤ K) (hX : 0 ≤ X) (hB : 0 ≤ B)
    (hcomp : (∑ t, prob t * comp t) ≤ HP)
    (hcount : ∀ t, count t ≤ K * X * B * comp t + K * E) :
    (∑ t, prob t * count t) ≤ K * X * B * HP + K * E := by
  calc
    _ ≤ ∑ t, prob t * (K * X * B * comp t + K * E) :=
      Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hcount t) (hprob t))
    _ = K * X * B * (∑ t, prob t * comp t) + K * E * (∑ t, prob t) := by
      simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro t ht <;> ring
    _ ≤ K * X * B * HP + K * E := by
      rw [hsum, mul_one]
      exact add_le_add (mul_le_mul_of_nonneg_left hcomp
        (mul_nonneg (mul_nonneg hK hX) hB)) le_rfl

theorem assignment_sieve_sum_bound (C : CandidateData) (x H a b c : ℝ)
    (jstar : ℕ) (hH : 0 ≤ H) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hmass : ∀ g, 0 < mass (C.bands.groups x) g)
    (hsize : ∀ (m : MicroAssignments C x jstar)
      (marks : GlobalMarkChoices (C.bands.groups x)),
      (assignmentModulus C x jstar m marks : ℝ) ≤ H)
    (counts : MicroAssignments C x jstar → GlobalMarkChoices (C.bands.groups x) → ℝ)
    (hcounts : ∀ m marks, counts m marks ≤
      a / (assignmentModulus C x jstar m marks : ℝ) +
        b * (assignmentModulus C x jstar m marks : ℝ) + c) :
    (∑ m : MicroAssignments C x jstar,
      ∑ marks : GlobalMarkChoices (C.bands.groups x),
        assignmentCoefficient C x * counts m marks) ≤
      (a + b * H ^ 2 + c * H) * microHarmonicMass C x jstar := by
  classical
  let sumD := ∑ m : MicroAssignments C x jstar,
    ∑ marks : GlobalMarkChoices (C.bands.groups x),
      assignmentCoefficient C x * (assignmentModulus C x jstar m marks : ℝ)
  let sumOne := ∑ m : MicroAssignments C x jstar,
    ∑ marks : GlobalMarkChoices (C.bands.groups x), assignmentCoefficient C x
  calc
    _ ≤ ∑ m : MicroAssignments C x jstar,
        ∑ marks : GlobalMarkChoices (C.bands.groups x),
          assignmentCoefficient C x *
            (a / (assignmentModulus C x jstar m marks : ℝ) +
              b * (assignmentModulus C x jstar m marks : ℝ) + c) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro marks ht
      exact mul_le_mul_of_nonneg_left (hcounts m marks) (assignmentCoefficient_nonneg C x)
    _ = a * (∑ m : MicroAssignments C x jstar,
        ∑ marks : GlobalMarkChoices (C.bands.groups x),
          assignmentCoefficient C x / (assignmentModulus C x jstar m marks : ℝ)) +
        b * sumD + c * sumOne := by
      have hterm (m : MicroAssignments C x jstar)
          (marks : GlobalMarkChoices (C.bands.groups x)) :
          assignmentCoefficient C x *
            (a / (assignmentModulus C x jstar m marks : ℝ) +
              b * (assignmentModulus C x jstar m marks : ℝ) + c) =
            a * (assignmentCoefficient C x / (assignmentModulus C x jstar m marks : ℝ)) +
              b * (assignmentCoefficient C x * (assignmentModulus C x jstar m marks : ℝ)) +
                c * assignmentCoefficient C x := by ring
      simp_rw [hterm]
      simp only [sumD, sumOne, Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ a * microHarmonicMass C x jstar +
        b * (H ^ 2 * microHarmonicMass C x jstar) +
        c * (H * microHarmonicMass C x jstar) := by
      rw [assignment_harmonic_sum C x jstar hmass]
      exact add_le_add
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (assignment_modulus_coefficient_sum_le C x H jstar hH hmass hsize) hb))
        (mul_le_mul_of_nonneg_left
          (assignment_coefficient_sum_le C x H jstar hmass hsize) hc)
    _ = (a + b * H ^ 2 + c * H) * microHarmonicMass C x jstar := by ring

end Erdos821.S56Core

