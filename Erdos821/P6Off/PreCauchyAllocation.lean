import Erdos821.P6Off.PreCauchyFourier
import Erdos821.S56.WeightBound

noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

theorem clipped_branch_nonneg (n : ℕ) (target R : ℝ) (v s : Fin n → ℝ)
    (delta : Fin n → Bool) : 0 ≤ clippedBranchMass n target v s R delta :=
  Finset.prod_nonneg (fun i _ => (transition_bounds R _ (delta i)).1)

theorem clipped_branch_sum_le_one (n : ℕ) (target R : ℝ) (v s : Fin n → ℝ) :
    (∑ delta : Fin n → Bool, clippedBranchMass n target v s R delta) ≤ 1 := by
  rw [← Erdos821.S56.branch_partition_proved n target v s Real.smoothTransition]
  apply Finset.sum_le_sum
  intro delta _
  unfold clippedBranchMass Erdos821.S56.branchMass
  apply Finset.prod_le_prod₀
  · intro i _
    exact (transition_bounds R _ (delta i)).1
  · intro i _
    have hw := window_bounds R ((Erdos821.S56.residual target v delta i.val-v i)/s i)
    have hg := Real.smoothTransition.nonneg ((Erdos821.S56.residual target v delta i.val-v i)/s i)
    have hg1 := Real.smoothTransition.le_one ((Erdos821.S56.residual target v delta i.val-v i)/s i)
    cases delta i <;> simp only [transition, Bool.false_eq_true, ↓reduceIte]
    · nlinarith
    · nlinarith

def allocationMass (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (emin E : ℝ) : ℝ :=
  ∑ delta : ProcessedIndex D x jstar → Bool,
    if processedFactor D z delta ∈ Finset.Icc ⌈emin⌉₊ ⌊E⌋₊ then
      clippedBranchMass (pureIndices D x jstar).card (Real.log E)
        (processedLog D z) (processedScale D x jstar) (argumentRadius D) delta
    else 0

theorem allocationMass_bounds (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (emin E : ℝ) :
    0 ≤ allocationMass D z emin E ∧ allocationMass D z emin E ≤ 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro delta _
    split_ifs
    · exact clipped_branch_nonneg _ _ _ _ _ _
    · exact le_rfl
  · apply le_trans _ (clipped_branch_sum_le_one (pureIndices D x jstar).card
      (Real.log E) (argumentRadius D) (processedLog D z) (processedScale D x jstar))
    apply Finset.sum_le_sum
    intro delta _
    split_ifs
    · exact le_rfl
    · exact clipped_branch_nonneg _ _ _ _ _ _

def factorialNormalization (D : BandData) (x : ℝ) : ℝ :=
  ((D.r₀.factorial : ℝ)^(D.last x+1))⁻¹

theorem factorialNormalization_pos (D : BandData) (x : ℝ) :
    0 < factorialNormalization D x := by
  unfold factorialNormalization
  positivity

def allocatedWeight (D : BandData) (x : ℝ) (jstar : ℕ) (emin E : ℝ) (u : ℕ) : ℝ :=
  factorialNormalization D x * markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u *
    ∑ z : D.Lists x jstar,
      if D.listProduct z = groupFreePart (D.groups x) u then allocationMass D z emin E else 0

theorem weight_as_list_sum (D : BandData) (x : ℝ) (jstar u : ℕ) :
    D.weight x jstar u =
      factorialNormalization D x * markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u *
        ∑ z : D.Lists x jstar, if D.listProduct z = groupFreePart (D.groups x) u then (1:ℝ) else 0 := by
  simp only [BandData.weight, BandData.aQ, factorialNormalization]
  simp
  ring

theorem allocatedWeight_bounds (D : BandData) (x : ℝ) (jstar : ℕ) (emin E : ℝ) (u : ℕ) :
    0 ≤ allocatedWeight D x jstar emin E u ∧ allocatedWeight D x jstar emin E u ≤ D.weight x jstar u := by
  have hmark := markWeight_nonneg (D.groups x) D.geometry.q D.geometry.damping.1.le
    (fun _ => D.geometry.ell) u
  have hfac := (factorialNormalization_pos D x).le
  constructor
  · unfold allocatedWeight
    apply mul_nonneg (mul_nonneg hfac hmark)
    apply Finset.sum_nonneg
    intro z _
    split_ifs
    · exact (allocationMass_bounds D z emin E).1
    · exact le_rfl
  · rw [weight_as_list_sum]
    unfold allocatedWeight
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hfac hmark)
    apply Finset.sum_le_sum
    intro z _
    split_ifs
    · exact (allocationMass_bounds D z emin E).2
    · exact le_rfl

theorem allocationMass_eq_one (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (emin E : ℝ) (hE : 0 ≤ E)
    (hpart : (∑ delta : ProcessedIndex D x jstar → Bool,
      clippedBranchMass (pureIndices D x jstar).card (Real.log E)
        (processedLog D z) (processedScale D x jstar) (argumentRadius D) delta) = 1)
    (hrange : ∀ delta : ProcessedIndex D x jstar → Bool,
      0 < clippedBranchMass (pureIndices D x jstar).card (Real.log E)
        (processedLog D z) (processedScale D x jstar) (argumentRadius D) delta →
      emin ≤ (processedFactor D z delta : ℝ) ∧ (processedFactor D z delta : ℝ) ≤ E) :
    allocationMass D z emin E = 1 := by
  rw [allocationMass, ← hpart]
  apply Finset.sum_congr rfl
  intro delta _
  by_cases hpos : 0 < clippedBranchMass (pureIndices D x jstar).card (Real.log E)
      (processedLog D z) (processedScale D x jstar) (argumentRadius D) delta
  · have hr := hrange delta hpos
    have hmem : processedFactor D z delta ∈ Finset.Icc ⌈emin⌉₊ ⌊E⌋₊ :=
      Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hr.1, (Nat.le_floor_iff hE).mpr hr.2⟩
    rw [if_pos hmem]
  · have hz := le_antisymm (le_of_not_gt hpos) (clipped_branch_nonneg _ _ _ _ _ _)
    simp only [hz, ite_self]

theorem allocatedWeight_eq_of_partition (D : BandData) (x : ℝ) (jstar : ℕ)
    (emin E : ℝ) (u : ℕ)
    (h : ∀ z : D.Lists x jstar, D.listProduct z = groupFreePart (D.groups x) u →
      allocationMass D z emin E = 1) :
    allocatedWeight D x jstar emin E u = D.weight x jstar u := by
  rw [weight_as_list_sum]
  unfold allocatedWeight
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  split_ifs with hz
  · exact h z hz
  · rfl


end Erdos821.P6Off
