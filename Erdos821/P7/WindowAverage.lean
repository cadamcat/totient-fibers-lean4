import Erdos821.P7.ConditionedMass
import Erdos821.P7.HarmonicPTruncation
import Erdos821.P7.PrefixHarmonicTask

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem freeWindow_average_upper (C : CandidateData)
    (hpsi : Function.support C.psi ⊆ Set.Icc 1 2)
    (x : ℝ) (hx : 0 < x) (jstar : ℕ) (s : C.bands.Slot x)
    (v : ℕ) (hv : 0 < v) (K : ℝ)
    (hsum : Summable (groupHarmonicTerm C.bands.geometry (C.bands.groups x)))
    (hupper : ∀ r : ℕ, 0 < r → freeWindowKernel C x jstar s v r ≤ K) :
    (∑' r : ℕ, groupHarmonicTerm C.bands.geometry (C.bands.groups x) r *
      freeWindowKernel C x jstar s v r) ≤ K * C.bands.harmonicP x := by
  calc
    _ ≤ ∑' r : ℕ, groupHarmonicTerm C.bands.geometry (C.bands.groups x) r * K := by
      apply Summable.tsum_le_tsum _
        (freeWindow_weighted_summable C hpsi x hx jstar s v hv _) (hsum.mul_right K)
      intro r
      by_cases hr : 0 < r
      · exact mul_le_mul_of_nonneg_left (hupper r hr)
          (groupHarmonicTerm_nonneg _ _ r)
      · have hr0 : r = 0 := by omega
        simp [hr0, groupHarmonicTerm]
    _ = K * C.bands.harmonicP x := by
      rw [tsum_mul_right]
      change C.bands.harmonicP x * K = _
      ring

theorem freeWindow_average_lower (C : CandidateData)
    (hpsi : Function.support C.psi ⊆ Set.Icc 1 2) (hpsi0 : ∀ y, 0 ≤ C.psi y)
    (x : ℝ) (hx : 0 < x) (jstar : ℕ) (s : C.bands.Slot x)
    (v : ℕ) (hv : 0 < v) (K Y : ℝ) (hK : 0 ≤ K)
    (hsum : Summable (groupHarmonicTerm C.bands.geometry (C.bands.groups x)))
    (hhead : C.bands.harmonicP x / 2 ≤ ∑' r : ℕ,
      if (r : ℝ) ≤ Y then groupHarmonicTerm C.bands.geometry (C.bands.groups x) r else 0)
    (hlower : ∀ r : ℕ, 0 < r → (r : ℝ) ≤ Y → K ≤ freeWindowKernel C x jstar s v r) :
    K * (C.bands.harmonicP x / 2) ≤
      ∑' r : ℕ, groupHarmonicTerm C.bands.geometry (C.bands.groups x) r *
        freeWindowKernel C x jstar s v r := by
  have hheadsum : Summable (fun r : ℕ => if (r : ℝ) ≤ Y then
      groupHarmonicTerm C.bands.geometry (C.bands.groups x) r else 0) := by
    apply Summable.of_nonneg_of_le _ _ hsum
    · intro r; split_ifs; exact groupHarmonicTerm_nonneg _ _ r; exact le_rfl
    · intro r; split_ifs; exact le_rfl; exact groupHarmonicTerm_nonneg _ _ r
  calc
    _ ≤ K * (∑' r : ℕ, if (r : ℝ) ≤ Y then
        groupHarmonicTerm C.bands.geometry (C.bands.groups x) r else 0) :=
      mul_le_mul_of_nonneg_left hhead hK
    _ = ∑' r : ℕ, (if (r : ℝ) ≤ Y then
        groupHarmonicTerm C.bands.geometry (C.bands.groups x) r else 0) * K := by
      rw [tsum_mul_right]
      ring
    _ ≤ _ := by
      apply Summable.tsum_le_tsum _ (hheadsum.mul_right K)
        (freeWindow_weighted_summable C hpsi x hx jstar s v hv _)
      intro r
      by_cases hsmall : (r : ℝ) ≤ Y
      · rw [if_pos hsmall]
        by_cases hr : 0 < r
        · exact mul_le_mul_of_nonneg_left (hlower r hr hsmall)
            (groupHarmonicTerm_nonneg _ _ r)
        · have hr0 : r = 0 := by omega
          simp [hr0, groupHarmonicTerm]
      · rw [if_neg hsmall, zero_mul]
        exact mul_nonneg (groupHarmonicTerm_nonneg _ _ r)
          (freeWindowKernel_nonneg C hpsi0 x jstar s v r)

theorem mass_rest_upper (C : CandidateData)
    (hpsi : Function.support C.psi ⊆ Set.Icc 1 2)
    (x : ℝ) (hx : 0 < x) (jstar : ℕ) (s : C.bands.Slot x) (K : ℝ)
    (hsum : Summable (groupHarmonicTerm C.bands.geometry (C.bands.groups x)))
    (hmass : C.mass x jstar =
      ((C.bands.r₀.factorial : ℝ) ^ (C.bands.last x + 1))⁻¹ *
        ∑ z : RestLists C.bands x jstar s, (restProduct C.bands z : ℝ)⁻¹ *
          ∑' r : ℕ, groupHarmonicTerm C.bands.geometry (C.bands.groups x) r *
            freeWindowKernel C x jstar s (restProduct C.bands z) r)
    (hupper : ∀ z : RestLists C.bands x jstar s, ∀ r : ℕ, 0 < r →
      freeWindowKernel C x jstar s (restProduct C.bands z) r ≤ K) :
    C.mass x jstar ≤
      ((C.bands.r₀.factorial : ℝ) ^ (C.bands.last x + 1))⁻¹ *
        restHarmonic C.bands x jstar s * K * C.bands.harmonicP x := by
  rw [hmass]
  calc
    _ ≤ ((C.bands.r₀.factorial : ℝ) ^ (C.bands.last x + 1))⁻¹ *
        ∑ z : RestLists C.bands x jstar s,
          (restProduct C.bands z : ℝ)⁻¹ * (K * C.bands.harmonicP x) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left
        (freeWindow_average_upper C hpsi x hx jstar s _ (restProduct_pos C.bands z)
          K hsum (hupper z)) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul]
      simp only [restHarmonic]
      ring

theorem mass_rest_lower (C : CandidateData)
    (hpsi : Function.support C.psi ⊆ Set.Icc 1 2) (hpsi0 : ∀ y, 0 ≤ C.psi y)
    (x : ℝ) (hx : 0 < x) (jstar : ℕ) (s : C.bands.Slot x)
    (epsilon c K Y : ℝ) (hK : 0 ≤ K)
    (hsum : Summable (groupHarmonicTerm C.bands.geometry (C.bands.groups x)))
    (hmass : C.mass x jstar =
      ((C.bands.r₀.factorial : ℝ) ^ (C.bands.last x + 1))⁻¹ *
        ∑ z : RestLists C.bands x jstar s, (restProduct C.bands z : ℝ)⁻¹ *
          ∑' r : ℕ, groupHarmonicTerm C.bands.geometry (C.bands.groups x) r *
            freeWindowKernel C x jstar s (restProduct C.bands z) r)
    (hprefix : c * restHarmonic C.bands x jstar s ≤
      ∑ z : RestLists C.bands x jstar s,
        if restPrefixEvent C epsilon s z then (restProduct C.bands z : ℝ)⁻¹ else 0)
    (hhead : C.bands.harmonicP x / 2 ≤ ∑' r : ℕ,
      if (r : ℝ) ≤ Y then groupHarmonicTerm C.bands.geometry (C.bands.groups x) r else 0)
    (hlower : ∀ z : RestLists C.bands x jstar s, restPrefixEvent C epsilon s z →
      ∀ r : ℕ, 0 < r → (r : ℝ) ≤ Y →
        K ≤ freeWindowKernel C x jstar s (restProduct C.bands z) r) :
    ((C.bands.r₀.factorial : ℝ) ^ (C.bands.last x + 1))⁻¹ *
      (c * restHarmonic C.bands x jstar s) * (K * (C.bands.harmonicP x / 2)) ≤
        C.mass x jstar := by
  have hP : 0 ≤ C.bands.harmonicP x := tsum_nonneg (groupHarmonicTerm_nonneg _ _)
  have hKP : 0 ≤ K * (C.bands.harmonicP x / 2) := by positivity
  rw [hmass]
  calc
    _ ≤ ((C.bands.r₀.factorial : ℝ) ^ (C.bands.last x + 1))⁻¹ *
        (∑ z : RestLists C.bands x jstar s,
          if restPrefixEvent C epsilon s z then (restProduct C.bands z : ℝ)⁻¹ else 0) *
            (K * (C.bands.harmonicP x / 2)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprefix (by positivity)) hKP
    _ = ((C.bands.r₀.factorial : ℝ) ^ (C.bands.last x + 1))⁻¹ *
        ∑ z : RestLists C.bands x jstar s,
          if restPrefixEvent C epsilon s z then
            (restProduct C.bands z : ℝ)⁻¹ * (K * (C.bands.harmonicP x / 2)) else 0 := by
      rw [mul_assoc, Finset.sum_mul]
      simp only [ite_mul, zero_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : restPrefixEvent C epsilon s z
      · rw [if_pos hz]
        exact mul_le_mul_of_nonneg_left
          (freeWindow_average_lower C hpsi hpsi0 x hx jstar s _
            (restProduct_pos C.bands z) K Y hK hsum hhead (hlower z hz)) (by positivity)
      · rw [if_neg hz]
        apply mul_nonneg (by positivity)
        exact tsum_nonneg (fun r => mul_nonneg (groupHarmonicTerm_nonneg _ _ r)
          (freeWindowKernel_nonneg C hpsi0 x jstar s _ r))

end Erdos821.P7Core

