import Erdos821.P6Off.PreCauchyAllocation
import Erdos821.S56.PreCauchyTask

noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

theorem real_cast_ite (p : Prop) [Decidable p] (r s : ℝ) :
    ((if p then r else s : ℝ) : ℂ) = if p then (r:ℂ) else (s:ℂ) := by
  split_ifs <;> rfl

def truncatedAllocationMass (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (emin E : ℝ) (a : Bool → ℝ → ℂ) : ℂ :=
  ∑ delta : ProcessedIndex D x jstar → Bool,
    if processedFactor D z delta ∈ Finset.Icc ⌈emin⌉₊ ⌊E⌋₊ then
      truncatedBranch (pureIndices D x jstar).card a (L x) (Real.log E)
        (processedLog D z) (processedScale D x jstar) delta
    else 0

def truncatedAllocatedWeight (D : BandData) (x : ℝ) (jstar : ℕ) (emin E : ℝ)
    (a : Bool → ℝ → ℂ) (u : ℕ) : ℂ :=
  (factorialNormalization D x * markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u : ℝ) *
    ∑ z : D.Lists x jstar,
      if D.listProduct z = groupFreePart (D.groups x) u then truncatedAllocationMass D z emin E a else 0

theorem allocationMass_truncation_error (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (emin E eps : ℝ) (a : Bool → ℝ → ℂ)
    (he : (∑ delta : ProcessedIndex D x jstar → Bool,
      ‖(clippedBranchMass (pureIndices D x jstar).card (Real.log E)
        (processedLog D z) (processedScale D x jstar) (argumentRadius D) delta : ℂ)-
        truncatedBranch (pureIndices D x jstar).card a (L x) (Real.log E)
          (processedLog D z) (processedScale D x jstar) delta‖) ≤ eps) :
    ‖(allocationMass D z emin E : ℂ)-truncatedAllocationMass D z emin E a‖ ≤ eps := by
  simp only [allocationMass, truncatedAllocationMass, Complex.ofReal_sum,
    real_cast_ite, Complex.ofReal_zero, ← Finset.sum_sub_distrib]
  apply le_trans (norm_sum_le _ _) (le_trans _ he)
  apply Finset.sum_le_sum
  intro delta _
  split_ifs
  · exact le_rfl
  · simp

set_option maxHeartbeats 800000 in
theorem allocatedWeight_truncation_error (D : BandData) (x : ℝ) (jstar : ℕ)
    (emin E eps : ℝ) (a : Bool → ℝ → ℂ) (u : ℕ)
    (he : ∀ z : D.Lists x jstar,
      ‖(allocationMass D z emin E : ℂ)-truncatedAllocationMass D z emin E a‖ ≤ eps) :
    ‖(allocatedWeight D x jstar emin E u : ℂ)-truncatedAllocatedWeight D x jstar emin E a u‖ ≤
      eps*D.weight x jstar u := by
  have hmark := markWeight_nonneg (D.groups x) D.geometry.q D.geometry.damping.1.le
    (fun _ => D.geometry.ell) u
  have hfac := (factorialNormalization_pos D x).le
  rw [weight_as_list_sum]
  simp only [allocatedWeight, truncatedAllocatedWeight, Complex.ofReal_mul, Complex.ofReal_sum,
    real_cast_ite, Complex.ofReal_zero, ← mul_sub, ← Finset.sum_sub_distrib,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfac, abs_of_nonneg hmark]
  calc
    _ ≤ factorialNormalization D x * markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u *
        ∑ z : D.Lists x jstar,
          ‖(if D.listProduct z = groupFreePart (D.groups x) u then (allocationMass D z emin E : ℂ) else 0)-
            (if D.listProduct z = groupFreePart (D.groups x) u then truncatedAllocationMass D z emin E a else 0)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (mul_nonneg hfac hmark)
    _ ≤ factorialNormalization D x * markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u *
        ∑ z : D.Lists x jstar, if D.listProduct z = groupFreePart (D.groups x) u then eps else 0 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hfac hmark)
      apply Finset.sum_le_sum
      intro z _
      split_ifs
      · exact he z
      · simp
    _ = eps*(factorialNormalization D x*markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u*
        ∑ z : D.Lists x jstar, if D.listProduct z = groupFreePart (D.groups x) u then (1:ℝ) else 0) := by
      have hid : (∑ z : D.Lists x jstar,
          if D.listProduct z = groupFreePart (D.groups x) u then eps else 0) =
          eps*∑ z : D.Lists x jstar,
            if D.listProduct z = groupFreePart (D.groups x) u then (1:ℝ) else 0 := by
        simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
      rw [hid]
      ring

def truncatedCutoff (f : ℝ → ℂ) (R : ℝ) (x : ℝ) (u : ℕ) : ℂ :=
  ∫ t in {t : ℝ | ‖t‖ ≤ R}, f t*e (t*(Real.log (u:ℝ)-Real.log x))

theorem allocated_cutoff_error (D : BandData) (x : ℝ) (jstar : ℕ)
    (emin E epsa epsf Mf : ℝ) (a : Bool → ℝ → ℂ) (f : ℝ → ℂ)
    (psi : ℝ → ℝ) (u : ℕ) (hea : 0 ≤ epsa) (hef : 0 ≤ epsf) (hMf : 0 ≤ Mf)
    (ha : ‖(allocatedWeight D x jstar emin E u : ℂ)-truncatedAllocatedWeight D x jstar emin E a u‖ ≤
      epsa*D.weight x jstar u)
    (hf : ‖(psi ((u:ℝ)/x) : ℂ)-truncatedCutoff f (L x) x u‖ ≤ epsf)
    (hfmass : ‖truncatedCutoff f (L x) x u‖ ≤ Mf) :
    ‖(allocatedWeight D x jstar emin E u*psi ((u:ℝ)/x) : ℝ)-
      truncatedAllocatedWeight D x jstar emin E a u*truncatedCutoff f (L x) x u‖ ≤
      (epsf+epsa*Mf)*D.weight x jstar u := by
  obtain ⟨hw0, hw⟩ := allocatedWeight_bounds D x jstar emin E u
  have hid : (allocatedWeight D x jstar emin E u*psi ((u:ℝ)/x) : ℝ)-
      truncatedAllocatedWeight D x jstar emin E a u*truncatedCutoff f (L x) x u =
      (allocatedWeight D x jstar emin E u : ℂ)*
        ((psi ((u:ℝ)/x) : ℂ)-truncatedCutoff f (L x) x u)+
      ((allocatedWeight D x jstar emin E u : ℂ)-truncatedAllocatedWeight D x jstar emin E a u)*
        truncatedCutoff f (L x) x u := by push_cast; ring
  rw [hid]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
  have h1 := mul_le_mul hw hf (norm_nonneg _) (band_weight_nonneg D x jstar u)
  have h2 := mul_le_mul ha hfmass (norm_nonneg _) (mul_nonneg hea (band_weight_nonneg D x jstar u))
  calc
    _ ≤ D.weight x jstar u*epsf+(epsa*D.weight x jstar u)*Mf := add_le_add h1 h2
    _ = _ := by ring


end Erdos821.P6Off
