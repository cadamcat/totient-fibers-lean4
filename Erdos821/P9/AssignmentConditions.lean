import Erdos821.P9.AssignmentMask

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section
attribute [local instance] Classical.propDecidable

open Erdos821.Blueprint
open Erdos821.Blueprint.Analytic

def globalMaskAllowedPrimes (G : PrimeGroups) (marks : GlobalMarkChoices G)
    (allow : PermissionIndex (groupPrimeSet G \ globalMarkImage G marks) → Bool) :
    Finset ℕ :=
  globalMarkImage G marks ∪
    (groupPrimeSet G \ globalMarkImage G marks).filter
      (fun p => if hp : p ∈ groupPrimeSet G \ globalMarkImage G marks then
        allow ⟨p, hp⟩ = true else False)

theorem globalAssignmentMask_divisor_dvd_index
    (G : PrimeGroups) (u : ℕ) (micro : ℕ) (marks : GlobalMarkChoices G)
    (hmicro : micro ∣ groupFreePart G u)
    (hmarks : globalMarksDivide G marks u) (hu : u ≠ 0) :
    micro * globalMarkProduct G marks ∣ u := by
  let marksSub : {m : GlobalMarkChoices G // globalMarksDivide G m u} := ⟨marks, hmarks⟩
  let dependentMarks := (markChoicesEquivGlobal G u).invFun marksSub
  have hmark := markProduct_dvd_groupPart G u hu dependentMarks
  have hmarkEq := markProduct_eq_globalMarkProduct G u marksSub
  rw [hmarkEq] at hmark
  have hprod := Nat.mul_dvd_mul hmicro hmark
  rw [groupFreePart_mul_groupPart G u hu] at hprod
  exact hprod

theorem globalAssignmentMask_no_banned_divisor
    (C : CandidateData) (x : ℝ) (jstar u : ℕ)
    (micro : MicroAssignments C x jstar)
    (marks : GlobalMarkChoices (C.bands.groups x))
    (allow : PermissionIndex
      (groupPrimeSet (C.bands.groups x) \ globalMarkImage (C.bands.groups x) marks) → Bool)
    (hMicroCapture : microCapturesSmallFreePrimes C x jstar u micro)
    (hMaskGood : permissionMaskGood
      (groupPrimeSet (C.bands.groups x) \ globalMarkImage (C.bands.groups x) marks)
      u allow)
    (p : ℕ) (hp : p.Prime) (hpSmall : (p : ℝ) ≤ x ^ C.theta)
    (hpDiv : p ∣ u)
    (hDnot : ¬ p ∣ microAssignmentProduct C x jstar micro *
      globalMarkProduct (C.bands.groups x) marks)
    (hBanned : p ∉ groupPrimeSet (C.bands.groups x) ∨
      p ∉ globalMaskAllowedPrimes (C.bands.groups x) marks allow) :
    False := by
  classical
  let G := C.bands.groups x
  by_cases hpGroup : p ∈ groupPrimeSet G
  · have hpNotA : p ∉ globalMaskAllowedPrimes G marks allow := by
      rcases hBanned with hnotGroup | hnotAllowed
      · exact (hnotGroup hpGroup).elim
      · exact hnotAllowed
    have hpNotMark : p ∉ globalMarkImage G marks := by
      intro hpM
      exact hpNotA (Finset.mem_union_left _ hpM)
    let U := groupPrimeSet G \ globalMarkImage G marks
    have hpU : p ∈ U := Finset.mem_sdiff.mpr ⟨hpGroup, hpNotMark⟩
    have hpNotAllowed : p ∉ U.filter (fun q =>
        if hq : q ∈ U then allow ⟨q, hq⟩ = true else False) := by
      intro hpF
      exact hpNotA (Finset.mem_union_right _ hpF)
    have hallowNot : allow ⟨p, hpU⟩ ≠ true := by
      intro htrue
      apply hpNotAllowed
      exact Finset.mem_filter.mpr ⟨hpU, by simp [hpU, htrue]⟩
    have hallowFalse : allow ⟨p, hpU⟩ = false := by
      cases hv : allow ⟨p, hpU⟩
      · rfl
      · exact (hallowNot hv).elim
    have hnotTrue : allow ⟨p, hpU⟩ ≠ true := by
      intro htrue
      rw [hallowFalse] at htrue
      contradiction
    exact (hMaskGood ⟨p, hpU⟩).resolve_left hnotTrue hpDiv
  · have hmicroDiv : p ∣ microAssignmentProduct C x jstar micro :=
      hMicroCapture p hp hpSmall hpGroup hpDiv
    have hdivMod : p ∣ microAssignmentProduct C x jstar micro *
        globalMarkProduct G marks := dvd_mul_of_dvd_left hmicroDiv _
    exact hDnot hdivMod


end

end Erdos821.P9Core
