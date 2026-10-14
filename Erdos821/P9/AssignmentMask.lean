import Erdos821.P9.GlobalAssignmentMajorant

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section
attribute [local instance] Classical.propDecidable

open Erdos821.Blueprint
open Erdos821.Blueprint.Analytic

abbrev GlobalMarkMasks (G : PrimeGroups) :=
  Σ marks : GlobalMarkChoices G,
    PermissionIndex (groupPrimeSet G \ globalMarkImage G marks) → Bool

abbrev GlobalAssignmentMasks (C : CandidateData) (x : ℝ) (jstar : ℕ) :=
  MicroAssignments C x jstar × GlobalMarkMasks (C.bands.groups x)

def globalAssignmentMaskGood
    (C : CandidateData) (x : ℝ) (jstar u : ℕ)
    (a : GlobalAssignmentMasks C x jstar) : Prop :=
  (microAssignmentProduct C x jstar a.1 ∣
      groupFreePart (C.bands.groups x) u ∧
    microCapturesSmallFreePrimes C x jstar u a.1) ∧
  globalMarksDivide (C.bands.groups x) a.2.1 u

def globalAssignmentMaskTerm
    (C : CandidateData) (x : ℝ) (jstar u : ℕ)
    (a : GlobalAssignmentMasks C x jstar) : ℝ :=
  if globalAssignmentMaskGood C x jstar u a then
    (listNormalizer C.bands x *
      (Fintype.card (MacroSlotIndex C)).factorial) *
      markBaseCoefficient (C.bands.groups x) u *
      permissionEventTerm
        (groupPrimeSet (C.bands.groups x) \
          globalMarkImage (C.bands.groups x) a.2.1)
        C.bands.geometry.q u a.2.2
  else 0

theorem globalAssignmentMaskTerm_eq_probability_indicator
    (C : CandidateData) (x : ℝ) (jstar u : ℕ)
    (a : GlobalAssignmentMasks C x jstar) :
    globalAssignmentMaskTerm C x jstar u a =
      if globalAssignmentMaskGood C x jstar u a ∧
          permissionMaskGood
            (groupPrimeSet (C.bands.groups x) \
              globalMarkImage (C.bands.groups x) a.2.1)
            u a.2.2 then
        (listNormalizer C.bands x *
          (Fintype.card (MacroSlotIndex C)).factorial) *
          markBaseCoefficient (C.bands.groups x) u *
          permissionMaskProbability
            (groupPrimeSet (C.bands.groups x) \
              globalMarkImage (C.bands.groups x) a.2.1)
            C.bands.geometry.q a.2.2
      else 0 := by
  unfold globalAssignmentMaskTerm
  by_cases hgood : globalAssignmentMaskGood C x jstar u a
  · simp [hgood, permissionEventTerm_eq_probability_indicator]
  · simp [hgood]

theorem bandWeight_le_global_assignment_mask_sum
    (C : CandidateData) (δ x : ℝ) (jstar u : ℕ)
    (hC : C.Geometry δ) (hx : 1 < x)
    (hbound : C.micro ≤ C.bands.last x + 1) (hj : C.micro ≤ jstar)
    (hu : u ≠ 0) (hell : C.bands.geometry.ell = 1)
    (hq : 0 < C.bands.geometry.q)
    (hmass : ∀ g, 0 < mass (C.bands.groups x) g) :
    C.bands.weight x jstar u ≤
      ∑ a : GlobalAssignmentMasks C x jstar,
        globalAssignmentMaskTerm C x jstar u a := by
  classical
  let G := C.bands.groups x
  let K := listNormalizer C.bands x * (Fintype.card (MacroSlotIndex C)).factorial
  let microGood := fun m : MicroAssignments C x jstar =>
    microAssignmentProduct C x jstar m ∣ groupFreePart G u ∧
      microCapturesSmallFreePrimes C x jstar u m
  let fGlobal := fun (m : MicroAssignments C x jstar)
      (marks : GlobalMarkChoices G)
      (allow : PermissionIndex (groupPrimeSet G \ globalMarkImage G marks) → Bool) =>
    K * markBaseCoefficient G u *
      permissionEventTerm (groupPrimeSet G \ globalMarkImage G marks)
        C.bands.geometry.q u allow
  let goodMicro := Finset.univ.filter microGood
  have hbase := bandWeight_le_global_assignment_mask C δ x jstar u
    hC hx hbound hj hu hell hq hmass
  have hmarkConvert (m : MicroAssignments C x jstar) :
      (∑ marks ∈ globalMarkDivisors G u,
        K * markBaseCoefficient G u *
          permissionEventSum (groupPrimeSet G \ globalMarkImage G marks)
            C.bands.geometry.q u) =
      ∑ z : GlobalMarkMasks G,
        if globalMarksDivide G z.1 u then fGlobal m z.1 z.2 else 0 := by
    calc
      _ = ∑ marks : GlobalMarkChoices G,
            if globalMarksDivide G marks u then
              ∑ allow : PermissionIndex (groupPrimeSet G \ globalMarkImage G marks) → Bool,
                K * markBaseCoefficient G u *
                  permissionEventTerm (groupPrimeSet G \ globalMarkImage G marks)
                    C.bands.geometry.q u allow
            else 0 := by
        simp [globalMarkDivisors, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro marks hm
        by_cases hdiv : globalMarksDivide G marks u
        · simp only [hdiv, ↓reduceIte, permissionEventSum]
          rw [Finset.mul_sum]
        · simp [hdiv]
      _ = ∑ z : GlobalMarkMasks G,
            if globalMarksDivide G z.1 u then fGlobal m z.1 z.2 else 0 := by
        calc
          _ = ∑ marks : GlobalMarkChoices G,
                ∑ allow : PermissionIndex (groupPrimeSet G \ globalMarkImage G marks) → Bool,
                  if globalMarksDivide G marks u then
                    fGlobal m marks allow else 0 := by
            apply Finset.sum_congr rfl
            intro marks hm
            by_cases hdiv : globalMarksDivide G marks u
            · simp only [hdiv, ↓reduceIte]
              change
                (∑ allow : PermissionIndex (groupPrimeSet G \ globalMarkImage G marks) → Bool,
                  K * markBaseCoefficient G u *
                    permissionEventTerm (groupPrimeSet G \ globalMarkImage G marks)
                      C.bands.geometry.q u allow) =
                ∑ allow : PermissionIndex (groupPrimeSet G \ globalMarkImage G marks) → Bool,
                  K * markBaseCoefficient G u *
                    permissionEventTerm (groupPrimeSet G \ globalMarkImage G marks)
                      C.bands.geometry.q u allow
              rfl
            · simp [hdiv]
          _ = _ := by rw [Fintype.sum_sigma]
  have hconvert :
      (∑ m ∈ goodMicro,
        ∑ marks ∈ globalMarkDivisors G u,
          K * markBaseCoefficient G u *
            permissionEventSum (groupPrimeSet G \ globalMarkImage G marks)
              C.bands.geometry.q u) =
      ∑ m : MicroAssignments C x jstar,
        ∑ z : GlobalMarkMasks G,
          if microGood m ∧ globalMarksDivide G z.1 u then
            fGlobal m z.1 z.2 else 0 := by
    calc
      _ = ∑ m ∈ goodMicro,
            ∑ z : GlobalMarkMasks G,
              if globalMarksDivide G z.1 u then fGlobal m z.1 z.2 else 0 := by
        apply Finset.sum_congr rfl
        intro m hm
        exact hmarkConvert m
      _ = ∑ m : MicroAssignments C x jstar,
            if microGood m then
              ∑ z : GlobalMarkMasks G,
                if globalMarksDivide G z.1 u then fGlobal m z.1 z.2 else 0
            else 0 := by
        simp [goodMicro, Finset.sum_filter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        by_cases hmg : microGood m
        · simp [hmg]
        · simp [hmg]
  calc
    C.bands.weight x jstar u ≤
        ∑ m ∈ goodMicro,
          ∑ marks ∈ globalMarkDivisors G u,
            K * markBaseCoefficient G u *
              permissionEventSum (groupPrimeSet G \ globalMarkImage G marks)
                C.bands.geometry.q u := by
      simpa [G, K, goodMicro, microGood] using hbase
    _ = ∑ m : MicroAssignments C x jstar,
          ∑ z : GlobalMarkMasks G,
            if microGood m ∧ globalMarksDivide G z.1 u then
              fGlobal m z.1 z.2 else 0 := hconvert
    _ = ∑ a : GlobalAssignmentMasks C x jstar,
          globalAssignmentMaskTerm C x jstar u a := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro z hz
      simp [globalAssignmentMaskTerm, globalAssignmentMaskGood,
        microGood, fGlobal, G, K, and_assoc]


end

end Erdos821.P9Core
