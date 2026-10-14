import Erdos821.P9.GlobalMarks
import Erdos821.P9.PermissionMask

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section
attribute [local instance] Classical.propDecidable

open Erdos821.Blueprint
open Erdos821.Blueprint.Analytic

/-- The existing pointwise assignment majorant with group marks indexed
independently of the target integer. -/
theorem bandWeight_le_global_assignment_mask
    (C : CandidateData) (δ x : ℝ) (jstar u : ℕ)
    (hC : C.Geometry δ) (hx : 1 < x)
    (hbound : C.micro ≤ C.bands.last x + 1) (hj : C.micro ≤ jstar)
    (hu : u ≠ 0) (hell : C.bands.geometry.ell = 1)
    (hq : 0 < C.bands.geometry.q)
    (hmass : ∀ g, 0 < mass (C.bands.groups x) g) :
    C.bands.weight x jstar u ≤
      ∑ m ∈ (Finset.univ.filter fun m : MicroAssignments C x jstar =>
          microAssignmentProduct C x jstar m ∣
            groupFreePart (C.bands.groups x) u ∧
          microCapturesSmallFreePrimes C x jstar u m),
        ∑ marks ∈ globalMarkDivisors (C.bands.groups x) u,
          (listNormalizer C.bands x *
            (Fintype.card (MacroSlotIndex C)).factorial) *
            markBaseCoefficient (C.bands.groups x) u *
            permissionEventSum
              (groupPrimeSet (C.bands.groups x) \ globalMarkImage (C.bands.groups x) marks)
              C.bands.geometry.q u := by
  classical
  let G := C.bands.groups x
  let K := listNormalizer C.bands x * (Fintype.card (MacroSlotIndex C)).factorial
  let goodAssignments := Finset.univ.filter fun m : MicroAssignments C x jstar =>
    microAssignmentProduct C x jstar m ∣ groupFreePart G u ∧
      microCapturesSmallFreePrimes C x jstar u m
  let f : MarkChoices G u → ℝ := fun marks =>
    K * markBaseCoefficient G u *
      permissionEventSum (groupPrimeSet G \ markImage G u marks)
        C.bands.geometry.q u
  let fGlobal : GlobalMarkChoices G → ℝ := fun marks =>
    K * markBaseCoefficient G u *
      permissionEventSum (groupPrimeSet G \ globalMarkImage G marks)
        C.bands.geometry.q u
  have hinner :
      (∑ marks : MarkChoices G u, f marks) =
        ∑ marks ∈ globalMarkDivisors G u, fGlobal marks := by
    calc
      (∑ marks : MarkChoices G u, f marks) =
          ∑ marks : {m : GlobalMarkChoices G // globalMarksDivide G m u},
            f ((markChoicesEquivGlobal G u).invFun marks) :=
        sum_markChoices_eq_sum_globalMarkDivisors G u f
      _ = ∑ marks : {m : GlobalMarkChoices G // globalMarksDivide G m u},
            fGlobal marks.val := by
        apply Finset.sum_congr rfl
        intro marks hm
        simp only [f, fGlobal]
        rw [markImage_eq_globalMarkImage]
      _ = ∑ marks ∈ globalMarkDivisors G u, fGlobal marks :=
        sum_globalMarkDivisors_eq_filter G u fGlobal
  have hbase := bandWeight_le_captured_assignment_mask C δ x jstar u
    hC hx hbound hj hu hell hq hmass
  calc
    C.bands.weight x jstar u ≤
        ∑ m ∈ goodAssignments, ∑ marks : MarkChoices G u, f marks := by
      simpa [G, K, goodAssignments, f] using hbase
    _ = ∑ m ∈ goodAssignments,
          ∑ marks ∈ globalMarkDivisors G u, fGlobal marks := by
      apply Finset.sum_congr rfl
      intro m hm
      exact hinner
    _ = _ := by
      simpa [G, K, goodAssignments, fGlobal]


end

end Erdos821.P9Core
