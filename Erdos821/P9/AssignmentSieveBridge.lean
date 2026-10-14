import Erdos821.P9.AssignmentConditions
import Erdos821.P9.PairSifted

open scoped BigOperators

namespace Erdos821.P9Core

noncomputable section
attribute [local instance] Classical.propDecidable

open Erdos821.Blueprint
open Erdos821.Blueprint.Analytic

theorem globalAssignmentMaskPair_sifted
    (C : CandidateData) (x : ℝ) (jstar : ℕ)
    (micro : MicroAssignments C x jstar)
    (marks : GlobalMarkChoices (C.bands.groups x))
    (allow : PermissionIndex
      (groupPrimeSet (C.bands.groups x) \ globalMarkImage (C.bands.groups x) marks) → Bool)
    (u m n a b c e : ℕ) (W : ℝ) (Q : Finset ℕ)
    (hu0 : u ≠ 0)
    (hDpos : 0 < microAssignmentProduct C x jstar micro *
      globalMarkProduct (C.bands.groups x) marks)
    (hgood : globalAssignmentMaskGood C x jstar u (micro, ⟨marks, allow⟩))
    (hMaskGood : permissionMaskGood
      (groupPrimeSet (C.bands.groups x) \ globalMarkImage (C.bands.groups x) marks)
      u allow)
    (hmn : m * n = 2 * u + 1)
    (hprod1 : 1 < m * n)
    (hroughM : Analytic.rough W m) (hroughN : Analytic.rough W n)
    (hm : m ∈ Finset.Ico a b) (hn : n ∈ Finset.Ico c e)
    (hQprime : ∀ p ∈ Q, p.Prime) (hQlarge : ∀ p ∈ Q, 3 ≤ p)
    (hQsmall : ∀ p ∈ Q, (p : ℝ) ≤ x ^ C.theta)
    (hQnotD : ∀ p ∈ Q,
      ¬ p ∣ microAssignmentProduct C x jstar micro *
        globalMarkProduct (C.bands.groups x) marks) :
    let G := C.bands.groups x
    let P := groupPrimeSet G
    let A := globalMaskAllowedPrimes G marks allow
    let D := microAssignmentProduct C x jstar micro * globalMarkProduct G marks
    let S := pairSieveData a b c e D W P A Q hDpos hQprime
    (m, n) ∈ S.objects ∧ ∀ p ∈ Q, ¬ S.bad p (m, n) := by
  classical
  let G := C.bands.groups x
  let P := groupPrimeSet G
  let A := globalMaskAllowedPrimes G marks allow
  let D := microAssignmentProduct C x jstar micro * globalMarkProduct G marks
  let S := pairSieveData a b c e D W P A Q hDpos hQprime
  have huNe : u ≠ 0 := by
    intro huZero
    subst u
    rw [hmn] at hprod1
    norm_num at hprod1
  have hDdiv : D ∣ u := by
    dsimp [D]
    exact globalAssignmentMask_divisor_dvd_index G u
      (microAssignmentProduct C x jstar micro) marks hgood.1.1 hgood.2 huNe
  have hnoBanned : ∀ p ∈ Q, p ∉ P ∨ p ∉ A → ¬ p ∣ u := by
    intro p hpQ hban
    intro hdiv
    have hnotD := hQnotD p hpQ
    exact globalAssignmentMask_no_banned_divisor C x jstar u micro marks allow
      hgood.1.2 hMaskGood p (hQprime p hpQ) (hQsmall p hpQ) hdiv
      hnotD hban
  have hData := pairSieveData_object_and_good_of_conditions
    a b c e D W P A Q hDpos hQprime hQlarge m n u hm hn hDdiv hmn
    hroughM hroughN hnoBanned
  simpa [S, G, P, A, D] using hData


end

end Erdos821.P9Core
