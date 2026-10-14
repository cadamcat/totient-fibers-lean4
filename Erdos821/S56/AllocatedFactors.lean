import Erdos821.S56.AllocationRange
import Erdos821.S56.GroupParts
import Erdos821.S56.SlotProduct

noncomputable section
open scoped BigOperators

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem processed_factor_product (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (delta : ProcessedIndex D x jstar → Bool) :
    processedFactor D z delta * processedFactor D z (fun i => !delta i) = pureProduct D z := by
  rw [processedFactor, processedFactor, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases delta i <;> simp

theorem groupFree_of_dvd (G : PrimeGroups) (e h : ℕ) (hfree : GroupFree G h) (hdvd : e ∣ h) :
    GroupFree G e := fun p hp hpe => hfree p hp (hpe.trans hdvd)

def allocatedH (D : BandData) {x : ℝ} {jstar : ℕ} (z : D.Lists x jstar)
    (u : ℕ) (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : ProcessedIndex D x jstar → Bool) : ℕ :=
  groupPart (D.groups x) u * (z (exceptionalSlot D x jstar hj hr)).val *
    processedFactor D z (fun i => !delta i)

theorem allocated_factors (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (u : ℕ) (hu : 0 < u)
    (hz : D.listProduct z = groupFreePart (D.groups x) u)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀)
    (delta : ProcessedIndex D x jstar → Bool) :
    processedFactor D z delta * allocatedH D z u hj hr delta = u ∧
      GroupFree (D.groups x) (processedFactor D z delta) ∧
      groupFreePart (D.groups x) (allocatedH D z u hj hr delta) =
        (z (exceptionalSlot D x jstar hj hr)).val * processedFactor D z (fun i => !delta i) ∧
      markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u =
        markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell)
          (allocatedH D z u hj hr delta) := by
  let e := processedFactor D z delta
  let h := allocatedH D z u hj hr delta
  let p := (z (exceptionalSlot D x jstar hj hr)).val
  let r := processedFactor D z (fun i => !delta i)
  have he : 0 < e := processed_factor_pos D z delta
  have hp : 0 < p := slot_value_pos D z _
  have hrpos : 0 < r := processed_factor_pos D z _
  have hh : 0 < h := mul_pos (mul_pos (groupPart_pos (D.groups x) u) hp) hrpos
  have hq : e * r * p = groupFreePart (D.groups x) u :=
    (congrArg (fun v : ℕ => v * p) (processed_factor_product D z delta)).trans
      ((pure_product_exceptional D z hj hr).trans hz)
  have hprod : e * h = u := by
    calc
      _ = groupPart (D.groups x) u * (e * r * p) := by dsimp [h, allocatedH, e, r, p]; ring
      _ = _ := by rw [hq]; exact groupPart_mul_freePart (D.groups x) u hu
  have hdvd : e ∣ groupFreePart (D.groups x) u := ⟨r * p, by rw [← hq]; ring⟩
  have hfree : GroupFree (D.groups x) e :=
    groupFree_of_dvd _ _ _ (groupFreePart_groupFree (D.groups x) u) hdvd
  have hpart := groupFreePart_mul (D.groups x) e h he hh hfree
  rw [hprod] at hpart
  have hpart' : groupFreePart (D.groups x) h = p * r := by
    apply Nat.eq_of_mul_eq_mul_left he
    rw [← hpart, ← hq]
    ring
  have hweight := markWeight_mul (D.groups x) e h hfree D.geometry.q (fun _ => D.geometry.ell)
  rw [hprod] at hweight
  exact ⟨hprod, hfree, hpart', hweight⟩


end Erdos821.S56Core
