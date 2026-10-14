import Erdos821.S56.GroupParts
import Erdos821.S56.SlotProduct

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem eventually_exceptional_present (D : BandData) (hD : D.Valid) (jstar : ℕ) :
    ∀ᶠ x : ℝ in atTop, jstar ≤ D.last x := by
  obtain ⟨_, _, _, _, _, _, _, hl, _⟩ := hD
  exact hl.eventually (eventually_ge_atTop jstar)

/-- The two preallocated factors use at most b/2 of the logarithmic size:
the group part is good, and the exceptional rough slot has eta<b/4. -/
theorem good_tuple_available (D : BandData) (hD : D.Valid) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (hj : jstar ≤ D.last x) (u : ℕ)
    (hz : D.listProduct z = groupFreePart (D.groups x) u)
    (hx : 1 < x) (hu : x ≤ (u : ℝ)) (b U K0 : ℝ) (hb : 0 < b)
    (hU : 0 < U) (hUhi : U ≤ x ^ (1 - b)) (hK0 : 0 ≤ K0) (hT : 0 ≤ T x)
    (heta : D.c₂ * D.s' / D.ratio ^ jstar < b / 4)
    (hgood : (groupPart (D.groups x) u : ℝ) ≤ x ^ (b / 4)) :
    Real.log (U * L x ^ (-K0)) ≤ ∑ i, processedLog D z i := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hupos : 0 < u := by exact_mod_cast (hxpos.trans_le hu)
  have hL : 0 < L x := Real.log_pos hx
  let p := (z (exceptionalSlot D x jstar hj hD.1)).val
  have hppos : (0 : ℝ) < p := by exact_mod_cast slot_value_pos D z _
  have hfree := groupPart_mul_freePart (D.groups x) u hupos
  have hprod := pure_product_exceptional D z hj hD.1
  have htotal : (u : ℝ) = (groupPart (D.groups x) u : ℝ) * (pureProduct D z : ℝ) * p := by
    have heq : u = groupPart (D.groups x) u * pureProduct D z * p := by
      calc
        u = groupPart (D.groups x) u * groupFreePart (D.groups x) u := hfree.symm
        _ = groupPart (D.groups x) u * D.listProduct z := by rw [hz]
        _ = groupPart (D.groups x) u * (pureProduct D z * p) := by rw [hprod]
        _ = _ := (Nat.mul_assoc _ _ _).symm
    exact_mod_cast heq
  have hgpos : (0 : ℝ) < groupPart (D.groups x) u := by
    exact_mod_cast groupPart_pos (D.groups x) u
  have hqpos : (0 : ℝ) < pureProduct D z := by exact_mod_cast pure_product_pos D z
  have hlogu : Real.log (u : ℝ) = Real.log (groupPart (D.groups x) u) +
      Real.log (pureProduct D z) + Real.log p := by
    rw [htotal, Real.log_mul (mul_ne_zero hgpos.ne' hqpos.ne') hppos.ne',
      Real.log_mul hgpos.ne' hqpos.ne']
  have hlogg := Real.log_le_log hgpos hgood
  rw [Real.log_rpow hxpos] at hlogg
  have hlogp : Real.log p ≤ (b / 4) * L x := by
    have hbound := (slot_log_bounds D z (exceptionalSlot D x jstar hj hD.1)).2
    have heq : D.c₂ * D.scale x jstar = (D.c₂ * D.s' / D.ratio ^ jstar) * L x := by
      unfold BandData.scale
      ring
    change Real.log p ≤ D.c₂ * D.scale x jstar at hbound
    rw [heq] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right heta.le hL.le)
  have hloglo : L x ≤ Real.log (u : ℝ) := Real.log_le_log hxpos hu
  have hlogU := Real.log_le_log hU hUhi
  rw [Real.log_rpow hxpos] at hlogU
  have hlogE : Real.log (U * L x ^ (-K0)) = Real.log U - K0 * T x := by
    rw [Real.log_mul hU.ne' (Real.rpow_pos_of_pos hL _).ne', Real.log_rpow hL]
    unfold T
    ring
  rw [hlogE, ← log_pure_product]
  have hK : 0 ≤ K0 * T x := mul_nonneg hK0 hT
  change Real.log x ≤ _ at hloglo
  unfold L at hL hlogp
  nlinarith [mul_pos hb hL]


end Erdos821.S56Core
