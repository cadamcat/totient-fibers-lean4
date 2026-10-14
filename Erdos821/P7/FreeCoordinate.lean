import Erdos821.P7.LiteralMass
import Erdos821.P7.PlacementTask

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

abbrev RestLists (D : BandData) (x : ℝ) (jstar : ℕ) (s : D.Slot x) :=
  (t : {t : D.Slot x // t ≠ s}) → D.SlotValue x jstar t.val

def restoreList (D : BandData) {x : ℝ} {jstar : ℕ} (s : D.Slot x)
    (v : D.SlotValue x jstar s) (z : RestLists D x jstar s) : D.Lists x jstar :=
  (Equiv.piSplitAt s (D.SlotValue x jstar)).symm (v, z)

def restProduct (D : BandData) {x : ℝ} {jstar : ℕ} {s : D.Slot x}
    (z : RestLists D x jstar s) : ℕ := ∏ t, (z t).val

def restHarmonic (D : BandData) (x : ℝ) (jstar : ℕ) (s : D.Slot x) : ℝ :=
  ∑ z : RestLists D x jstar s, (restProduct D z : ℝ)⁻¹

def slotHarmonic (D : BandData) (x : ℝ) (jstar : ℕ) (s : D.Slot x) : ℝ :=
  ∑ v ∈ D.slotValues x jstar s, (v : ℝ)⁻¹

theorem restoreList_at (D : BandData) {x : ℝ} {jstar : ℕ} (s : D.Slot x)
    (v : D.SlotValue x jstar s) (z : RestLists D x jstar s) :
    restoreList D s v z s = v := by
  simp [restoreList, Equiv.piSplitAt]

theorem restoreList_off (D : BandData) {x : ℝ} {jstar : ℕ} (s : D.Slot x)
    (v : D.SlotValue x jstar s) (z : RestLists D x jstar s)
    (t : {t : D.Slot x // t ≠ s}) :
    restoreList D s v z t.val = z t := by
  simp [restoreList, Equiv.piSplitAt, t.property]

theorem slotValue_pos (D : BandData) {x : ℝ} {jstar : ℕ} {s : D.Slot x}
    (v : D.SlotValue x jstar s) : 0 < v.val := by
  have hm := v.property
  change v.val ∈ D.slotValues x jstar s at hm
  unfold BandData.slotValues at hm
  have hlo : ⌈Real.exp (D.c₁ * D.scale x s.1.val)⌉₊ ≤ v.val := by
    split_ifs at hm <;> exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  have hvR : (0 : ℝ) < v.val := (Real.exp_pos _).trans_le (Nat.ceil_le.mp hlo)
  exact_mod_cast hvR

theorem restProduct_pos (D : BandData) {x : ℝ} {jstar : ℕ} {s : D.Slot x}
    (z : RestLists D x jstar s) : 0 < restProduct D z :=
  Finset.prod_pos (fun t _ => slotValue_pos D (z t))

theorem outsideSlotProduct_restoreList (D : BandData) {x : ℝ} {jstar : ℕ}
    (s : D.Slot x) (v : D.SlotValue x jstar s) (z : RestLists D x jstar s) :
    outsideSlotProduct D (restoreList D s v z) s = restProduct D z := by
  unfold outsideSlotProduct restProduct
  rw [Finset.prod_subtype (p := fun t : D.Slot x => t ≠ s)
    (Finset.univ.erase s) (fun t => by simp)]
  apply Finset.prod_congr rfl
  intro t _
  rw [restoreList_off]

theorem listProduct_restoreList (D : BandData) {x : ℝ} {jstar : ℕ}
    (s : D.Slot x) (v : D.SlotValue x jstar s) (z : RestLists D x jstar s) :
    D.listProduct (restoreList D s v z) = v.val * restProduct D z := by
  rw [BandData.listProduct, Fintype.prod_eq_mul_prod_subtype_ne
    (fun t => (restoreList D s v z t).val) s]
  simp only [restoreList_at, restoreList_off, restProduct]

/-- Exact finite change of variables into a free coordinate and its complement. -/
theorem sum_lists_split (D : BandData) (x : ℝ) (jstar : ℕ) (s : D.Slot x)
    (f : D.Lists x jstar → ℝ) :
    (∑ z : D.Lists x jstar, f z) =
      ∑ z : RestLists D x jstar s, ∑ v : D.SlotValue x jstar s,
        f (restoreList D s v z) := by
  calc
    _ = ∑ p : D.SlotValue x jstar s × RestLists D x jstar s,
        f (restoreList D s p.1 p.2) :=
      ((Equiv.piSplitAt s (D.SlotValue x jstar)).symm.sum_comp f).symm
    _ = ∑ v : D.SlotValue x jstar s, ∑ z : RestLists D x jstar s,
        f (restoreList D s v z) := Fintype.sum_prod_type _
    _ = _ := Finset.sum_comm

theorem harmonic_test_split (D : BandData) (x : ℝ) (jstar : ℕ) (s : D.Slot x)
    (f : D.Lists x jstar → ℝ) :
    (∑ z : D.Lists x jstar, (D.listProduct z : ℝ)⁻¹ * f z) =
      ∑ z : RestLists D x jstar s, (restProduct D z : ℝ)⁻¹ *
        ∑ v : D.SlotValue x jstar s, (v.val : ℝ)⁻¹ * f (restoreList D s v z) := by
  rw [sum_lists_split D x jstar s]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [listProduct_restoreList]
  simp only [Nat.cast_mul, mul_inv_rev]
  ring

theorem slotHarmonic_eq_subtype_sum (D : BandData) (x : ℝ) (jstar : ℕ) (s : D.Slot x) :
    slotHarmonic D x jstar s = ∑ v : D.SlotValue x jstar s, (v.val : ℝ)⁻¹ := by
  exact (Finset.sum_coe_sort (D.slotValues x jstar s) (fun v : ℕ => (v : ℝ)⁻¹)).symm

theorem harmonicQ_free_split (D : BandData) (x : ℝ) (jstar : ℕ) (s : D.Slot x) :
    D.harmonicQ x jstar =
      ((D.r₀.factorial : ℝ) ^ (D.last x + 1))⁻¹ *
        restHarmonic D x jstar s * slotHarmonic D x jstar s := by
  rw [BandData.harmonicQ, ← Erdos821.S56Core.tuple_harmonic_factorization]
  have hs := harmonic_test_split D x jstar s (fun _ => 1)
  simp only [mul_one, ← Finset.sum_mul, ← slotHarmonic_eq_subtype_sum] at hs
  rw [hs]
  simp only [restHarmonic, mul_assoc]

def restPrefixEvent (C : CandidateData) (epsilon : ℝ) {x : ℝ} {jstar : ℕ}
    (s : C.bands.Slot x) (z : RestLists C.bands x jstar s) : Prop :=
  ∀ t : {t : C.bands.Slot x // t ≠ s}, t.val.1.val ≤ C.prefixLen →
    |Real.log (z t).val - (C.bands.c₁ + C.bands.c₂) / 2 * C.bands.scale x t.val.1.val| ≤
      epsilon * C.bands.scale x t.val.1.val

theorem prefixMidpointEvent_restoreList (C : CandidateData) (epsilon : ℝ)
    {x : ℝ} {jstar : ℕ} (s : C.bands.Slot x)
    (v : C.bands.SlotValue x jstar s) (z : RestLists C.bands x jstar s) :
    prefixMidpointEvent C epsilon s (restoreList C.bands s v z) ↔
      restPrefixEvent C epsilon s z := by
  constructor
  · intro h t ht
    simpa only [restoreList_off] using h t.val t.property ht
  · intro h t hts ht
    have hoff : restoreList C.bands s v z t = z ⟨t, hts⟩ :=
      restoreList_off C.bands s v z ⟨t, hts⟩
    simpa only [hoff] using h ⟨t, hts⟩ ht

/-- The prefix event ignores the free coordinate, so its harmonic sum factors
with the same full free-slot mass. -/
theorem prefix_harmonic_free_split (C : CandidateData) (epsilon : ℝ)
    (x : ℝ) (jstar : ℕ) (s : C.bands.Slot x) :
    (∑ z : C.bands.Lists x jstar, if prefixMidpointEvent C epsilon s z then
      (C.bands.listProduct z : ℝ)⁻¹ else 0) =
      (∑ z : RestLists C.bands x jstar s,
        if restPrefixEvent C epsilon s z then (restProduct C.bands z : ℝ)⁻¹ else 0) *
          slotHarmonic C.bands x jstar s := by
  have hs := harmonic_test_split C.bands x jstar s
    (fun z => if prefixMidpointEvent C epsilon s z then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, prefixMidpointEvent_restoreList,
    slotHarmonic_eq_subtype_sum] at hs ⊢
  rw [hs]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp [slotHarmonic_eq_subtype_sum, mul_assoc]

end Erdos821.P7Core

