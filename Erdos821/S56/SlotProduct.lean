import Erdos821.S56.ProcessedSlots

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def exceptionalSlot (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀) : D.Slot x :=
  (⟨jstar, by omega⟩, ⟨0, by omega⟩)

def pureProduct (D : BandData) {x : ℝ} {jstar : ℕ} (z : D.Lists x jstar) : ℕ :=
  ∏ i : ProcessedIndex D x jstar, (z (processedSlot D x jstar i)).val

theorem pure_indices_erase (D : BandData) (x : ℝ) (jstar : ℕ)
    (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀) :
    pureIndices D x jstar = Finset.univ.erase
      ((decodeSlot D x).symm (exceptionalSlot D x jstar hj hr)) := by
  ext q
  simp only [pureIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, and_true]
  constructor
  · intro hn heq
    subst q
    simp [exceptionalSlot] at hn
  · intro hn heq
    apply hn
    apply (decodeSlot D x).injective
    simp only [Equiv.apply_symm_apply]
    apply Prod.ext <;> apply Fin.ext
    · exact heq.1
    · exact heq.2

theorem pure_product_index (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) :
    pureProduct D z = ∏ q ∈ pureIndices D x jstar, (z (decodeSlot D x q)).val := by
  calc
    _ = ∏ q : pureIndices D x jstar, (z (decodeSlot D x q.val)).val :=
      ((pureIndices D x jstar).orderIsoOfFin rfl).toEquiv.prod_comp _
    _ = _ := Finset.prod_coe_sort (pureIndices D x jstar)
      (fun q : AllSlotIndex D x => (z (decodeSlot D x q)).val)

theorem pure_product_exceptional (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (hj : jstar ≤ D.last x) (hr : 1 ≤ D.r₀) :
    pureProduct D z * (z (exceptionalSlot D x jstar hj hr)).val = D.listProduct z := by
  rw [pure_product_index, pure_indices_erase D x jstar hj hr]
  have hmem : (decodeSlot D x).symm (exceptionalSlot D x jstar hj hr) ∈ Finset.univ :=
    Finset.mem_univ _
  have hprod := Finset.prod_erase_mul Finset.univ (fun q => (z (decodeSlot D x q)).val) hmem
  have hvalue : (z (decodeSlot D x ((decodeSlot D x).symm
      (exceptionalSlot D x jstar hj hr)))).val = (z (exceptionalSlot D x jstar hj hr)).val :=
    congrArg (fun s : D.Slot x => (z s).val) ((decodeSlot D x).apply_symm_apply _)
  rw [hvalue] at hprod
  rw [hprod]
  exact (decodeSlot D x).prod_comp (fun s : D.Slot x => (z s).val)

theorem log_pure_product (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) :
    Real.log (pureProduct D z) = ∑ i, processedLog D z i := by
  simp only [pureProduct, Nat.cast_prod]
  apply Real.log_prod
  intro i _
  have hp : (0 : ℝ) < (z (processedSlot D x jstar i)).val := by
    exact_mod_cast slot_value_pos D z (processedSlot D x jstar i)
  exact hp.ne'

theorem pure_product_pos (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) : 0 < pureProduct D z :=
  Finset.prod_pos (fun i _ => slot_value_pos D z (processedSlot D x jstar i))


end Erdos821.S56Core
