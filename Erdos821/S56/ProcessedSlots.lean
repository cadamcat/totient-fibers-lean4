import Erdos821.S56.SlotBounds

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

abbrev AllSlotIndex (D : BandData) (x : ℝ) := Fin ((D.last x + 1) * D.r₀)

def decodeSlot (D : BandData) (x : ℝ) : AllSlotIndex D x ≃ D.Slot x :=
  finProdFinEquiv.symm

def pureIndices (D : BandData) (x : ℝ) (jstar : ℕ) : Finset (AllSlotIndex D x) :=
  Finset.univ.filter fun i => ¬((decodeSlot D x i).1.val = jstar ∧
    (decodeSlot D x i).2.val = 0)

abbrev ProcessedIndex (D : BandData) (x : ℝ) (jstar : ℕ) :=
  Fin (pureIndices D x jstar).card

def processedSlot (D : BandData) (x : ℝ) (jstar : ℕ)
    (i : ProcessedIndex D x jstar) : D.Slot x :=
  decodeSlot D x (((pureIndices D x jstar).orderIsoOfFin rfl i).val)

def processedLog (D : BandData) {x : ℝ} {jstar : ℕ} (z : D.Lists x jstar)
    (i : ProcessedIndex D x jstar) : ℝ := Real.log (z (processedSlot D x jstar i)).val

def processedScale (D : BandData) (x : ℝ) (jstar : ℕ)
    (i : ProcessedIndex D x jstar) : ℝ := D.scale x (processedSlot D x jstar i).1.val

theorem processed_not_exceptional (D : BandData) (x : ℝ) (jstar : ℕ)
    (i : ProcessedIndex D x jstar) :
    ¬((processedSlot D x jstar i).1.val = jstar ∧
      (processedSlot D x jstar i).2.val = 0) :=
  (Finset.mem_filter.mp ((pureIndices D x jstar).orderEmbOfFin_mem rfl i)).2

theorem processedSlot_injective (D : BandData) (x : ℝ) (jstar : ℕ) :
    Function.Injective (processedSlot D x jstar) :=
  (decodeSlot D x).injective.comp ((pureIndices D x jstar).orderEmbOfFin rfl).injective

theorem processed_log_bounds (D : BandData) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (i : ProcessedIndex D x jstar) :
    D.c₁ * processedScale D x jstar i ≤ processedLog D z i ∧
      processedLog D z i ≤ D.c₂ * processedScale D x jstar i :=
  slot_log_bounds D z (processedSlot D x jstar i)

theorem processed_log_pos (D : BandData) (hD : D.Valid) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (hL : 0 < L x) (i : ProcessedIndex D x jstar) :
    0 < processedLog D z i ∧ 0 < processedScale D x jstar i := by
  have hs := scale_pos D hD x hL (processedSlot D x jstar i).1.val
  exact ⟨(mul_pos hD.2.1 hs).trans_le (processed_log_bounds D z i).1, hs⟩

theorem processed_card_bound (D : BandData) (hD : D.Valid) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ jstar : ℕ, ((pureIndices D x jstar).card : ℝ) ≤ C * T x := by
  obtain ⟨C, hC, hx⟩ := band_count_bound D hD
  refine ⟨C * D.r₀, mul_pos hC (by exact_mod_cast (zero_lt_one.trans_le hD.1)), ?_⟩
  filter_upwards [hx] with x hx
  intro jstar
  have hcard : (pureIndices D x jstar).card ≤ (D.last x + 1) * D.r₀ := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  calc
    _ ≤ (((D.last x + 1) * D.r₀ : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ C * D.r₀ * T x := by
      push_cast at hx ⊢
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg D.r₀ : (0 : ℝ) ≤ D.r₀)


end Erdos821.S56Core
