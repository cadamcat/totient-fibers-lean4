import Erdos821.S56.ProcessedSlots

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def nextBandSlot (D : BandData) (x : ℝ) (jstar : ℕ)
    (i : ProcessedIndex D x jstar)
    (hnext : (processedSlot D x jstar i).1.val < D.last x)
    (k : Fin (D.r₀ - 1)) : D.Slot x :=
  (⟨(processedSlot D x jstar i).1.val + 1, by omega⟩, ⟨k.val + 1, by omega⟩)

def nextBandPosition (D : BandData) (x : ℝ) (jstar : ℕ)
    (i : ProcessedIndex D x jstar)
    (hnext : (processedSlot D x jstar i).1.val < D.last x)
    (k : Fin (D.r₀ - 1)) : ProcessedIndex D x jstar := by
  let q := (decodeSlot D x).symm (nextBandSlot D x jstar i hnext k)
  have hq : q ∈ pureIndices D x jstar := by
    simp only [pureIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    simp [q, nextBandSlot]
  exact ((pureIndices D x jstar).orderIsoOfFin rfl).symm ⟨q, hq⟩

theorem processed_nextBandPosition (D : BandData) (x : ℝ) (jstar : ℕ)
    (i : ProcessedIndex D x jstar)
    (hnext : (processedSlot D x jstar i).1.val < D.last x)
    (k : Fin (D.r₀ - 1)) :
    processedSlot D x jstar (nextBandPosition D x jstar i hnext k) =
      nextBandSlot D x jstar i hnext k := by
  simp [processedSlot, nextBandPosition]

theorem nextBandPosition_injective (D : BandData) (x : ℝ) (jstar : ℕ)
    (i : ProcessedIndex D x jstar)
    (hnext : (processedSlot D x jstar i).1.val < D.last x) :
    Function.Injective (nextBandPosition D x jstar i hnext) := by
  intro k k' h
  have hs := congrArg (processedSlot D x jstar) h
  rw [processed_nextBandPosition, processed_nextBandPosition] at hs
  have hv := congrArg (fun s : D.Slot x => s.2.val) hs
  apply Fin.ext
  dsimp [nextBandSlot] at hv
  omega

theorem processed_encoding (D : BandData) (x : ℝ) (jstar : ℕ)
    (i : ProcessedIndex D x jstar) :
    (((pureIndices D x jstar).orderIsoOfFin rfl i).val).val =
      (processedSlot D x jstar i).2.val + D.r₀ * (processedSlot D x jstar i).1.val := by
  have h := congrArg Fin.val ((decodeSlot D x).symm_apply_apply
    (((pureIndices D x jstar).orderIsoOfFin rfl i).val))
  exact h.symm

theorem nextBandPosition_gt (D : BandData) (x : ℝ) (jstar : ℕ)
    (i : ProcessedIndex D x jstar)
    (hnext : (processedSlot D x jstar i).1.val < D.last x)
    (k : Fin (D.r₀ - 1)) : i < nextBandPosition D x jstar i hnext k := by
  apply ((pureIndices D x jstar).orderIsoOfFin rfl).lt_iff_lt.mp
  change (((pureIndices D x jstar).orderIsoOfFin rfl i).val).val <
    (((pureIndices D x jstar).orderIsoOfFin rfl
      (nextBandPosition D x jstar i hnext k)).val).val
  rw [processed_encoding, processed_encoding, processed_nextBandPosition]
  have hi := (processedSlot D x jstar i).2.isLt
  dsimp [nextBandSlot]
  simp only [Nat.mul_add, Nat.mul_one]
  omega

theorem next_band_log_sum (D : BandData) (hD : D.Valid) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (hL : 0 < L x) (i : ProcessedIndex D x jstar)
    (hnext : (processedSlot D x jstar i).1.val < D.last x) :
    ((D.r₀ : ℝ) - 1) * D.c₁ * D.scale x ((processedSlot D x jstar i).1.val + 1) ≤
      ∑ t ∈ Finset.univ.filter (fun t : ProcessedIndex D x jstar => i.val < t.val),
        processedLog D z t := by
  let f := nextBandPosition D x jstar i hnext
  let s := Finset.univ.image f
  have hsub : s ⊆ Finset.univ.filter (fun t : ProcessedIndex D x jstar => i.val < t.val) := by
    intro t ht
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, nextBandPosition_gt D x jstar i hnext k⟩
  have hr : ((D.r₀ - 1 : ℕ) : ℝ) = (D.r₀ : ℝ) - 1 :=
    by simpa only [Nat.cast_one] using (Nat.cast_sub hD.1 : ((D.r₀ - 1 : ℕ) : ℝ) = _)
  calc
    _ = ∑ _k : Fin (D.r₀ - 1),
        D.c₁ * D.scale x ((processedSlot D x jstar i).1.val + 1) := by simp [hr]; ring
    _ ≤ ∑ k : Fin (D.r₀ - 1), processedLog D z (f k) := by
      apply Finset.sum_le_sum
      intro k _
      have h := (processed_log_bounds D z (f k)).1
      simpa [f, processedScale, processed_nextBandPosition, nextBandSlot] using h
    _ = ∑ t ∈ s, processedLog D z t := by
      rw [Finset.sum_image]
      exact fun a _ b _ h => nextBandPosition_injective D x jstar i hnext h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun t _ _ => (processed_log_pos D hD z hL t).1.le)


theorem scale_succ (D : BandData) (x : ℝ) (j : ℕ) :
    D.scale x (j + 1) = D.scale x j / D.ratio := by
  simp only [BandData.scale, pow_succ, div_div]

/-- After a possible skip, the next band has r₀−1 nonexceptional slots.
In the last band the terminal allowance supplies the required room. -/
theorem processed_room (D : BandData) (hD : D.Valid) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (hL : 0 < L x) (i : ProcessedIndex D x jstar) :
    processedLog D z i + processedScale D x jstar i ≤
      (∑ t ∈ Finset.univ.filter (fun t : ProcessedIndex D x jstar => i.val < t.val),
        processedLog D z t) + (D.c₂ + 1) * D.scale x (D.last x) := by
  have htpos : 0 ≤ (D.c₂ + 1) * D.scale x (D.last x) := by
    have hc2 : 0 < D.c₂ := hD.2.1.trans hD.2.2.1
    exact mul_nonneg (by linarith) (scale_pos D hD x hL _).le
  have hupper := (processed_log_bounds D z i).2
  have hi := (processedSlot D x jstar i).1.isLt
  by_cases hnext : (processedSlot D x jstar i).1.val < D.last x
  · have hsum := next_band_log_sum D hD z hL i hnext
    have hdata := hD
    obtain ⟨_, _, _, _, _, _, hroom, _⟩ := hdata
    have hroommul := mul_le_mul_of_nonneg_right hroom
      (scale_pos D hD x hL (processedSlot D x jstar i).1.val).le
    have hnextscale := scale_succ D x (processedSlot D x jstar i).1.val
    have hroom' : (D.c₂ + 1) * processedScale D x jstar i ≤
        ((D.r₀ : ℝ) - 1) * D.c₁ *
          D.scale x ((processedSlot D x jstar i).1.val + 1) := by
      rw [hnextscale]
      convert hroommul using 1 <;> simp only [processedScale, div_eq_mul_inv] <;> ring
    linarith
  · have hlast : (processedSlot D x jstar i).1.val = D.last x := by omega
    have hsum0 : 0 ≤ ∑ t ∈ Finset.univ.filter
        (fun t : ProcessedIndex D x jstar => i.val < t.val), processedLog D z t :=
      Finset.sum_nonneg (fun t _ => (processed_log_pos D hD z hL t).1.le)
    have heq : processedScale D x jstar i = D.scale x (D.last x) := by
      simp only [processedScale, hlast]
    rw [heq] at hupper ⊢
    linarith


end Erdos821.S56Core
