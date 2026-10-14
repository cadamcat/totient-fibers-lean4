import Erdos821.S56.ProcessedSlots

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem scale_add (D : BandData) (x : ℝ) (j k : ℕ) :
    D.scale x (j + k) = D.scale x j * (D.ratio⁻¹) ^ k := by
  simp only [BandData.scale, pow_add, div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

theorem scale_tail_bound (D : BandData) (hD : D.Valid) (x : ℝ) (hL : 0 < L x)
    (j N : ℕ) :
    (∑ k ∈ Finset.Icc j N, D.scale x k) ≤ D.scale x j / (1 - D.ratio⁻¹) := by
  have hr : 1 < D.ratio := hD.2.2.2.2.1
  have hrpos : 0 < D.ratio := zero_lt_one.trans hr
  have hir : 0 ≤ D.ratio⁻¹ := inv_nonneg.mpr hrpos.le
  have hir1 : D.ratio⁻¹ < 1 := (inv_lt_one₀ hrpos).mpr hr
  have hg := hasSum_geometric_of_lt_one hir hir1
  let s := (Finset.Icc j N).image (fun k => k - j)
  have hinj : Set.InjOn (fun k : ℕ => k - j) (Finset.Icc j N) := by
    intro k hk l hl heq
    obtain ⟨hk, _⟩ := Finset.mem_Icc.mp hk
    obtain ⟨hl, _⟩ := Finset.mem_Icc.mp hl
    dsimp only at heq
    omega
  have heq : (∑ k ∈ Finset.Icc j N, D.scale x k) =
      D.scale x j * ∑ k ∈ s, (D.ratio⁻¹) ^ k := by
    rw [Finset.mul_sum, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : j ≤ k := (Finset.mem_Icc.mp hk).1
    conv_lhs => rw [← Nat.add_sub_of_le hkj, scale_add]
  rw [heq, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (scale_pos D hD x hL j).le
  simpa only [hg.tsum_eq] using hg.summable.sum_le_tsum s (fun k _ => pow_nonneg hir k)

theorem processed_band_monotone (D : BandData) (x : ℝ) (jstar : ℕ)
    (i t : ProcessedIndex D x jstar) (hit : i ≤ t) :
    (processedSlot D x jstar i).1.val ≤ (processedSlot D x jstar t).1.val := by
  have h := ((pureIndices D x jstar).orderIsoOfFin rfl).monotone hit
  have hval : (((pureIndices D x jstar).orderIsoOfFin rfl i).val).val ≤
      (((pureIndices D x jstar).orderIsoOfFin rfl t).val).val := h
  exact Nat.div_le_div_right hval


theorem all_slot_scale_sum (D : BandData) (x : ℝ) (j : ℕ) :
    (∑ s ∈ Finset.univ.filter (fun s : D.Slot x => j ≤ s.1.val),
      D.c₂ * D.scale x s.1.val) =
      (D.r₀ : ℝ) * D.c₂ * ∑ k ∈ Finset.Icc j (D.last x), D.scale x k := by
  simp only [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [mul_ite, mul_zero]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    if j ≤ k then (D.r₀ : ℝ) * (D.c₂ * D.scale x k) else 0) (D.last x + 1)]
  have hset : (Finset.range (D.last x + 1)).filter (fun k => j ≤ k) =
      Finset.Icc j (D.last x) := by ext k; simp; omega
  rw [← Finset.sum_filter, hset]
  simp only [← mul_assoc, ← Finset.mul_sum]

theorem processed_log_tail_bound (D : BandData) (hD : D.Valid) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (hL : 0 < L x) (i : ProcessedIndex D x jstar) :
    (∑ t ∈ Finset.univ.filter (fun t : ProcessedIndex D x jstar => i.val ≤ t.val),
      processedLog D z t) ≤
      (D.r₀ : ℝ) * D.c₂ * processedScale D x jstar i / (1 - D.ratio⁻¹) := by
  let s := Finset.univ.filter (fun t : ProcessedIndex D x jstar => i.val ≤ t.val)
  let f := processedSlot D x jstar
  let q := Finset.univ.filter (fun a : D.Slot x => (f i).1.val ≤ a.1.val)
  have hsub : s.image f ⊆ q := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      processed_band_monotone D x jstar i t (Finset.mem_filter.mp ht).2⟩
  have hc2 : 0 < D.c₂ := hD.2.1.trans hD.2.2.1
  calc
    _ ≤ ∑ t ∈ s, D.c₂ * D.scale x (f t).1.val := by
      apply Finset.sum_le_sum
      intro t _
      exact (processed_log_bounds D z t).2
    _ = ∑ a ∈ s.image f, D.c₂ * D.scale x a.1.val := by
      rw [Finset.sum_image]
      exact fun a _ b _ h => processedSlot_injective D x jstar h
    _ ≤ ∑ a ∈ q, D.c₂ * D.scale x a.1.val :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun a _ _ => mul_nonneg hc2.le (scale_pos D hD x hL a.1.val).le)
    _ = (D.r₀ : ℝ) * D.c₂ * ∑ k ∈ Finset.Icc (f i).1.val (D.last x), D.scale x k :=
      all_slot_scale_sum D x (f i).1.val
    _ ≤ (D.r₀ : ℝ) * D.c₂ * (D.scale x (f i).1.val / (1 - D.ratio⁻¹)) :=
      mul_le_mul_of_nonneg_left (scale_tail_bound D hD x hL _ _) (by positivity)
    _ = _ := by dsimp [f, processedScale]; ring

theorem scale_antitone (D : BandData) (hD : D.Valid) (x : ℝ) (hL : 0 < L x)
    (i j : ℕ) (hij : i ≤ j) : D.scale x j ≤ D.scale x i := by
  have hr : 1 < D.ratio := hD.2.2.2.2.1
  exact div_le_div_of_nonneg_left (mul_pos hD.2.2.2.1 hL).le
    (pow_pos (zero_lt_one.trans hr) i) (pow_le_pow_right₀ hr.le hij)

def argumentRadius (D : BandData) : ℝ :=
  (D.r₀ : ℝ) * D.c₂ / (1 - D.ratio⁻¹) + D.c₂ + 1

theorem processed_argument_cap (D : BandData) (hD : D.Valid) {x : ℝ} {jstar : ℕ}
    (z : D.Lists x jstar) (hL : 0 < L x) (i : ProcessedIndex D x jstar) :
    (∑ t ∈ Finset.univ.filter (fun t : ProcessedIndex D x jstar => i.val ≤ t.val),
      processedLog D z t) + (D.c₂ + 1) * D.scale x (D.last x) ≤
        argumentRadius D * processedScale D x jstar i := by
  have ht := processed_log_tail_bound D hD z hL i
  have hc2 : 0 < D.c₂ := hD.2.1.trans hD.2.2.1
  have hs := scale_antitone D hD x hL (processedSlot D x jstar i).1.val (D.last x)
    (Nat.le_of_lt_succ (processedSlot D x jstar i).1.isLt)
  have hterm := mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ D.c₂ + 1)
  have heq : (D.r₀ : ℝ) * D.c₂ * processedScale D x jstar i / (1 - D.ratio⁻¹) +
      (D.c₂ + 1) * processedScale D x jstar i =
      argumentRadius D * processedScale D x jstar i := by unfold argumentRadius; ring
  rw [← heq]
  exact add_le_add ht hterm


end Erdos821.S56Core
