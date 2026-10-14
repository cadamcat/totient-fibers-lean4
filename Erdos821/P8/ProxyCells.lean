import Erdos821.Blueprint.Proxy

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

def logIndex (delta : ℝ) (n : ℕ) : ℤ := ⌈Real.log n / delta⌉ - 1

def logCellAt (delta : ℝ) (j : ℤ) : Finset ℕ :=
  Finset.Ioc ⌊Real.exp ((j : ℝ) * delta)⌋₊
    ⌊Real.exp (((j : ℝ) + 1) * delta)⌋₊

lemma logCell_eq_index (x S : ℝ) (n : ℕ) :
    logCell x S n = logCellAt (L x ^ (-S)) (logIndex (L x ^ (-S)) n) := rfl

lemma cell_width_pos {x : ℝ} (hx : 1 < x) (S : ℝ) : 0 < L x ^ (-S) :=
  Real.rpow_pos_of_pos (Real.log_pos hx) _

lemma mem_logCellAt_iff (delta : ℝ) (j : ℤ) (n : ℕ) :
    n ∈ logCellAt delta j ↔ 0 < n ∧ (j : ℝ) * delta < Real.log n ∧
      Real.log n ≤ ((j : ℝ) + 1) * delta := by
  unfold logCellAt
  rw [Finset.mem_Ioc]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hlo
    have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
    refine ⟨hn, ?_, ?_⟩
    · exact (Real.lt_log_iff_exp_lt hnr).mpr
        ((Nat.floor_lt' (ne_of_gt hn)).mp hlo)
    · exact (Real.log_le_iff_le_exp hnr).mpr
        ((Nat.le_floor_iff' (ne_of_gt hn)).mp hhi)
  · rintro ⟨hn, hlo, hhi⟩
    have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
    exact ⟨(Nat.floor_lt' (ne_of_gt hn)).mpr ((Real.lt_log_iff_exp_lt hnr).mp hlo),
      (Nat.le_floor_iff' (ne_of_gt hn)).mpr ((Real.log_le_iff_le_exp hnr).mp hhi)⟩

lemma logIndex_eq_of_mem {delta : ℝ} (hdelta : 0 < delta) {j : ℤ} {n : ℕ}
    (hn : n ∈ logCellAt delta j) : logIndex delta n = j := by
  rcases (mem_logCellAt_iff delta j n).mp hn with ⟨_, hlo, hhi⟩
  have hceil : ⌈Real.log n / delta⌉ = j + 1 := by
    apply Int.ceil_eq_iff.mpr
    simp only [Int.cast_add, Int.cast_one, add_sub_cancel_right]
    exact ⟨(lt_div_iff₀ hdelta).mpr hlo, (div_le_iff₀ hdelta).mpr hhi⟩
  unfold logIndex
  rw [hceil]
  omega

lemma mem_assigned_logCell {delta : ℝ} (hdelta : 0 < delta) {n : ℕ}
    (hn : 0 < n) : n ∈ logCellAt delta (logIndex delta n) := by
  rw [mem_logCellAt_iff]
  have hb := Int.ceil_eq_iff.mp (rfl : ⌈Real.log n / delta⌉ = ⌈Real.log n / delta⌉)
  refine ⟨hn, ?_, ?_⟩
  · simpa only [logIndex, Int.cast_sub, Int.cast_one] using (lt_div_iff₀ hdelta).mp hb.1
  · simpa only [logIndex, Int.cast_sub, Int.cast_one, sub_add_cancel] using
      (div_le_iff₀ hdelta).mp hb.2

lemma mem_logCell_self {x : ℝ} (hx : 1 < x) (S : ℝ) {n : ℕ} (hn : 0 < n) :
    n ∈ logCell x S n := by
  rw [logCell_eq_index]
  exact mem_assigned_logCell (cell_width_pos hx S) hn

lemma logCell_eq_of_mem {x : ℝ} (hx : 1 < x) (S : ℝ) {m n : ℕ}
    (hm : m ∈ logCell x S n) : logCell x S m = logCell x S n := by
  rw [logCell_eq_index] at hm
  have hi := logIndex_eq_of_mem (cell_width_pos hx S) hm
  simp only [logCell_eq_index, hi]

lemma abs_log_sub_le_width {x : ℝ} (hx : 1 < x) (S : ℝ) {m n : ℕ}
    (hn : 0 < n) (hm : m ∈ logCell x S n) :
    |Real.log m - Real.log n| ≤ L x ^ (-S) := by
  rw [logCell_eq_index] at hm
  have hn' := mem_assigned_logCell (cell_width_pos hx S) hn
  rcases (mem_logCellAt_iff _ _ m).mp hm with ⟨_, hmlo, hmhi⟩
  rcases (mem_logCellAt_iff _ _ n).mp hn' with ⟨_, hnlo, hnhi⟩
  simp only [add_mul, one_mul] at hmhi hnhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma proxyConstant_eq_of_mem (I : FactorTest) {x : ℝ} (hx : 1 < x) (S : ℝ)
    {m n : ℕ} (hm : m ∈ logCell x S n) :
    proxyConstant I x S m = proxyConstant I x S n := by
  simp only [proxyConstant, proxyDenominator, logCell_eq_of_mem hx S hm]

lemma logCell_eq_or_disjoint {x : ℝ} (hx : 1 < x) (S : ℝ) (m n : ℕ) :
    logCell x S m = logCell x S n ∨ Disjoint (logCell x S m) (logCell x S n) := by
  by_cases heq : logCell x S m = logCell x S n
  · exact Or.inl heq
  · right
    apply Finset.disjoint_left.mpr
    intro k hkm hkn
    exact heq ((logCell_eq_of_mem hx S hkm).symm.trans (logCell_eq_of_mem hx S hkn))

lemma proxyDenominator_pos_iff (x S : ℝ) (n : ℕ) :
    0 < proxyDenominator x S n ↔ ∃ m ∈ logCell x S n, rough (W x) m := by
  simp only [proxyDenominator, Finset.card_pos, Finset.filter_nonempty_iff]

lemma test_nonneg (I : FactorTest) (x : ℝ) (n : ℕ) : 0 ≤ test I x n := by
  cases I with
  | prime => simp only [test]; split_ifs <;> norm_num
  | rough gamma => simp only [test]; split_ifs <;> norm_num

lemma test_le_one (I : FactorTest) (x : ℝ) (n : ℕ) : test I x n ≤ 1 := by
  cases I with
  | prime => simp only [test]; split_ifs <;> norm_num
  | rough gamma => simp only [test]; split_ifs <;> norm_num

lemma proxyConstant_nonneg (I : FactorTest) (x S : ℝ) (n : ℕ) :
    0 ≤ proxyConstant I x S n := by
  unfold proxyConstant
  exact div_nonneg (Finset.sum_nonneg (fun m _ => test_nonneg I x m)) (by positivity)

lemma proxy_nonneg (I : FactorTest) (x S : ℝ) (n : ℕ) : 0 ≤ proxy I x S n := by
  unfold proxy
  split_ifs
  · exact proxyConstant_nonneg I x S n
  · exact le_rfl

lemma test_sum_le_denominator (I : FactorTest) (x S : ℝ) (n : ℕ)
    (hsubset : ∀ m ∈ logCell x S n, test I x m ≠ 0 → rough (W x) m) :
    (∑ m ∈ logCell x S n, test I x m) ≤ (proxyDenominator x S n : ℝ) := by
  calc
    (∑ m ∈ logCell x S n, test I x m) ≤
        ∑ m ∈ logCell x S n, (if rough (W x) m then 1 else 0 : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      by_cases hr : rough (W x) m
      · simpa only [hr, ite_true] using test_le_one I x m
      · have hz : test I x m = 0 := by
          by_contra h
          exact hr (hsubset m hm h)
        simp only [hr, ite_false, hz, le_refl]
    _ = (proxyDenominator x S n : ℝ) := by
      rw [← Finset.sum_filter]
      simp [proxyDenominator]

lemma proxyConstant_le_one (I : FactorTest) (x S : ℝ) (n : ℕ)
    (hden : 0 < proxyDenominator x S n)
    (hsubset : ∀ m ∈ logCell x S n, test I x m ≠ 0 → rough (W x) m) :
    proxyConstant I x S n ≤ 1 := by
  unfold proxyConstant
  apply (div_le_one (by exact_mod_cast hden)).mpr
  exact test_sum_le_denominator I x S n hsubset

lemma proxy_le_one (I : FactorTest) (x S : ℝ) (n : ℕ)
    (hden : 0 < proxyDenominator x S n)
    (hsubset : ∀ m ∈ logCell x S n, test I x m ≠ 0 → rough (W x) m) :
    proxy I x S n ≤ 1 := by
  unfold proxy
  split_ifs
  · exact proxyConstant_le_one I x S n hden hsubset
  · norm_num

/-- Full-cell matching is exact before any interval truncation. -/
theorem proxy_full_cell_sum (I : FactorTest) {x : ℝ} (hx : 1 < x) (S : ℝ) (n : ℕ)
    (hden : 0 < proxyDenominator x S n) :
    (∑ m ∈ logCell x S n, proxy I x S m) = ∑ m ∈ logCell x S n, test I x m := by
  have hdenr : (proxyDenominator x S n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hden)
  calc
    (∑ m ∈ logCell x S n, proxy I x S m) =
        ∑ m ∈ logCell x S n, if rough (W x) m then proxyConstant I x S n else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [proxy, proxyConstant_eq_of_mem I hx S hm]
    _ = (proxyDenominator x S n : ℝ) * proxyConstant I x S n := by
      rw [← Finset.sum_filter]
      simp [proxyDenominator, nsmul_eq_mul]
    _ = ∑ m ∈ logCell x S n, test I x m := by
      unfold proxyConstant
      field_simp

theorem proxy_full_cell_difference (I : FactorTest) {x : ℝ} (hx : 1 < x) (S : ℝ) (n : ℕ)
    (hden : 0 < proxyDenominator x S n) :
    (∑ m ∈ logCell x S n, (test I x m - proxy I x S m)) = 0 := by
  rw [Finset.sum_sub_distrib, proxy_full_cell_sum I hx S n hden, sub_self]

theorem proxy_full_cell_complex_difference (I : FactorTest) {x : ℝ} (hx : 1 < x)
    (S : ℝ) (n : ℕ) (hden : 0 < proxyDenominator x S n) :
    (∑ m ∈ logCell x S n, ((test I x m - proxy I x S m : ℝ) : ℂ)) = 0 := by
  exact_mod_cast proxy_full_cell_difference I hx S n hden

theorem proxyDifference_norm_le_one (I : FactorTest) (x S lo hi : ℝ) (n : ℕ)
    (hden : 0 < proxyDenominator x S n)
    (hsubset : ∀ m ∈ logCell x S n, test I x m ≠ 0 → rough (W x) m) :
    ‖proxyDifference I x S lo hi n‖ ≤ 1 := by
  have htn := test_nonneg I x n
  have htu := test_le_one I x n
  have hpn := proxy_nonneg I x S n
  have hpu := proxy_le_one I x S n hden hsubset
  have hd : |test I x n - proxy I x S n| ≤ 1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  unfold proxyDifference
  split_ifs
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using hd
  · simp

theorem proxyDifference_norm_le_one_on_range (I : FactorTest) (x S lo hi : ℝ) (n : ℕ)
    (hcell : lo ≤ (n : ℝ) → (n : ℝ) ≤ hi →
      0 < proxyDenominator x S n ∧
        ∀ m ∈ logCell x S n, test I x m ≠ 0 → rough (W x) m) :
    ‖proxyDifference I x S lo hi n‖ ≤ 1 := by
  by_cases hn : lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi
  · rcases hcell hn.1 hn.2 with ⟨hden, hsubset⟩
    exact proxyDifference_norm_le_one I x S lo hi n hden hsubset
  · simp [proxyDifference, hn]

end Erdos821.P8Core

