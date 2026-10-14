import Erdos821.P8.RoughCharacters

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

lemma logIndex_nonneg_shift {delta : ℝ} (hdelta : 0 < delta) (n : ℕ) :
    -1 ≤ logIndex delta n := by
  have hceil : 0 ≤ ⌈Real.log n / delta⌉ :=
    Int.ceil_nonneg (div_nonneg (Real.log_natCast_nonneg n) hdelta.le)
  unfold logIndex
  omega

lemma logIndex_le_probe {x delta : ℝ} (hx : 1 < x) (hdelta : 0 < delta)
    {n : ℕ} (hn : 0 < n) (hhi : (n : ℝ) ≤ x ^ (2 : ℕ)) :
    logIndex delta n ≤ ⌈2 * L x / delta⌉ - 1 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log n ≤ 2 * L x := by
    simpa only [Real.log_pow, Nat.cast_ofNat, L] using Real.log_le_log hn0 hhi
  unfold logIndex
  exact sub_le_sub_right (Int.ceil_mono (div_le_div_of_nonneg_right hlog hdelta.le)) _

theorem interval_logIndex_count_le {x delta : ℝ} (hx : 1 < x) (hdelta : 0 < delta)
    {a z : ℕ} (ha : 0 < a) (hz : (z : ℝ) ≤ x ^ (2 : ℕ)) :
    (((Finset.Icc a z).image (logIndex delta)).card : ℝ) ≤ 2 * L x / delta + 2 := by
  let J : ℤ := ⌈2 * L x / delta⌉
  have hJ : 0 ≤ J := Int.ceil_nonneg (by have := (Real.log_pos hx).le; positivity)
  have hsubset : (Finset.Icc a z).image (logIndex delta) ⊆ Finset.Icc (-1) (J - 1) := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨n, hn, rfl⟩
    rcases Finset.mem_Icc.mp hn with ⟨han, hnz⟩
    exact Finset.mem_Icc.mpr ⟨logIndex_nonneg_shift hdelta n,
      logIndex_le_probe hx hdelta (ha.trans_le han) ((by exact_mod_cast hnz : (n : ℝ) ≤ z).trans hz)⟩
  have hcard := Finset.card_le_card hsubset
  have hJ1 : 0 ≤ J + 1 := by omega
  have hceil := Int.ceil_lt_add_one (2 * L x / delta)
  calc
    (((Finset.Icc a z).image (logIndex delta)).card : ℝ) ≤
        ((Finset.Icc (-1 : ℤ) (J - 1)).card : ℝ) := by exact_mod_cast hcard
    _ = (J : ℝ) + 1 := by
      rw [Int.card_Icc]
      have heq : J - 1 + 1 - (-1) = J + 1 := by ring
      rw [heq, ← Int.cast_natCast, Int.toNat_of_nonneg hJ1]
      push_cast
      ring
    _ ≤ 2 * L x / delta + 2 := by change (⌈2 * L x / delta⌉ : ℝ) + 1 ≤ _; linarith

theorem interval_logCell_count_le {x : ℝ} (hx : 1 < x) (hL : 1 ≤ L x) (S : ℝ)
    (hS : 0 < S) {a z : ℕ} (ha : 0 < a) (hz : (z : ℝ) ≤ x ^ (2 : ℕ)) :
    (((Finset.Icc a z).image (logIndex (L x ^ (-S)))).card : ℝ) ≤ 4 * L x ^ (S + 1) := by
  have hL0 : 0 < L x := zero_lt_one.trans_le hL
  have hLP : 1 ≤ L x ^ (S + 1) := Real.one_le_rpow hL (by linarith)
  apply (interval_logIndex_count_le hx (cell_width_pos hx S) ha hz).trans
  have heq : 2 * L x / L x ^ (-S) = 2 * L x ^ (S + 1) := by
    rw [Real.rpow_neg hL0.le, div_inv_eq_mul, Real.rpow_add_one hL0.ne']
    ring
  rw [heq]
  linarith

lemma interval_logIndex_fiber_shape {delta : ℝ} (hdelta : 0 < delta)
    {a z : ℕ} (ha : 0 < a) (j : ℤ) :
    ((Finset.Icc a z).filter (fun m => logIndex delta m = j)) =
      Finset.Icc (max a (⌊Real.exp ((j : ℝ) * delta)⌋₊ + 1))
        (min z ⌊Real.exp (((j : ℝ) + 1) * delta)⌋₊) := by
  have heq : ((Finset.Icc a z).filter (fun m => logIndex delta m = j)) =
      Finset.Icc a z ∩ logCellAt delta j := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · intro hm
      exact ⟨hm.1, interval_logIndex_fiber_subset hdelta ha j (Finset.mem_filter.mpr hm)⟩
    · intro hm
      exact ⟨hm.1, logIndex_eq_of_mem hdelta hm.2⟩
  rw [heq]
  ext m
  simp only [Finset.mem_inter, logCellAt, Finset.mem_Icc, Finset.mem_Ioc, max_le_iff, le_min_iff]
  omega

lemma Icc_eq_real_Ioc {m k : ℕ} (hm : 0 < m) :
    Finset.Icc m k = Finset.Ioc ⌊(m : ℝ) - 1⌋₊ ⌊(k : ℝ)⌋₊ := by
  have hfloor : ⌊(m : ℝ) - 1⌋₊ = m - 1 := by
    have heq : (m : ℝ) - 1 = ((m - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    rw [heq, Nat.floor_natCast]
  rw [hfloor, Nat.floor_natCast]
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

theorem eventually_integer_lower_endpoint (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, ∀ m : ℕ, x ^ (b / 4) ≤ (m : ℝ) →
      x ^ (b / 8) ≤ (m : ℝ) - 1 := by
  have hlarge : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ (b / 8) :=
    (tendsto_rpow_atTop (by linarith : 0 < b / 8)).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hlarge] with x hx hpow
  intro m hm
  have hx0 : 0 < x := by linarith
  have heq : x ^ (b / 4) = x ^ (b / 8) * x ^ (b / 8) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [heq] at hm
  nlinarith

end Erdos821.P8Core

