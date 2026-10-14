import Erdos821.P8.ProxySupport

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

def mellinWeight (y u : ℝ) : ℂ := mellin y u / (y : ℂ)

lemma mellinWeight_eq_exp {y : ℝ} (hy : 0 < y) (u : ℝ) :
    mellinWeight y u = Complex.exp ((Complex.I * (u : ℂ) - 1) * (Real.log y : ℂ)) := by
  unfold mellinWeight Blueprint.Analytic.mellin
  have hexp : Complex.exp (Real.log y : ℂ) = (y : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hy]
  rw [div_eq_mul_inv, ← hexp, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  ring

lemma norm_mellinWeight {y : ℝ} (hy : 0 < y) (u : ℝ) :
    ‖mellinWeight y u‖ = y⁻¹ := by
  unfold mellinWeight
  rw [norm_div]
  have hm : ‖mellin y u‖ = 1 := by
    simp [Blueprint.Analytic.mellin, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  rw [hm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy, one_div]

lemma mellinWeight_mul_exp_log_sub {y z : ℝ} (hy : 0 < y) (hz : 0 < z) (u : ℝ) :
    mellinWeight y u = mellinWeight z u *
      Complex.exp ((Complex.I * (u : ℂ) - 1) * ((Real.log y - Real.log z : ℝ) : ℂ)) := by
  rw [mellinWeight_eq_exp hy, mellinWeight_eq_exp hz, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_mellin_slope (u : ℝ) : ‖Complex.I * (u : ℂ) - 1‖ ≤ 1 + |u| := by
  calc
    ‖Complex.I * (u : ℂ) - 1‖ ≤ ‖Complex.I * (u : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 1 + |u| := by simp [Complex.norm_real, Real.norm_eq_abs, add_comm]

theorem mellinWeight_variation {y z delta : ℝ} (hy : 0 < y) (hz : 0 < z) (u : ℝ)
    (hclose : |Real.log y - Real.log z| ≤ delta)
    (hsmall : (1 + |u|) * delta ≤ 1) :
    ‖mellinWeight y u - mellinWeight z u‖ ≤ 2 * (1 + |u|) * delta / z := by
  let v : ℂ := (Complex.I * (u : ℂ) - 1) * ((Real.log y - Real.log z : ℝ) : ℂ)
  have harg : ‖v‖ ≤ (1 + |u|) * delta := by
    dsimp only [v]
    rw [norm_mul]
    apply mul_le_mul (norm_mellin_slope u)
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hclose
    · exact norm_nonneg _
    · positivity
  have he : ‖Complex.exp v - 1‖ ≤ 2 * ((1 + |u|) * delta) :=
    (Complex.norm_exp_sub_one_le (harg.trans hsmall)).trans
      (mul_le_mul_of_nonneg_left harg (by norm_num))
  have hfactor : mellinWeight y u - mellinWeight z u =
      mellinWeight z u * (Complex.exp v - 1) := by
    rw [mellinWeight_mul_exp_log_sub hy hz]
    dsimp only [v]
    ring
  rw [hfactor, norm_mul, norm_mellinWeight hz]
  calc
    z⁻¹ * ‖Complex.exp v - 1‖ ≤ z⁻¹ * (2 * ((1 + |u|) * delta)) :=
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hz.le)
    _ = 2 * (1 + |u|) * delta / z := by rw [div_eq_mul_inv]; ring

theorem eventually_mellin_small_argument (B S : ℝ) (hB : 0 < B) (hBS : B < S) :
    ∀ᶠ x : ℝ in atTop, ∀ u : ℝ, |u| ≤ L x ^ B → (1 + |u|) * L x ^ (-S) ≤ 1 := by
  have ht : Tendsto (fun x : ℝ => L x ^ (-(S - B))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < S - B)).comp Real.tendsto_log_atTop
  have hsmall : ∀ᶠ x : ℝ in atTop, L x ^ (B - S) ≤ (1 / 2 : ℝ) := by
    filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with x hx
    simpa only [neg_sub] using hx.le
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hsmall, hL] with x hx hLx
  intro u hu
  have hL0 : 0 < L x := zero_lt_one.trans_le hLx
  have hpow1 : 1 ≤ L x ^ B := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hLx hB.le
  have hcoef : 1 + |u| ≤ 2 * L x ^ B := by linarith
  calc
    (1 + |u|) * L x ^ (-S) ≤ (2 * L x ^ B) * L x ^ (-S) :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hL0.le _)
    _ = 2 * L x ^ (B - S) := by
      simp only [mul_assoc, ← Real.rpow_add hL0, sub_eq_add_neg]
    _ ≤ 1 := by linarith

theorem mellin_cell_variation {x : ℝ} (hx : 1 < x) (S u : ℝ) {m n : ℕ}
    (hn : 0 < n) (hm : m ∈ logCell x S n) (hsmall : (1 + |u|) * L x ^ (-S) ≤ 1) :
    ‖mellinWeight m u - mellinWeight n u‖ ≤ 2 * (1 + |u|) * L x ^ (-S) / (m : ℝ) := by
  have hm0 : 0 < m := by
    rw [logCell_eq_index] at hm
    exact ((mem_logCellAt_iff _ _ m).mp hm).1
  have hclose : |Real.log (n : ℝ) - Real.log (m : ℝ)| ≤ L x ^ (-S) := by
    simpa only [abs_sub_comm] using abs_log_sub_le_width hx S hn hm
  rw [norm_sub_rev]
  exact mellinWeight_variation (by exact_mod_cast hn) (by exact_mod_cast hm0) u hclose hsmall

lemma norm_weighted_sum_zero_sum (s : Finset ℕ) (c w : ℕ → ℂ) (z : ℂ) (M : ℕ → ℝ)
    (hzero : (∑ n ∈ s, c n) = 0) (hc : ∀ n ∈ s, ‖c n‖ ≤ 1)
    (hw : ∀ n ∈ s, ‖w n - z‖ ≤ M n) :
    ‖∑ n ∈ s, c n * w n‖ ≤ ∑ n ∈ s, M n := by
  have heq : (∑ n ∈ s, c n * w n) = ∑ n ∈ s, c n * (w n - z) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, zero_mul, sub_zero]
  rw [heq]
  calc
    ‖∑ n ∈ s, c n * (w n - z)‖ ≤ ∑ n ∈ s, ‖c n * (w n - z)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s, M n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul (hc n hn) (hw n hn) (norm_nonneg _) (by norm_num)

lemma norm_cell_difference_le_one (I : FactorTest) {x : ℝ} (hx : 1 < x) (S : ℝ) (n : ℕ)
    (hden : 0 < proxyDenominator x S n)
    (hsubset : ∀ m ∈ logCell x S n, test I x m ≠ 0 → rough (W x) m)
    {m : ℕ} (hm : m ∈ logCell x S n) :
    ‖((test I x m - proxy I x S m : ℝ) : ℂ)‖ ≤ 1 := by
  have hc := proxyConstant_le_one I x S n hden hsubset
  have hp1 : proxy I x S m ≤ 1 := by
    unfold proxy
    split_ifs
    · rw [proxyConstant_eq_of_mem I hx S hm]
      exact hc
    · norm_num
  have hp0 := proxy_nonneg I x S m
  have ht0 := test_nonneg I x m
  have ht1 := test_le_one I x m
  simp only [Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The weighted error is controlled by the cell's actual harmonic mass. -/
theorem norm_proxy_full_cell_mellin_le (I : FactorTest) {x : ℝ} (hx : 1 < x)
    (S u : ℝ) (n : ℕ) (hn : 0 < n) (hden : 0 < proxyDenominator x S n)
    (hsubset : ∀ m ∈ logCell x S n, test I x m ≠ 0 → rough (W x) m)
    (hsmall : (1 + |u|) * L x ^ (-S) ≤ 1) :
    ‖∑ m ∈ logCell x S n, ((test I x m - proxy I x S m : ℝ) : ℂ) *
      mellin m u / (m : ℂ)‖ ≤
      2 * (1 + |u|) * L x ^ (-S) * (∑ m ∈ logCell x S n, (m : ℝ)⁻¹) := by
  have hbound := norm_weighted_sum_zero_sum (logCell x S n)
    (fun m => ((test I x m - proxy I x S m : ℝ) : ℂ)) (fun m => mellinWeight m u)
    (mellinWeight n u) (fun m => 2 * (1 + |u|) * L x ^ (-S) / (m : ℝ))
    (proxy_full_cell_complex_difference I hx S n hden)
    (fun m hm => norm_cell_difference_le_one I hx S n hden hsubset hm)
    (fun m hm => mellin_cell_variation hx S u hn hm hsmall)
  calc
    ‖∑ m ∈ logCell x S n, ((test I x m - proxy I x S m : ℝ) : ℂ) *
        mellin m u / (m : ℂ)‖ ≤
        ∑ m ∈ logCell x S n, 2 * (1 + |u|) * L x ^ (-S) / (m : ℝ) := by
      simpa only [mellinWeight, mul_div_assoc, Complex.ofReal_natCast] using hbound
    _ = 2 * (1 + |u|) * L x ^ (-S) *
        (∑ m ∈ logCell x S n, (m : ℝ)⁻¹) := by
      simp only [div_eq_mul_inv, Finset.mul_sum]

/-- A truncated cell has a direct harmonic-mass bound without count cancellation. -/
theorem norm_proxy_subcell_mellin_le (I : FactorTest) {x : ℝ} (hx : 1 < x)
    (S u : ℝ) (n : ℕ) (hden : 0 < proxyDenominator x S n)
    (hsubset : ∀ m ∈ logCell x S n, test I x m ≠ 0 → rough (W x) m)
    (s : Finset ℕ) (hs : s ⊆ logCell x S n) :
    ‖∑ m ∈ s, ((test I x m - proxy I x S m : ℝ) : ℂ) *
      mellin m u / (m : ℂ)‖ ≤ ∑ m ∈ s, (m : ℝ)⁻¹ := by
  calc
    ‖∑ m ∈ s, ((test I x m - proxy I x S m : ℝ) : ℂ) * mellin m u / (m : ℂ)‖ ≤
        ∑ m ∈ s, ‖((test I x m - proxy I x S m : ℝ) : ℂ) * mellin m u / (m : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m ∈ s, (m : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro m hm
      have hmcell := hs hm
      have hm0 : 0 < m := by
        rw [logCell_eq_index] at hmcell
        exact ((mem_logCellAt_iff _ _ m).mp hmcell).1
      have hw : ‖mellin m u / (m : ℂ)‖ = (m : ℝ)⁻¹ := by
        simpa only [mellinWeight, Complex.ofReal_natCast] using
          norm_mellinWeight (by exact_mod_cast hm0 : 0 < (m : ℝ)) u
      rw [mul_div_assoc, norm_mul, hw]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (norm_cell_difference_le_one I hx S n hden hsubset (hs hm)) (by positivity)

theorem eventually_principal_cell_mellin_bound (b kappa B S : ℝ)
    (hb : 0 < b) (hB : 0 < B) (hBS : B < S) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : FactorTest) (n r : ℕ) (u : ℝ), TestAllowed b kappa I →
      x ^ (b / 4) ≤ (n : ℝ) → 0 < r → (r : ℝ) ≤ L x ^ B → |u| ≤ L x ^ B →
      0 < proxyDenominator x S n →
      ‖∑ m ∈ logCell x S n, ((test I x m - proxy I x S m : ℝ) : ℂ) *
        (1 : DirichletCharacter ℂ r) (m : ZMod r) * mellin m u / (m : ℂ)‖ ≤
        2 * (1 + |u|) * L x ^ (-S) * (∑ m ∈ logCell x S n, (m : ℝ)⁻¹) := by
  have hS : 0 < S := hB.trans hBS
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_log_power_lt_W B hB,
    eventually_test_supported_on_cells b kappa S hb hS,
    eventually_mellin_small_argument B S hB hBS] with x hx hmod hs harg
  intro I n r u hallowed hn hr hsmall hu hden
  have hn0 : 0 < n := by
    exact_mod_cast (Real.rpow_pos_of_pos (by linarith : 0 < x) (b / 4)).trans_le hn
  have hsubset := hs I n hallowed hn
  have heq : (∑ m ∈ logCell x S n, ((test I x m - proxy I x S m : ℝ) : ℂ) *
      (1 : DirichletCharacter ℂ r) (m : ZMod r) * mellin m u / (m : ℂ)) =
      ∑ m ∈ logCell x S n, ((test I x m - proxy I x S m : ℝ) : ℂ) *
        mellin m u / (m : ℂ) := by
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hrough : rough (W x) m
    · rw [principal_character_eq_one_of_rough hr (hsmall.trans hmod.le) hrough, mul_one]
    · have ht0 : test I x m = 0 := by
        by_contra ht
        exact hrough (hsubset m hm ht)
      simp [proxy, hrough, ht0]
  rw [heq]
  exact norm_proxy_full_cell_mellin_le I hx S u n hn0 hden hsubset (harg u hu)

end Erdos821.P8Core

