import Erdos821.P8.ProxyCells

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

lemma sqrt_lt_linear_sub_one {a z : ℝ} (ha : 0 < a) (hz : 0 ≤ z)
    (hlarge : (2 / a + 2) ^ 2 ≤ z) : Real.sqrt z < a * z - 1 := by
  have hk : 0 ≤ 2 / a + 2 := by positivity
  have hs : 2 / a + 2 ≤ Real.sqrt z := (Real.le_sqrt hk hz).mpr hlarge
  have hdiv : 2 / a ≤ Real.sqrt z := by linarith
  have hmul : 2 ≤ Real.sqrt z * a := (div_le_iff₀ ha).mp hdiv
  have hmain : 2 * Real.sqrt z ≤ a * z := calc
    2 * Real.sqrt z ≤ (Real.sqrt z * a) * Real.sqrt z :=
      mul_le_mul_of_nonneg_right hmul (Real.sqrt_nonneg z)
    _ = a * (Real.sqrt z * Real.sqrt z) := by ring
    _ = a * z := by rw [Real.mul_self_sqrt hz]
  have hdiv0 : 0 ≤ 2 / a := by positivity
  linarith

lemma eventually_sqrt_log_lt_linear (a : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, 1 < x ∧ 1 ≤ L x ∧ Real.sqrt (L x) < a * L x - 1 := by
  have hlog : ∀ᶠ x : ℝ in atTop, max 1 ((2 / a + 2) ^ 2) ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hlog] with x hx hL
  have hL1 : 1 ≤ L x := (le_max_left _ _).trans hL
  exact ⟨hx, hL1, sqrt_lt_linear_sub_one ha (by linarith)
    ((le_max_right _ _).trans hL)⟩

theorem eventually_W_lt_rpow (a : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, W x < x ^ a := by
  filter_upwards [eventually_sqrt_log_lt_linear a ha] with x hx
  rw [W, Real.rpow_def_of_pos (by linarith [hx.1]), Real.exp_lt_exp]
  have hlin : Real.sqrt (L x) < a * L x := by linarith [hx.2.2]
  simpa only [L, mul_comm] using hlin

theorem eventually_W_le_rpow_exponent_ge (a : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, ∀ gamma : ℝ, a ≤ gamma → W x ≤ x ^ gamma := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_W_lt_rpow a ha] with x hx hW
  intro gamma hgamma
  exact hW.le.trans (Real.rpow_le_rpow_of_exponent_le hx.le hgamma)

theorem eventually_cell_members_gt_W (a S : ℝ) (ha : 0 < a) (hS : 0 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, x ^ a ≤ (n : ℝ) →
      ∀ m ∈ logCell x S n, W x < (m : ℝ) := by
  filter_upwards [eventually_sqrt_log_lt_linear a ha] with x hx
  intro n hsize m hm
  have hx0 : 0 < x := by linarith [hx.1]
  have hnr : 0 < (n : ℝ) := (Real.rpow_pos_of_pos hx0 a).trans_le hsize
  have hn : 0 < n := by exact_mod_cast hnr
  have hmr : 0 < (m : ℝ) := by
    rw [logCell_eq_index] at hm
    exact_mod_cast ((mem_logCellAt_iff _ _ m).mp hm).1
  have hwidth : L x ^ (-S) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx.2.1 (by linarith)
  have hlogn : a * L x ≤ Real.log n := by
    apply (Real.le_log_iff_exp_le hnr).mpr
    simpa only [L, Real.rpow_def_of_pos hx0, mul_comm] using hsize
  have hclose := (abs_le.mp (abs_log_sub_le_width hx.1 S hn hm)).1
  have hlogm : Real.sqrt (L x) < Real.log m := by linarith [hx.2.2]
  exact (Real.lt_log_iff_exp_lt hmr).mp hlogm

lemma rough_of_prime_of_lt {y : ℝ} {n : ℕ} (hn : n.Prime) (hy : y < (n : ℝ)) :
    rough y n := by
  refine ⟨hn.pos, ?_⟩
  intro p hp hpn
  have heq : p = n := (Nat.prime_dvd_prime_iff_eq hp hn).mp hpn
  simpa only [heq] using hy

lemma rough_mono_cutoff {y z : ℝ} {n : ℕ} (hyz : y ≤ z) (hn : rough z n) :
    rough y n := by
  exact ⟨hn.1, fun p hp hpn => hyz.trans_lt (hn.2 p hp hpn)⟩

/-- The support inclusion is uniform in every allowed exponent bin. -/
theorem eventually_test_supported_on_cells (b kappa S : ℝ) (hb : 0 < b) (hS : 0 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : FactorTest) (n : ℕ), TestAllowed b kappa I →
      x ^ (b / 4) ≤ (n : ℝ) →
      ∀ m ∈ logCell x S n, test I x m ≠ 0 → rough (W x) m := by
  filter_upwards [eventually_cell_members_gt_W (b / 4) S (by linarith) hS,
    eventually_W_le_rpow_exponent_ge b hb] with x hcell hpow
  intro I n hallowed hn m hm htest
  cases I with
  | prime =>
      have hp : m.Prime := by
        by_contra hp
        simp only [test, hp, ite_false, ne_eq, not_true_eq_false] at htest
      exact rough_of_prime_of_lt hp (hcell n hn m hm)
  | rough gamma =>
      change b ≤ gamma ∧ gamma ≤ 1 / 2 - kappa at hallowed
      have hr : rough (x ^ gamma) m := by
        by_contra hr
        simp only [test, hr, ite_false, ne_eq, not_true_eq_false] at htest
      exact rough_mono_cutoff (hpow gamma hallowed.1) hr

theorem eventually_proxy_bounds_given_denominator (b kappa S : ℝ)
    (hb : 0 < b) (hS : 0 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : FactorTest) (n : ℕ), TestAllowed b kappa I →
      x ^ (b / 4) ≤ (n : ℝ) → 0 < proxyDenominator x S n →
      0 ≤ proxyConstant I x S n ∧ proxyConstant I x S n ≤ 1 ∧
        0 ≤ proxy I x S n ∧ proxy I x S n ≤ 1 := by
  filter_upwards [eventually_test_supported_on_cells b kappa S hb hS] with x hs
  intro I n hallowed hn hden
  have hsupport := hs I n hallowed hn
  exact ⟨proxyConstant_nonneg I x S n, proxyConstant_le_one I x S n hden hsupport,
    proxy_nonneg I x S n, proxy_le_one I x S n hden hsupport⟩

/-- The uniform coefficient bound requires denominator positivity only inside the range. -/
theorem eventually_proxy_difference_bound (b kappa S : ℝ) (hb : 0 < b) (hS : 0 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : FactorTest) (lo hi : ℝ), TestAllowed b kappa I →
      x ^ (b / 4) ≤ lo →
      (∀ n : ℕ, lo ≤ (n : ℝ) → (n : ℝ) ≤ hi → 0 < proxyDenominator x S n) →
      ∀ n : ℕ, ‖proxyDifference I x S lo hi n‖ ≤ 1 := by
  filter_upwards [eventually_test_supported_on_cells b kappa S hb hS] with x hs
  intro I lo hi hallowed hlo hden n
  apply proxyDifference_norm_le_one_on_range
  intro hnlo hnhi
  exact ⟨hden n hnlo hnhi, hs I n hallowed (hlo.trans hnlo)⟩

theorem eventually_log_power_lt_W (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℝ in atTop, L x ^ B < W x := by
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).bound
    (show 0 < (2 * B)⁻¹ by positivity)
  have hbase : ∀ᶠ z : ℝ in atTop, 1 ≤ z ∧ B * Real.log z < Real.sqrt z := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall] with z hz hbnd
    have hz0 : 0 < z := by linarith
    have hbnd' : Real.log z ≤ (2 * B)⁻¹ * z ^ (1 / 2 : ℝ) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hz),
        abs_of_nonneg (Real.rpow_nonneg hz0.le _)] using hbnd
    have hB0 : B ≠ 0 := ne_of_gt hB
    have hscaled : B * Real.log z ≤ (1 / 2 : ℝ) * Real.sqrt z := calc
      B * Real.log z ≤ B * ((2 * B)⁻¹ * z ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hbnd' hB.le
      _ = (1 / 2 : ℝ) * Real.sqrt z := by
        rw [Real.sqrt_eq_rpow]
        field_simp
    exact ⟨hz, by have := Real.sqrt_pos.mpr hz0; linarith⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hbase] with x hx
  have hL0 : 0 < L x := zero_lt_one.trans_le hx.1
  rw [Real.rpow_def_of_pos hL0, W, Real.exp_lt_exp]
  simpa only [L, mul_comm] using hx.2

lemma rough_coprime_small_modulus {y : ℝ} {n r : ℕ}
    (hr : 0 < r) (hsmall : (r : ℝ) ≤ y) (hn : rough y n) : Nat.Coprime n r := by
  apply Nat.coprime_of_dvd
  intro p hp hpn hpr
  have hle : (p : ℝ) ≤ r := by exact_mod_cast Nat.le_of_dvd hr hpr
  exact (not_lt_of_ge (hle.trans hsmall)) (hn.2 p hp hpn)

lemma principal_character_eq_one_of_rough {x : ℝ} {n r : ℕ}
    (hr : 0 < r) (hsmall : (r : ℝ) ≤ W x) (hn : rough (W x) n) :
    (1 : DirichletCharacter ℂ r) (n : ZMod r) = 1 :=
  MulChar.one_apply ((ZMod.isUnit_iff_coprime n r).mpr
    (rough_coprime_small_modulus hr hsmall hn))

theorem eventually_proxy_difference_rough_support (b kappa S : ℝ)
    (hb : 0 < b) (hS : 0 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : FactorTest) (lo hi : ℝ), TestAllowed b kappa I →
      x ^ (b / 4) ≤ lo → ∀ n : ℕ,
        proxyDifference I x S lo hi n ≠ 0 → rough (W x) n := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_test_supported_on_cells b kappa S hb hS] with x hx hs
  intro I lo hi hallowed hlo n hne
  have hnrange : lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi := by
    by_contra h
    simp only [proxyDifference, h, ite_false, ne_eq, not_true_eq_false] at hne
  have hsize : x ^ (b / 4) ≤ (n : ℝ) := hlo.trans hnrange.1
  have hn0 : 0 < n := by
    exact_mod_cast (Real.rpow_pos_of_pos (by linarith : 0 < x) (b / 4)).trans_le hsize
  by_contra hr
  have ht0 : test I x n = 0 := by
    by_contra ht
    exact hr (hs I n hallowed hsize n (mem_logCell_self hx S hn0) ht)
  have hp0 : proxy I x S n = 0 := by simp only [proxy, hr, ite_false]
  simp [proxyDifference, hnrange, ht0, hp0] at hne

theorem eventually_principal_character_difference (b kappa B S : ℝ)
    (hb : 0 < b) (hB : 0 < B) (hS : 0 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : FactorTest) (lo hi : ℝ) (r : ℕ),
      TestAllowed b kappa I → x ^ (b / 4) ≤ lo → 0 < r → (r : ℝ) ≤ L x ^ B →
      ∀ n : ℕ, (1 : DirichletCharacter ℂ r) (n : ZMod r) *
        proxyDifference I x S lo hi n = proxyDifference I x S lo hi n := by
  filter_upwards [eventually_log_power_lt_W B hB,
    eventually_proxy_difference_rough_support b kappa S hb hS] with x hmod hs
  intro I lo hi r hallowed hlo hr hsmall n
  by_cases hz : proxyDifference I x S lo hi n = 0
  · simp only [hz, mul_zero]
  · rw [principal_character_eq_one_of_rough hr (hsmall.trans hmod.le)
      (hs I lo hi hallowed hlo n hz), one_mul]

theorem eventually_principal_cell_cancellation (b kappa B S : ℝ)
    (hb : 0 < b) (hB : 0 < B) (hS : 0 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : FactorTest) (n r : ℕ), TestAllowed b kappa I →
      x ^ (b / 4) ≤ (n : ℝ) → 0 < r → (r : ℝ) ≤ L x ^ B →
      0 < proxyDenominator x S n →
      (∑ m ∈ logCell x S n, (1 : DirichletCharacter ℂ r) (m : ZMod r) *
        ((test I x m - proxy I x S m : ℝ) : ℂ)) = 0 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_log_power_lt_W B hB,
    eventually_test_supported_on_cells b kappa S hb hS] with x hx hmod hs
  intro I n r hallowed hn hr hsmall hden
  have heq : (∑ m ∈ logCell x S n, (1 : DirichletCharacter ℂ r) (m : ZMod r) *
      ((test I x m - proxy I x S m : ℝ) : ℂ)) =
      ∑ m ∈ logCell x S n, ((test I x m - proxy I x S m : ℝ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hrough : rough (W x) m
    · rw [principal_character_eq_one_of_rough hr (hsmall.trans hmod.le) hrough, one_mul]
    · have ht0 : test I x m = 0 := by
        by_contra ht
        exact hrough (hs I n hallowed hn m hm ht)
      simp only [proxy, hrough, ite_false, ht0, sub_self, Complex.ofReal_zero, mul_zero]
  rw [heq]
  exact proxy_full_cell_complex_difference I hx S n hden

end Erdos821.P8Core

