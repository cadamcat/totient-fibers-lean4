import Erdos821.P8.CellIntervals

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

lemma interval_restrict_sum {M : Type*} [AddCommMonoid M] (a b : ℕ)
    (lo hi : ℝ) (hhi : 0 ≤ hi) (f : ℕ → M) :
    (∑ n ∈ Finset.Icc a b, if lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi then f n else 0) =
      ∑ n ∈ Finset.Icc (max a ⌈lo⌉₊) (min b ⌊hi⌋₊), f n := by
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, max_le_iff, le_min_iff,
    Nat.ceil_le, Nat.le_floor_iff hhi]
  tauto

lemma proxy_probe_sum_eq (I : FactorTest) (x S lo hi probeLo probeHi u : ℝ)
    (hhi : 0 ≤ hi) :
    (∑ n ∈ Finset.Icc ⌈probeLo⌉₊ ⌊probeHi⌋₊,
      proxyDifference I x S lo hi n * mellin n u / (n : ℂ)) =
    ∑ n ∈ Finset.Icc (max ⌈probeLo⌉₊ ⌈lo⌉₊) (min ⌊probeHi⌋₊ ⌊hi⌋₊),
      ((test I x n - proxy I x S n : ℝ) : ℂ) * mellin n u / (n : ℂ) := by
  calc
    _ = ∑ n ∈ Finset.Icc ⌈probeLo⌉₊ ⌊probeHi⌋₊,
        if lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi then
          ((test I x n - proxy I x S n : ℝ) : ℂ) * mellin n u / (n : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      simp only [proxyDifference]
      split_ifs <;> simp
    _ = _ := interval_restrict_sum _ _ lo hi hhi _

lemma tendsto_log_rpow_div_rpow (B a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => L x ^ B / x ^ a) atTop (nhds 0) :=
  (isLittleO_log_rpow_rpow_atTop B ha).tendsto_div_nhds_zero

theorem eventually_principal_error_bound (b B S : ℝ)
    (hb : 0 < b) (hB : 0 < B) (hS : 2 * B + 3 < S) :
    ∀ᶠ x : ℝ in atTop,
      2 * (1 + L x ^ B) * L x ^ (-S) * (1 + 2 * L x) +
        4 * L x ^ (-S) + 2 * Real.exp 1 / x ^ (b / 4) ≤ L x ^ (-B) := by
  have hpow : Tendsto (fun x : ℝ => L x ^ (2 * B + 1 - S)) atTop (nhds 0) := by
    have hneg : 0 < -(2 * B + 1 - S) := by linarith
    simpa only [neg_neg, Function.comp_def, L] using
      (tendsto_rpow_neg_atTop hneg).comp Real.tendsto_log_atTop
  have hsmall : ∀ᶠ x : ℝ in atTop,
      L x ^ (2 * B + 1 - S) ≤ (1 / 32 : ℝ) :=
    (hpow.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 32))).mono
      (fun _ h => h.le)
  have htail : ∀ᶠ x : ℝ in atTop,
      L x ^ B / x ^ (b / 4) ≤ 1 / (4 * Real.exp 1) :=
    ((tendsto_log_rpow_div_rpow B (b / 4) (by linarith)).eventually
      (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (4 * Real.exp 1)))).mono
        (fun _ h => h.le)
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hL, hsmall, htail] with x hx hLx hs ht
  have hLpos : 0 < L x := zero_lt_one.trans_le hLx
  have hxpos : 0 < x := by linarith
  have hLB : 1 ≤ L x ^ B := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hLx hB.le
  have hmain :
      2 * (1 + L x ^ B) * L x ^ (-S) * (1 + 2 * L x) + 4 * L x ^ (-S) ≤
        16 * L x ^ (B + 1 - S) := by
    have hwidth : L x ^ (-S) ≤ L x ^ (B + 1 - S) :=
      Real.rpow_le_rpow_of_exponent_le hLx (by linarith)
    have hfirst : 2 * (1 + L x ^ B) * L x ^ (-S) * (1 + 2 * L x) ≤
        12 * L x ^ (B + 1 - S) := by
      calc
        _ ≤ 2 * (2 * L x ^ B) * L x ^ (-S) * (3 * L x) := by
          gcongr <;> linarith
        _ = 12 * L x ^ (B + 1 - S) := by
          rw [show B + 1 - S = B + (-S) + 1 by ring,
            Real.rpow_add hLpos, Real.rpow_one, Real.rpow_add hLpos]
          ring
    linarith
  have hmain_half : 16 * L x ^ (B + 1 - S) ≤ L x ^ (-B) / 2 := by
    have hfactor : L x ^ (B + 1 - S) =
        L x ^ (2 * B + 1 - S) * L x ^ (-B) := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    rw [hfactor]
    nlinarith [mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hLpos.le (-B))]
  have htail_half : 2 * Real.exp 1 / x ^ (b / 4) ≤ L x ^ (-B) / 2 := by
    have hxpow : 0 < x ^ (b / 4) := Real.rpow_pos_of_pos hxpos _
    have hLpow : 0 < L x ^ B := Real.rpow_pos_of_pos hLpos _
    rw [Real.rpow_neg hLpos.le, inv_eq_one_div, div_div]
    have htailmul : 4 * Real.exp 1 * L x ^ B ≤ x ^ (b / 4) := by
      have := (div_le_div_iff₀ hxpow (by positivity : 0 < 4 * Real.exp 1)).mp ht
      nlinarith
    apply (div_le_div_iff₀ hxpow (by positivity : 0 < L x ^ B * 2)).mpr
    nlinarith
  linarith

/-- Every principal-character probe has the desired saving, conditional on positive cell counts. -/
theorem eventually_principal_discrepancy_given_denominator (b kappa B S : ℝ)
    (hb : 0 < b) (hB : 0 < B) (hS : 2 * B + 3 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : FactorTest) (lo hi : ℝ),
      TestAllowed b kappa I → x ^ (b / 4) ≤ lo → lo ≤ hi →
      (∀ n : ℕ, lo ≤ (n : ℝ) → (n : ℝ) ≤ hi → 0 < proxyDenominator x S n) →
      ∀ (probeLo probeHi u : ℝ) (r : ℕ),
        1 ≤ probeLo → probeLo ≤ probeHi → probeHi ≤ x ^ (2 : ℕ) →
        1 ≤ r → (r : ℝ) ≤ L x ^ B → |u| ≤ L x ^ B →
        ‖∑ n ∈ Finset.Icc ⌈probeLo⌉₊ ⌊probeHi⌋₊,
          proxyDifference I x S lo hi n * (1 : DirichletCharacter ℂ r) (n : ZMod r) *
            mellin n u / (n : ℂ)‖ ≤ L x ^ (-B) := by
  have hSpos : 0 < S := by linarith
  have hBS : B < S := by linarith
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hL,
    eventually_test_supported_on_cells b kappa S hb hSpos,
    eventually_principal_character_difference b kappa B S hb hB hSpos,
    eventually_mellin_small_argument B S hB hBS,
    eventually_principal_error_bound b B S hb hB hS] with x hx hLx hs hchar harg herr
  intro I lo hi hallowed hlo horder hden probeLo probeHi u r hpLo hpOrder hpHi hr hrB hu
  have hLpos : 0 < L x := zero_lt_one.trans_le hLx
  have hwidth : L x ^ (-S) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hLx (by linarith : -S ≤ 0)
  have hxpow : 0 < x ^ (b / 4) := Real.rpow_pos_of_pos (by linarith) _
  have hlo0 : 0 < lo := hxpow.trans_le hlo
  have hhi0 : 0 ≤ hi := (hlo0.trans_le horder).le
  have heq : ∀ n : ℕ,
      proxyDifference I x S lo hi n * (1 : DirichletCharacter ℂ r) (n : ZMod r) =
        proxyDifference I x S lo hi n := by
    intro n
    rw [mul_comm]
    exact hchar I lo hi r hallowed hlo (by omega) hrB n
  simp_rw [heq]
  rw [proxy_probe_sum_eq I x S lo hi probeLo probeHi u hhi0]
  let a := max ⌈probeLo⌉₊ ⌈lo⌉₊
  let z := min ⌊probeHi⌋₊ ⌊hi⌋₊
  change ‖∑ n ∈ Finset.Icc a z,
    ((test I x n - proxy I x S n : ℝ) : ℂ) * mellin n u / (n : ℂ)‖ ≤ L x ^ (-B)
  by_cases haz : a ≤ z
  · have ha : 0 < a := by
      have := Nat.one_le_ceil_iff.mpr hlo0
      have : ⌈lo⌉₊ ≤ a := le_max_right _ _
      omega
    have han : lo ≤ (a : ℝ) :=
      (Nat.le_ceil lo).trans (by exact_mod_cast (le_max_right ⌈probeLo⌉₊ ⌈lo⌉₊))
    have hzn : (z : ℝ) ≤ hi := by
      have hzceil : z ≤ ⌊hi⌋₊ := min_le_right _ _
      exact (Nat.le_floor_iff hhi0).mp hzceil
    have hprobe0 : 0 ≤ probeHi := by linarith
    have hzprobe : (z : ℝ) ≤ x ^ (2 : ℕ) := by
      have hzfloor : z ≤ ⌊probeHi⌋₊ := min_le_left _ _
      exact ((Nat.le_floor_iff hprobe0).mp hzfloor).trans hpHi
    have hrange : ∀ n ∈ Finset.Icc a z, lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi := by
      intro n hn
      rcases Finset.mem_Icc.mp hn with ⟨han', hnz⟩
      exact ⟨han.trans (by exact_mod_cast han'),
        (show (n : ℝ) ≤ (z : ℝ) by exact_mod_cast hnz).trans hzn⟩
    have hinterval := norm_proxy_interval_mellin_le I hx S u hwidth (harg u hu) ha haz
      (fun n hn => hden n (hrange n hn).1 (hrange n hn).2)
      (fun n hn => hs I n hallowed (hlo.trans (hrange n hn).1))
    have hmass := interval_harmonic_mass_le_probe hx ha hzprobe
    have hend : 2 * Real.exp 1 / (a : ℝ) ≤ 2 * Real.exp 1 / x ^ (b / 4) := by
      apply div_le_div_of_nonneg_left (by positivity) hxpow (hlo.trans han)
    have hcoeff : 2 * (1 + |u|) * L x ^ (-S) ≤
        2 * (1 + L x ^ B) * L x ^ (-S) := by
      gcongr
    have hmass0 := harmonic_mass_nonneg (Finset.Icc a z)
    have hcoeff0 : 0 ≤ 2 * (1 + L x ^ B) * L x ^ (-S) := by
      exact mul_nonneg (by positivity) (cell_width_pos hx S).le
    have hmain := mul_le_mul hcoeff hmass hmass0 hcoeff0
    exact (hinterval.trans (by linarith)).trans herr
  · rw [Finset.Icc_eq_empty_of_lt (Nat.lt_of_not_ge haz), Finset.sum_empty, norm_zero]
    exact Real.rpow_nonneg hLpos.le _

end Erdos821.P8Core

