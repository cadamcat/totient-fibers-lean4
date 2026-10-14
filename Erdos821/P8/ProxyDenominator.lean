import Erdos821.P8.PrincipalDiscrepancy
import Erdos821.P8.ProxyTasks
import Erdos821.P8.SieveProducts

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

def logCellLower (x S : ℝ) (n : ℕ) : ℝ :=
  Real.exp ((logIndex (L x ^ (-S)) n : ℝ) * L x ^ (-S))

def logCellUpper (x S : ℝ) (n : ℕ) : ℝ :=
  Real.exp (((logIndex (L x ^ (-S)) n : ℝ) + 1) * L x ^ (-S))

lemma logCell_eq_endpoints (x S : ℝ) (n : ℕ) :
    logCell x S n = Finset.Ioc ⌊logCellLower x S n⌋₊ ⌊logCellUpper x S n⌋₊ := rfl

lemma logCell_endpoint_relation (x S : ℝ) (n : ℕ) :
    logCellUpper x S n = logCellLower x S n * Real.exp (L x ^ (-S)) := by
  unfold logCellUpper logCellLower
  rw [add_mul, one_mul, Real.exp_add]

lemma logCell_length_lower {x : ℝ} (_hx : 1 < x) (S : ℝ) (n : ℕ) :
    logCellLower x S n * L x ^ (-S) ≤ logCellUpper x S n - logCellLower x S n := by
  rw [logCell_endpoint_relation]
  have he := Real.add_one_le_exp (L x ^ (-S))
  have hy : 0 < logCellLower x S n := Real.exp_pos _
  nlinarith

theorem eventually_logCell_endpoint_bounds (b S : ℝ) (hb : 0 < b) (hS : 0 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,
      x ^ (b / 4) ≤ (n : ℝ) → (n : ℝ) ≤ x ^ (1 - b / 4) →
      x ^ (b / 8) ≤ logCellLower x S n ∧
        logCellLower x S n ≤ logCellUpper x S n ∧ logCellUpper x S n ≤ x ^ (2 : ℝ) := by
  have hL : ∀ᶠ x : ℝ in atTop, max 1 (8 / b) ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hL] with x hx hLx
  intro n hnlo hnhi
  have hx0 : 0 < x := by linarith
  have hn0 : 0 < (n : ℝ) := (Real.rpow_pos_of_pos hx0 (b / 4)).trans_le hnlo
  have hn : 0 < n := by exact_mod_cast hn0
  have hL1 : 1 ≤ L x := (le_max_left _ _).trans hLx
  have hLb : 8 / b ≤ L x := (le_max_right _ _).trans hLx
  have hwidth : L x ^ (-S) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hmem := (mem_logCellAt_iff (L x ^ (-S)) (logIndex (L x ^ (-S)) n) n).mp
    (mem_assigned_logCell (cell_width_pos hx S) hn)
  have hloglo : b / 4 * L x ≤ Real.log n := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hx0 (b / 4)) hnlo
    simpa only [Real.log_rpow hx0, L, mul_comm] using h
  have hloghi : Real.log n ≤ (1 - b / 4) * L x := by
    have h := Real.log_le_log hn0 hnhi
    simpa only [Real.log_rpow hx0, L, mul_comm] using h
  have hbL : 1 ≤ b / 8 * L x := by
    have := (div_le_iff₀ hb).mp hLb
    nlinarith
  constructor
  · rw [logCellLower, Real.rpow_def_of_pos hx0, Real.exp_le_exp]
    simp only [L] at hloglo hbL hwidth hmem ⊢
    nlinarith [hmem.2.2]
  constructor
  · rw [logCellUpper, logCellLower, Real.exp_le_exp]
    nlinarith [cell_width_pos hx S]
  · rw [logCellUpper, Real.rpow_def_of_pos hx0, Real.exp_le_exp]
    simp only [L] at hloghi hwidth hmem hL1 ⊢
    nlinarith [hmem.2.1]

lemma tendsto_W_atTop : Tendsto W atTop atTop :=
  Real.tendsto_exp_atTop.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)

/-- A weaker logarithmic lower bound is enough for positive cell counts. -/
theorem eventually_sieveProduct_W_lower (hc : ClassicalInputs) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-Real.eulerMascheroniConstant) / (2 * L x) ≤ sieveProduct (W x) := by
  let c := Real.exp (-Real.eulerMascheroniConstant)
  have hcpos : 0 < c := Real.exp_pos _
  have ht := hc.mertens.2.comp tendsto_W_atTop
  have hlower : ∀ᶠ x : ℝ in atTop, c / 2 ≤ Real.log (W x) * sieveProduct (W x) :=
    (ht.eventually (eventually_gt_nhds (by dsimp [c]; linarith [hcpos] : c / 2 < c))).mono
      (fun _ h => h.le)
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hL, hlower] with x hLx hlow
  have hLpos : 0 < L x := zero_lt_one.trans_le hLx
  have hsqrt : Real.sqrt (L x) ≤ L x := Real.sqrt_le_self_iff.mpr (Or.inr hLx)
  have hsieve : 0 ≤ sieveProduct (W x) := (sieveProduct_pos _).le
  have hprod : c / 2 ≤ L x * sieveProduct (W x) := by
    rw [W, Real.log_exp] at hlow
    exact hlow.trans (mul_le_mul_of_nonneg_right hsqrt hsieve)
  apply (div_le_iff₀ (by positivity : 0 < 2 * L x)).mpr
  dsimp only [c] at hprod
  nlinarith

theorem eventually_denominator_main_lower (hc : ClassicalInputs) (b S : ℝ)
    (hb : 0 < b) (hS : 0 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,
      x ^ (b / 4) ≤ (n : ℝ) → (n : ℝ) ≤ x ^ (1 - b / 4) →
      4 * x ^ (b / 16) ≤
        (logCellUpper x S n - logCellLower x S n) * sieveProduct (W x) := by
  let c := Real.exp (-Real.eulerMascheroniConstant)
  have hcpos : 0 < c := Real.exp_pos _
  have hratio : ∀ᶠ x : ℝ in atTop, L x ^ (S + 1) / x ^ (b / 16) ≤ c / 8 :=
    ((tendsto_log_rpow_div_rpow (S + 1) (b / 16) (by linarith)).eventually
      (eventually_lt_nhds (by positivity : (0 : ℝ) < c / 8))).mono (fun _ h => h.le)
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hL, hratio,
    eventually_logCell_endpoint_bounds b S hb hS, eventually_sieveProduct_W_lower hc]
    with x hx hLx hr hcells hsieve
  intro n hnlo hnhi
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L x := zero_lt_one.trans_le hLx
  have hxeta : 0 < x ^ (b / 16) := Real.rpow_pos_of_pos hx0 _
  have hLP : 0 < L x ^ (S + 1) := Real.rpow_pos_of_pos hL0 _
  have hLS : 0 < L x ^ S := Real.rpow_pos_of_pos hL0 _
  have hratio' : 8 * L x ^ (S + 1) ≤ c * x ^ (b / 16) := by
    have := (div_le_div_iff₀ hxeta (by norm_num : (0 : ℝ) < 8)).mp hr
    nlinarith
  have hxpow : x ^ (b / 16) * x ^ (b / 16) = x ^ (b / 8) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hratio_mul := mul_le_mul_of_nonneg_right hratio' hxeta.le
  have hpoly : 4 * x ^ (b / 16) ≤
      x ^ (b / 8) * L x ^ (-S) * (c / (2 * L x)) := by
    have heq : x ^ (b / 8) * L x ^ (-S) * (c / (2 * L x)) =
        x ^ (b / 8) * c / (2 * L x ^ (S + 1)) := by
      rw [Real.rpow_neg hL0.le, Real.rpow_add_one hL0.ne']
      field_simp
    rw [heq]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L x ^ (S + 1))).mpr
    have hmul : 8 * L x ^ (S + 1) * x ^ (b / 16) ≤ c * x ^ (b / 8) := by
      simpa only [mul_assoc, hxpow] using hratio_mul
    nlinarith
  have hY : x ^ (b / 8) ≤ logCellLower x S n := (hcells n hnlo hnhi).1
  have hdelta : 0 < L x ^ (-S) := cell_width_pos hx S
  have hYdelta := mul_le_mul_of_nonneg_right hY hdelta.le
  have hV : c / (2 * L x) ≤ sieveProduct (W x) := hsieve
  have hV0 : 0 ≤ sieveProduct (W x) := (sieveProduct_pos _).le
  calc
    4 * x ^ (b / 16) ≤ x ^ (b / 8) * L x ^ (-S) * (c / (2 * L x)) := hpoly
    _ ≤ logCellLower x S n * L x ^ (-S) * sieveProduct (W x) :=
      mul_le_mul hYdelta hV (by positivity) (by unfold logCellLower; positivity)
    _ ≤ (logCellUpper x S n - logCellLower x S n) * sieveProduct (W x) :=
      mul_le_mul_of_nonneg_right (logCell_length_lower hx S n) hV0

/-- The r=1 residue estimate gives positivity throughout the ambient range. -/
theorem eventually_proxyDenominator_pos (hc : ClassicalInputs) (hs : SieveInputs)
    (hresidue : RoughResidueIntervalTask) (b S : ℝ) (hb : 0 < b) (hS : 0 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,
      x ^ (b / 4) ≤ (n : ℝ) → (n : ℝ) ≤ x ^ (1 - b / 4) →
      0 < proxyDenominator x S n := by
  have hcounts := hresidue hc hs (b / 8) 2 1 1 (b / 16)
    (by linarith) (by norm_num) (by norm_num) (by norm_num) (by linarith)
  have hL : ∀ᶠ x : ℝ in atTop, 4 ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hL, hcounts,
    eventually_logCell_endpoint_bounds b S hb hS,
    eventually_denominator_main_lower hc b S hb hS] with x hx hLx hcount hcells hmain
  intro n hnlo hnhi
  rcases hcells n hnlo hnhi with ⟨hY, hYZ, hZ⟩
  have hq : L x ^ (-1 : ℝ) ≤ (1 / 4 : ℝ) := by
    rw [Real.rpow_neg_one]
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 4) hLx
  have herr := hcount (logCellLower x S n) (logCellUpper x S n) 1 0 hY hYZ hZ
    (by norm_num) (by simpa only [Nat.cast_one, Real.rpow_one] using (by linarith : 1 ≤ L x))
    (by simp)
  let M := (logCellUpper x S n - logCellLower x S n) * sieveProduct (W x)
  have herr' : |(proxyDenominator x S n : ℝ) - M| ≤ M * L x ^ (-1 : ℝ) + x ^ (b / 16) := by
    simpa only [proxyDenominator, logCell_eq_endpoints, Nat.mod_one, Nat.totient_one,
      Nat.cast_one, div_one, and_true, M] using herr
  have hmain' : 4 * x ^ (b / 16) ≤ M := hmain n hnlo hnhi
  have hxeta : 0 < x ^ (b / 16) := Real.rpow_pos_of_pos (by linarith) _
  have hM : 0 < M := by linarith
  have hqM := mul_le_mul_of_nonneg_left hq hM.le
  have hN : (0 : ℝ) < proxyDenominator x S n := by
    have hlow := (abs_le.mp herr').1
    linarith
  exact_mod_cast hN

theorem eventually_proxy_bounds_from_residue (hc : ClassicalInputs) (hs : SieveInputs)
    (hresidue : RoughResidueIntervalTask) (b kappa S : ℝ) (hb : 0 < b) (hS : 0 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : FactorTest) (n : ℕ), TestAllowed b kappa I →
      x ^ (b / 4) ≤ (n : ℝ) → (n : ℝ) ≤ x ^ (1 - b / 4) →
      0 < proxyDenominator x S n ∧
      0 ≤ proxyConstant I x S n ∧ proxyConstant I x S n ≤ 1 ∧
      0 ≤ proxy I x S n ∧ proxy I x S n ≤ 1 := by
  filter_upwards [eventually_proxyDenominator_pos hc hs hresidue b S hb hS,
    eventually_proxy_bounds_given_denominator b kappa S hb hS] with x hden hbounds
  intro I n hallowed hnlo hnhi
  have hn := hden n hnlo hnhi
  exact ⟨hn, hbounds I n hallowed hnlo hn⟩

theorem eventually_principal_discrepancy_from_residue (hc : ClassicalInputs) (hs : SieveInputs)
    (hresidue : RoughResidueIntervalTask) (b kappa B S : ℝ)
    (hb : 0 < b) (hB : 0 < B) (hS : 2 * B + 3 < S) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : FactorTest) (lo hi : ℝ),
      TestAllowed b kappa I → x ^ (b / 4) ≤ lo → lo ≤ hi → hi ≤ x ^ (1 - b / 4) →
      ∀ (probeLo probeHi u : ℝ) (r : ℕ),
        1 ≤ probeLo → probeLo ≤ probeHi → probeHi ≤ x ^ (2 : ℕ) →
        1 ≤ r → (r : ℝ) ≤ L x ^ B → |u| ≤ L x ^ B →
        ‖∑ n ∈ Finset.Icc ⌈probeLo⌉₊ ⌊probeHi⌋₊,
          proxyDifference I x S lo hi n * (1 : DirichletCharacter ℂ r) (n : ZMod r) *
            mellin n u / (n : ℂ)‖ ≤ L x ^ (-B) := by
  have hSpos : 0 < S := by linarith
  filter_upwards [eventually_proxyDenominator_pos hc hs hresidue b S hb hSpos,
    eventually_principal_discrepancy_given_denominator b kappa B S hb hB hS]
    with x hden hprincipal
  intro I lo hi hallowed hlo horder hhi
  apply hprincipal I lo hi hallowed hlo horder
  intro n hnlo hnhi
  exact hden n (hlo.trans hnlo) (hnhi.trans hhi)

end Erdos821.P8Core

