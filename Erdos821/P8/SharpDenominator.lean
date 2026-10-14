import Erdos821.P8.ProxyDenominator

noncomputable section
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

/-- The absolute sieve error is negligible relative to every ambient cell main term. -/
theorem eventually_proxyDenominator_relative_lower (hc : ClassicalInputs) (hs : SieveInputs)
    (hresidue : RoughResidueIntervalTask) (b S eps : ℝ)
    (hb : 0 < b) (hS : 0 < S) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,
      x ^ (b / 4) ≤ (n : ℝ) → (n : ℝ) ≤ x ^ (1 - b / 4) →
      (1 - eps) * (logCellUpper x S n - logCellLower x S n) * sieveProduct (W x) ≤
        (proxyDenominator x S n : ℝ) := by
  have hcounts := hresidue hc hs (b / 8) 2 1 1 (b / 32)
    (by linarith) (by norm_num) (by norm_num) (by norm_num) (by linarith)
  have hq : ∀ᶠ x : ℝ in atTop, L x ^ (-1 : ℝ) ≤ eps / 2 :=
    (((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp
      Real.tendsto_log_atTop).eventually
        (eventually_lt_nhds (by linarith : (0 : ℝ) < eps / 2))).mono (fun _ h => h.le)
  have hpower : ∀ᶠ x : ℝ in atTop, x ^ (-(b / 32)) ≤ 2 * eps :=
    ((tendsto_rpow_neg_atTop (by linarith : 0 < b / 32)).eventually
      (eventually_lt_nhds (by linarith : (0 : ℝ) < 2 * eps))).mono (fun _ h => h.le)
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hL, hcounts, hq, hpower,
    eventually_logCell_endpoint_bounds b S hb hS,
    eventually_denominator_main_lower hc b S hb hS]
    with x hx hLx hcount hqx hpx hcells hmain
  intro n hnlo hnhi
  rcases hcells n hnlo hnhi with ⟨hY, hYZ, hZ⟩
  have hx0 : 0 < x := by linarith
  have herr := hcount (logCellLower x S n) (logCellUpper x S n) 1 0 hY hYZ hZ
    (by norm_num) (by simpa only [Nat.cast_one, Real.rpow_one] using hLx) (by simp)
  let M := (logCellUpper x S n - logCellLower x S n) * sieveProduct (W x)
  have herr' : |(proxyDenominator x S n : ℝ) - M| ≤
      M * L x ^ (-1 : ℝ) + x ^ (b / 32) := by
    simpa only [proxyDenominator, logCell_eq_endpoints, Nat.mod_one, Nat.totient_one,
      Nat.cast_one, div_one, and_true, M] using herr
  have hmain' : 4 * x ^ (b / 16) ≤ M := hmain n hnlo hnhi
  have hp16 : 0 < x ^ (b / 16) := Real.rpow_pos_of_pos hx0 _
  have hM : 0 < M := by linarith
  have hpower_eq : x ^ (-(b / 32)) * x ^ (b / 16) = x ^ (b / 32) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hsmall : x ^ (b / 32) ≤ 2 * eps * x ^ (b / 16) := by
    simpa only [hpower_eq] using mul_le_mul_of_nonneg_right hpx hp16.le
  have habsolute : x ^ (b / 32) ≤ eps / 2 * M := by
    have := mul_le_mul_of_nonneg_left hmain' (by linarith : 0 ≤ eps / 2)
    nlinarith
  have hrelative := mul_le_mul_of_nonneg_left hqx hM.le
  have hlower := (abs_le.mp herr').1
  change (1 - eps) * (logCellUpper x S n - logCellLower x S n) *
    sieveProduct (W x) ≤ _
  change -(M * L x ^ (-1 : ℝ) + x ^ (b / 32)) ≤
    (proxyDenominator x S n : ℝ) - M at hlower
  dsimp only [M] at hrelative habsolute hlower
  nlinarith

/-- A sharp denominator lower bound in the normalization used by density cell counts. -/
theorem eventually_proxyDenominator_sharp_lower (hc : ClassicalInputs) (hs : SieveInputs)
    (hresidue : RoughResidueIntervalTask) (b S eps : ℝ)
    (hb : 0 < b) (hS : 0 < S) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,
      x ^ (b / 4) ≤ (n : ℝ) → (n : ℝ) ≤ x ^ (1 - b / 4) →
      (1 - eps) * L x ^ (-S) * logCellLower x S n * sieveProduct (W x) ≤
        (proxyDenominator x S n : ℝ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_proxyDenominator_relative_lower hc hs hresidue b S eps hb hS heps]
    with x hx hlower
  intro n hnlo hnhi
  by_cases heps1 : eps ≤ 1
  · have hlength := mul_le_mul_of_nonneg_right
      (logCell_length_lower hx S n) (sieveProduct_pos (W x)).le
    have hscaled := mul_le_mul_of_nonneg_left hlength (by linarith : 0 ≤ 1 - eps)
    calc
      (1 - eps) * L x ^ (-S) * logCellLower x S n * sieveProduct (W x) =
          (1 - eps) * (logCellLower x S n * L x ^ (-S) * sieveProduct (W x)) := by ring
      _ ≤ (1 - eps) * ((logCellUpper x S n - logCellLower x S n) *
          sieveProduct (W x)) := hscaled
      _ = (1 - eps) * (logCellUpper x S n - logCellLower x S n) *
          sieveProduct (W x) := by ring
      _ ≤ (proxyDenominator x S n : ℝ) := hlower n hnlo hnhi
  · have hdelta := (cell_width_pos hx S).le
    have hY := (Real.exp_pos ((logIndex (L x ^ (-S)) n : ℝ) * L x ^ (-S))).le
    have hV := (sieveProduct_pos (W x)).le
    have hnonpos : (1 - eps) * L x ^ (-S) * logCellLower x S n *
        sieveProduct (W x) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) hdelta) hY) hV
    exact hnonpos.trans (Nat.cast_nonneg _)

end Erdos821.P8Core

