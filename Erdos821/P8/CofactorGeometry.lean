import Erdos821.P8.ProxyDenominator

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

def cellExponent (x S : ℝ) (m : ℕ) : ℝ := Real.log (logCellLower x S m) / L x

lemma rpow_cellExponent {x : ℝ} (hx : 1 < x) (S : ℝ) (m : ℕ) :
    x ^ cellExponent x S m = logCellLower x S m := by
  have hL0 : 0 < L x := Real.log_pos hx
  have hY0 : 0 < logCellLower x S m := Real.exp_pos _
  have heq : Real.log x * cellExponent x S m = Real.log (logCellLower x S m) := by
    unfold cellExponent
    change L x * (Real.log (logCellLower x S m) / L x) = _
    field_simp
  rw [Real.rpow_def_of_pos (by linarith : 0 < x), heq, Real.exp_log hY0]

lemma logCellLower_log_error {x : ℝ} (hx : 1 < x) (S : ℝ) {m : ℕ} (hm : 0 < m) :
    0 ≤ Real.log m - Real.log (logCellLower x S m) ∧
      Real.log m - Real.log (logCellLower x S m) ≤ L x ^ (-S) := by
  have hmem := (mem_logCellAt_iff _ _ m).mp (mem_assigned_logCell (cell_width_pos hx S) hm)
  unfold logCellLower
  rw [Real.log_exp]
  constructor <;> nlinarith [hmem.2.1, hmem.2.2]

lemma cellExponent_bounds {x : ℝ} (hx : 1 < x) (S : ℝ) {m : ℕ} (hm : 0 < m) :
    cellExponent x S m ≤ Real.log m / L x ∧
      Real.log m / L x ≤ cellExponent x S m + L x ^ (-S) / L x := by
  have hL0 : 0 < L x := Real.log_pos hx
  rcases logCellLower_log_error hx S hm with ⟨hlo, hhi⟩
  have hlow := div_le_div_of_nonneg_right (sub_nonneg.mp hlo) hL0.le
  have hhigh := div_le_div_of_nonneg_right hhi hL0.le
  rw [sub_div] at hhigh
  exact ⟨hlow, by dsimp [cellExponent]; linarith⟩

lemma cofactor_pos {m n u : ℕ} (hfactor : m * n = 2 * u + 1) : 0 < m ∧ 0 < n := by
  constructor
  · by_contra hm
    have hm0 : m = 0 := by omega
    rw [hm0, zero_mul] at hfactor
    omega
  · by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0, mul_zero] at hfactor
    omega

lemma cofactor_log_bounds {x : ℝ} (hx : 1 ≤ x) {m n u : ℕ}
    (hfactor : m * n = 2 * u + 1) (hulo : x ≤ (u : ℝ)) (huhi : (u : ℝ) ≤ 2 * x) :
    L x ≤ Real.log m + Real.log n ∧
      Real.log m + Real.log n ≤ L x + Real.log 5 := by
  have hx0 : 0 < x := by linarith
  rcases cofactor_pos hfactor with ⟨hm, hn⟩
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmul : (m : ℝ) * (n : ℝ) = 2 * (u : ℝ) + 1 := by exact_mod_cast hfactor
  have hlow := Real.log_le_log hx0 (show x ≤ (m : ℝ) * (n : ℝ) by linarith)
  have hhigh := Real.log_le_log (mul_pos hm0 hn0)
    (show (m : ℝ) * (n : ℝ) ≤ 5 * x by linarith)
  rw [Real.log_mul hm0.ne' hn0.ne'] at hlow hhigh
  rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hx0.ne'] at hhigh
  exact ⟨hlow, by dsimp [L]; linarith⟩

lemma cofactor_scaled_log_bounds {x : ℝ} (hx : 1 < x) {m n u : ℕ}
    (hfactor : m * n = 2 * u + 1) (hulo : x ≤ (u : ℝ)) (huhi : (u : ℝ) ≤ 2 * x) :
    1 - Real.log n / L x ≤ Real.log m / L x ∧
      Real.log m / L x ≤ 1 - Real.log n / L x + Real.log 5 / L x := by
  have hL0 : 0 < L x := Real.log_pos hx
  rcases cofactor_log_bounds hx.le hfactor hulo huhi with ⟨hlow, hhigh⟩
  have hlo := div_le_div_of_nonneg_right hlow hL0.le
  have hhi := div_le_div_of_nonneg_right hhigh hL0.le
  rw [add_div, div_self hL0.ne'] at hlo
  rw [add_div, add_div, div_self hL0.ne'] at hhi
  exact ⟨by linarith, by linarith⟩

/-- The cell cofactor exponent differs from the complementary exponent by O(1/log x). -/
lemma cofactor_cellExponent_near {x : ℝ} (hx : 1 < x) (S : ℝ)
    (hdelta : L x ^ (-S) ≤ 1) {m n u : ℕ}
    (hfactor : m * n = 2 * u + 1) (hulo : x ≤ (u : ℝ)) (huhi : (u : ℝ) ≤ 2 * x) :
    |cellExponent x S m - (1 - Real.log n / L x)| ≤ (Real.log 5 + 1) / L x := by
  have hL0 : 0 < L x := Real.log_pos hx
  have hlog5 : 0 ≤ Real.log 5 := (Real.log_pos (by norm_num : (1 : ℝ) < 5)).le
  have hlog5div : 0 ≤ Real.log 5 / L x := div_nonneg hlog5 hL0.le
  have hdeltaDiv := div_le_div_of_nonneg_right hdelta hL0.le
  rcases cellExponent_bounds hx S (cofactor_pos hfactor).1 with ⟨hcellLo, hcellHi⟩
  rcases cofactor_scaled_log_bounds hx hfactor hulo huhi with ⟨hlo, hhi⟩
  rw [add_div]
  exact abs_le.mpr ⟨by linarith, by linarith [one_div_pos.mpr hL0]⟩

/-- The source's cofactor hypotheses put every cell in the compact density and sieve ranges. -/
theorem eventually_cofactor_geometry (b kappa S gamma gamma' : ℝ)
    (hb : 0 < b) (hkappa : 0 < kappa) (hS : 0 < S)
    (hbgamma : b ≤ gamma) (horder : gamma < gamma') (hhi : gamma' ≤ 1 / 2 - kappa) :
    ∀ᶠ x : ℝ in atTop, ∀ m n u : ℕ,
      m * n = 2 * u + 1 → x ≤ (u : ℝ) → (u : ℝ) ≤ 2 * x →
      gamma < Real.log n / L x → Real.log n / L x ≤ gamma' →
      x ^ (b / 4) ≤ (m : ℝ) ∧ (m : ℝ) ≤ x ^ (1 - b / 4) ∧
      gamma + kappa ≤ cellExponent x S m ∧ cellExponent x S m ≤ 2 ∧
      |cellExponent x S m - (1 - Real.log n / L x)| ≤ (Real.log 5 + 1) / L x := by
  have ht : Tendsto (fun x : ℝ => (L x)⁻¹) atTop (nhds 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  have hinv : ∀ᶠ x : ℝ in atTop, 1 / L x ≤ kappa := by
    simpa only [one_div] using
      (ht.eventually (eventually_lt_nhds hkappa)).mono (fun _ h => h.le)
  have hlog5 : ∀ᶠ x : ℝ in atTop, Real.log 5 / L x ≤ min 1 (b / 2) := by
    have hsmall := (ht.const_mul (Real.log 5)).eventually
      (eventually_lt_nhds (show Real.log 5 * 0 < min 1 (b / 2) by simp; positivity))
    simpa only [div_eq_mul_inv] using hsmall.mono (fun _ h => h.le)
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ L x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hL, hinv, hlog5] with x hx hLx hinvX hlog5X
  intro m n u hfactor hulo huhi haLo haHi
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L x := zero_lt_one.trans_le hLx
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (cofactor_pos hfactor).1
  have hdelta : L x ^ (-S) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hLx (by linarith)
  have hdeltaDiv := div_le_div_of_nonneg_right hdelta hL0.le
  have hlog5One : Real.log 5 / L x ≤ 1 := hlog5X.trans (min_le_left _ _)
  have hlog5b : Real.log 5 / L x ≤ b / 2 := hlog5X.trans (min_le_right _ _)
  rcases cofactor_scaled_log_bounds hx hfactor hulo huhi with ⟨hlo, hupper⟩
  rcases cellExponent_bounds hx S (cofactor_pos hfactor).1 with ⟨hcellLo, hcellHi⟩
  have hmlower : b / 4 ≤ Real.log m / L x := by linarith
  have hmupper : Real.log m / L x ≤ 1 - b / 4 := by linarith
  have hmloglo : b / 4 * L x ≤ Real.log m := (le_div_iff₀ hL0).mp hmlower
  have hmloghi : Real.log m ≤ (1 - b / 4) * L x := (div_le_iff₀ hL0).mp hmupper
  refine ⟨?_, ?_, ?_, ?_, cofactor_cellExponent_near hx S hdelta hfactor hulo huhi⟩
  · calc
      x ^ (b / 4) = Real.exp (b / 4 * L x) := by
        rw [Real.rpow_def_of_pos hx0]
        congr 1
        dsimp [L]
        ring
      _ ≤ Real.exp (Real.log m) := Real.exp_le_exp.mpr hmloglo
      _ = (m : ℝ) := Real.exp_log hm0
  · calc
      (m : ℝ) = Real.exp (Real.log m) := (Real.exp_log hm0).symm
      _ ≤ Real.exp ((1 - b / 4) * L x) := Real.exp_le_exp.mpr hmloghi
      _ = x ^ (1 - b / 4) := by
        rw [Real.rpow_def_of_pos hx0]
        congr 1
        dsimp [L]
        ring
  · linarith
  · linarith

end Erdos821.P8Core

