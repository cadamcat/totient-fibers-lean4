import Erdos821.Blueprint.TypeII

noncomputable section
open Filter
open scoped BigOperators

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem tendsto_L : Tendsto L atTop atTop := Real.tendsto_log_atTop

theorem tendsto_T : Tendsto T atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_L

/-- The terminal scale forces O(T) bands. Its constant depends on the fixed
band data alone, before K₀ and every separation precision. -/
theorem band_count_bound (D : BandData) (hD : D.Valid) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ((D.last x + 1 : ℕ) : ℝ) ≤ C * T x := by
  obtain ⟨hr, hc1, hc12, hs, hratio, hsmall, hroom, hlast, cmin, cmax,
    hcmin, hcmax, hevent⟩ := hD
  have hlogratio : 0 < Real.log D.ratio := Real.log_pos hratio
  let C : ℝ := 2 / Real.log D.ratio + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hlarge : ∀ᶠ x : ℝ in atTop,
      max 1 (Real.log (D.s' / cmin)) ≤ T x :=
    tendsto_T.eventually (eventually_ge_atTop _)
  filter_upwards [hevent, hlarge, tendsto_L.eventually (eventually_ge_atTop 1)] with x hx hTx hL1
  have hT1 : 1 ≤ T x := (le_max_left _ _).trans hTx
  have hlogconst : Real.log (D.s' / cmin) ≤ T x := (le_max_right _ _).trans hTx
  have hL : 0 < L x := lt_of_lt_of_le zero_lt_one hL1
  have hscale : cmin * T x ≤ D.s' * L x / D.ratio ^ D.last x := hx.2.1
  have hpow : D.ratio ^ D.last x ≤ (D.s' / cmin) * L x := by
    have hbase := (le_div_iff₀ (pow_pos (by linarith : 0 < D.ratio) _)).mp hscale
    have hTc : cmin ≤ cmin * T x := by nlinarith
    calc
      D.ratio ^ D.last x ≤ (D.s' * L x) / cmin := by
        apply (le_div_iff₀ hcmin).mpr
        calc
          D.ratio ^ D.last x * cmin ≤ (cmin * T x) * D.ratio ^ D.last x := by
            simpa [mul_comm] using mul_le_mul_of_nonneg_right hTc
              (pow_pos (by linarith : 0 < D.ratio) (D.last x)).le
          _ ≤ D.s' * L x := hbase
      _ = (D.s' / cmin) * L x := by ring
  have hpowlog := Real.log_le_log (pow_pos (by linarith : 0 < D.ratio) _) hpow
  rw [Real.log_pow, Real.log_mul (by positivity : D.s' / cmin ≠ 0) hL.ne'] at hpowlog
  have hindex : (D.last x : ℝ) ≤ 2 * T x / Real.log D.ratio := by
    apply (le_div_iff₀ hlogratio).mpr
    change (D.last x : ℝ) * Real.log D.ratio ≤ _
    change (D.last x : ℝ) * Real.log D.ratio ≤ Real.log (D.s' / cmin) + T x at hpowlog
    linarith
  dsimp [C]
  push_cast
  calc
    (D.last x : ℝ) + 1 ≤ 2 * T x / Real.log D.ratio + T x := by linarith
    _ = _ := by ring


/-- A fixed cost per slot becomes a fixed power of L when there are O(T) slots. -/
theorem polylog_of_loglog_count (x C M : ℝ) (n : ℕ) (hL : 0 < L x)
    (hM : 1 ≤ M) (hn : (n : ℝ) ≤ C * T x) :
    M ^ n ≤ L x ^ (C * Real.log M) := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  calc
    M ^ n = Real.exp (Real.log M * (n : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hMpos]
    _ ≤ Real.exp (Real.log M * (C * T x)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hlogM)
    _ = L x ^ (C * Real.log M) := by
      rw [Real.rpow_def_of_pos hL]
      congr 1
      unfold T
      ring

theorem band_factorial_bound (D : BandData) (hD : D.Valid) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      (D.r₀.factorial : ℝ) ^ (D.last x + 1) ≤ L x ^ C := by
  obtain ⟨C, hC, hevent⟩ := band_count_bound D hD
  refine ⟨C * Real.log D.r₀.factorial, ?_⟩
  filter_upwards [hevent, tendsto_L.eventually (eventually_gt_atTop 0)] with x hx hL
  exact polylog_of_loglog_count x C D.r₀.factorial _ hL
    (by exact_mod_cast Nat.factorial_pos D.r₀) hx


end Erdos821.S56Core
