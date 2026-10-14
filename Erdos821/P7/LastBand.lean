import Erdos821.Blueprint.Candidate

noncomputable section
open Filter
open scoped Topology

namespace Erdos821.P7Core
open Erdos821.Blueprint.Analytic

def terminalRatio (s x : ℝ) : ℝ := s * L x / (20 * T x)

/-- Choose the last dyadic scale still above `20 log log x`. -/
def lastBand (s x : ℝ) : ℕ :=
  if h : 1 ≤ terminalRatio s x then
    (exists_nat_pow_near h (show (1 : ℝ) < 2 by norm_num)).choose
  else 0

theorem lastBand_pow_bounds (s x : ℝ) (h : 1 ≤ terminalRatio s x) :
    (2 : ℝ) ^ lastBand s x ≤ terminalRatio s x ∧
      terminalRatio s x < (2 : ℝ) ^ (lastBand s x + 1) := by
  simp only [lastBand, dite_eq_left h]
  exact (exists_nat_pow_near h (show (1 : ℝ) < 2 by norm_num)).choose_spec

theorem terminalRatio_tendsto (s : ℝ) (hs : 0 < s) :
    Tendsto (terminalRatio s) atTop atTop := by
  have ht₀ : Tendsto (fun x : ℝ => T x / L x) atTop (nhds 0) := by
    simpa [T, L, Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        Real.tendsto_log_atTop
  have ht : Tendsto (fun x : ℝ => 20 / s * (T x / L x)) atTop (nhds 0) := by
    simpa using ht₀.const_mul (20 / s)
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < 20 / s * (T x / L x) := by
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 1] with x hx
    have hL : 0 < L x := by dsimp [L]; linarith
    have hT : 0 < T x := Real.log_pos hx
    positivity
  have hinv := tendsto_inv_nhdsGT_zero.comp
    (tendsto_nhdsWithin_iff.mpr ⟨ht, hpos⟩)
  convert hinv using 1
  ext x
  simp [terminalRatio, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm,
    mul_assoc]

theorem lastBand_tendsto (s : ℝ) (hs : 0 < s) :
    Tendsto (lastBand s) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [(terminalRatio_tendsto s hs).eventually_ge_atTop
    ((2 : ℝ) ^ n)] with x hx
  have h1 : 1 ≤ terminalRatio s x :=
    (one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)).trans hx
  have hpow := (lastBand_pow_bounds s x h1).2
  have hlt : (2 : ℝ) ^ n < 2 ^ (lastBand s x + 1) := hx.trans_lt hpow
  have hindex : n < lastBand s x + 1 :=
    (pow_lt_pow_iff_right₀ (show (1 : ℝ) < 2 by norm_num)).mp hlt
  omega

theorem lastBand_scale_bounds (s : ℝ) (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop,
      20 * T x ≤ s * L x / 2 ^ lastBand s x ∧
      s * L x / 2 ^ (lastBand s x + 1) < 20 * T x ∧
      s * L x / 2 ^ lastBand s x < 40 * T x := by
  filter_upwards [(terminalRatio_tendsto s hs).eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_gt_atTop 1] with x hx hL
  have hT : 0 < T x := Real.log_pos hL
  obtain ⟨hlo, hhi⟩ := lastBand_pow_bounds s x hx
  have hlo' : 2 ^ lastBand s x * (20 * T x) ≤ s * L x := by
    exact (le_div_iff₀ (by positivity)).mp hlo
  have hhi' : s * L x < 2 ^ (lastBand s x + 1) * (20 * T x) := by
    exact (div_lt_iff₀ (by positivity)).mp hhi
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_lt_iff₀ (by positivity)]
    simpa only [mul_comm] using hhi'
  · rw [div_lt_iff₀ (by positivity)]
    rw [pow_succ] at hhi'
    nlinarith

end Erdos821.P7Core

