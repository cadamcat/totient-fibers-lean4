import Erdos821.Blueprint.Candidate

noncomputable section
open scoped ContDiff

namespace Erdos821.P7Core

/-- The fixed choices made before selecting any rough-slot index. -/
structure EarlyParameters (δ : ℝ) where
  r₀ : ℕ
  s' : ℝ
  prefixLen : ℕ
  micro : ℕ
  j₀ : ℕ
  theta : ℝ
  r₀_large : 6 ≤ r₀
  s'_eq : s' = 1 / ((r₀ : ℝ) * (1 + 6 / 5))
  s'_pos : 0 < s'
  smoothness_margin : (6 / 5 : ℝ) * s' < δ
  band_room : ((r₀ : ℝ) - 1) / 2 ≥ 6 / 5 + 1
  prefix_before : prefixLen < j₀
  prefix_tail : 2 * r₀ * (6 / 5 : ℝ) * s' / 2 ^ (prefixLen + 1) <
    ((6 / 5 : ℝ) - 1) * s' / 24
  micro_before : micro ≤ j₀
  micro_lower : (6 / 5 : ℝ) * s' / 2 ^ micro < theta
  micro_upper : theta < 2 * s' / 2 ^ micro
  theta_small : 10 * theta ≤ 1 / 20
  micro_tail : 2 * r₀ * (6 / 5 : ℝ) * s' / 2 ^ micro ≤ 1 / 25

theorem earlyParameters_nonempty (δ : ℝ) (hδ : 0 < δ) :
    Nonempty (EarlyParameters δ) := by
  obtain ⟨r, hr⟩ := exists_nat_gt (max (6 : ℝ) δ⁻¹)
  have hr6 : 6 < (r : ℝ) := (le_max_left _ _).trans_lt hr
  have hrδ : δ⁻¹ < (r : ℝ) := (le_max_right _ _).trans_lt hr
  have hr0 : 0 < (r : ℝ) := by linarith
  have hrδ' : 1 < δ * r := by
    have := mul_lt_mul_of_pos_left hrδ hδ
    simpa only [mul_inv_cancel₀ hδ.ne'] using this
  let s : ℝ := 1 / ((r : ℝ) * (1 + 6 / 5))
  have hs : 0 < s := by dsimp [s]; positivity
  have hseq : s * ((r : ℝ) * (1 + 6 / 5)) = 1 := by
    dsimp [s]
    field_simp
  have hsm : (6 / 5 : ℝ) * s < δ := by
    dsimp [s]
    rw [← mul_div_assoc, mul_one, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨p, hp⟩ := pow_unbounded_of_one_lt (288 * (r : ℝ))
    (show (1 : ℝ) < 2 by norm_num)
  have hp0 : (0 : ℝ) < 2 ^ p := by positivity
  have hp1 : (288 : ℝ) * r < 2 ^ (p + 1) := by
    rw [pow_succ]
    linarith
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (max (320 * s) (60 * r * s))
    (show (1 : ℝ) < 2 by norm_num)
  have hm0 : (0 : ℝ) < 2 ^ m := by positivity
  have hmθ : 320 * s < (2 : ℝ) ^ m := (le_max_left _ _).trans_lt hm
  have hmt : 60 * r * s < (2 : ℝ) ^ m := (le_max_right _ _).trans_lt hm
  let θ : ℝ := (8 / 5 : ℝ) * s / 2 ^ m
  refine ⟨{
    r₀ := r, s' := s, prefixLen := p, micro := m,
    j₀ := max p m + 1, theta := θ,
    r₀_large := ?_, s'_eq := rfl, s'_pos := hs,
    smoothness_margin := hsm, band_room := ?_,
    prefix_before := ?_, prefix_tail := ?_, micro_before := ?_,
    micro_lower := ?_, micro_upper := ?_, theta_small := ?_, micro_tail := ?_ }⟩
  · exact_mod_cast hr6.le
  · linarith
  · omega
  · rw [div_lt_iff₀ (by positivity)]
    have := mul_lt_mul_of_pos_left hp1 hs
    nlinarith
  · omega
  · dsimp [θ]
    apply (div_lt_div_iff_of_pos_right hm0).mpr
    nlinarith
  · dsimp [θ]
    apply (div_lt_div_iff_of_pos_right hm0).mpr
    nlinarith
  · dsimp [θ]
    rw [← mul_div_assoc, div_le_iff₀ hm0]
    linarith
  · rw [div_le_iff₀ hm0]
    linarith

/-- A smooth cutoff supported in `[1,2]`, equal to one on `[5/4,7/4]`. -/
def candidateBump : ContDiffBump (3 / 2 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem candidateBump_properties :
    ContDiff ℝ ∞ (candidateBump : ℝ → ℝ) ∧
    Function.support (candidateBump : ℝ → ℝ) ⊆ Set.Icc 1 2 ∧
    (∀ y : ℝ, 0 ≤ candidateBump y) ∧
    (∃ a b c : ℝ, 1 < a ∧ a < b ∧ b < 2 ∧ 0 < c ∧
      ∀ y ∈ Set.Icc a b, c ≤ candidateBump y) := by
  refine ⟨candidateBump.contDiff, ?_, candidateBump.nonneg', ?_⟩
  · rw [candidateBump.support_eq]
    intro y hy
    have hy' : |y - 3 / 2| < 1 / 2 := by
      simpa [candidateBump, Real.dist_eq] using hy
    exact ⟨by linarith [(abs_lt.mp hy').1], by linarith [(abs_lt.mp hy').2]⟩
  · refine ⟨5 / 4, 7 / 4, 1, by norm_num, by norm_num, by norm_num,
      by norm_num, ?_⟩
    intro y hy
    have hball : y ∈ Metric.closedBall (3 / 2 : ℝ) candidateBump.rIn := by
      simp only [Metric.mem_closedBall, Real.dist_eq, candidateBump]
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]
    rw [candidateBump.one_of_mem_closedBall hball]

end Erdos821.P7Core

