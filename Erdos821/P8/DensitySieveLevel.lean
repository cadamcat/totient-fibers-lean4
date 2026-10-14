import Erdos821.Blueprint.Proxy

noncomputable section
open Filter

namespace Erdos821.P8Core

def dyadicSieveLevel (b : ℝ) : ℕ := 2 * ⌊(1 : ℝ) / (40 * b)⌋₊

/-- A fixed even sieve level gives exponential saving while keeping the remainder sublinear. -/
theorem dyadicSieveLevel_bounds (h0 : ℕ) {b : ℝ} (hb : 0 < b)
    (hsmall : b < min (1 / 100 : ℝ) (1 / (40 * ((h0 : ℝ) + 2)))) :
    h0 ≤ dyadicSieveLevel b ∧ Even (dyadicSieveLevel b) ∧
      b * ((4 * dyadicSieveLevel b + 2 : ℕ) : ℝ) ≤ 1 / 4 ∧
      1 / (20 * b) - 2 ≤ (dyadicSieveLevel b : ℝ) := by
  have hb100 : b < 1 / 100 := hsmall.trans_le (min_le_left _ _)
  have hbH : b < 1 / (40 * ((h0 : ℝ) + 2)) := hsmall.trans_le (min_le_right _ _)
  have hqpos : 0 ≤ (1 : ℝ) / (40 * b) := by positivity
  have hfloorLo := Nat.lt_floor_add_one ((1 : ℝ) / (40 * b))
  have hfloorHi := Nat.floor_le hqpos
  have hqH : (h0 : ℝ) + 2 < 1 / (40 * b) := by
    apply (lt_div_iff₀ (by positivity : 0 < 40 * b)).mpr
    have hmul := (lt_div_iff₀ (by positivity : 0 < 40 * ((h0 : ℝ) + 2))).mp hbH
    nlinarith
  have h0floor : h0 ≤ ⌊(1 : ℝ) / (40 * b)⌋₊ := by
    have hcast : (h0 : ℝ) ≤ (⌊(1 : ℝ) / (40 * b)⌋₊ : ℝ) := by linarith
    exact_mod_cast hcast
  have hlevel : (dyadicSieveLevel b : ℝ) = 2 * (⌊(1 : ℝ) / (40 * b)⌋₊ : ℝ) := by
    simp [dyadicSieveLevel]
  have hqmul : ((1 : ℝ) / (40 * b)) * b = 1 / 40 := by field_simp
  have hqtwice : 2 * ((1 : ℝ) / (40 * b)) = 1 / (20 * b) := by field_simp; norm_num
  refine ⟨h0floor.trans (by unfold dyadicSieveLevel; omega), ?_, ?_, ?_⟩
  · exact ⟨⌊(1 : ℝ) / (40 * b)⌋₊, by unfold dyadicSieveLevel; ring⟩
  · have hmul := mul_le_mul_of_nonneg_left hfloorHi hb.le
    push_cast
    nlinarith
  · linarith

lemma dyadicSieveLevel_exp_upper (h0 : ℕ) {b : ℝ} (hb : 0 < b)
    (hsmall : b < min (1 / 100 : ℝ) (1 / (40 * ((h0 : ℝ) + 2)))) :
    Real.exp (-(dyadicSieveLevel b : ℝ)) ≤ Real.exp 2 * Real.exp (-(1 / 20 : ℝ) / b) := by
  have hlevel := (dyadicSieveLevel_bounds h0 hb hsmall).2.2.2
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have heq : (1 : ℝ) / (20 * b) = (1 / 20 : ℝ) / b := by ring
  rw [heq] at hlevel
  rw [neg_div]
  linarith

end Erdos821.P8Core

