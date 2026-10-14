import Erdos821.P7Char.Task

/-! Elementary eventual comparisons between powers of `x` and of `L x = log x`, and
divisor-moment bounds in the form used by the Type I assembly. -/
noncomputable section
open scoped BigOperators
open Filter Erdos821.Blueprint.Analytic

namespace Erdos821.P7Char

open Erdos821.Blueprint

theorem tendsto_L' : Tendsto L atTop atTop := Real.tendsto_log_atTop

theorem ev_log_rpow_le_rpow (a b c : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, c * L x ^ a ≤ x ^ b := by
  have hlo := (isLittleO_log_rpow_rpow_atTop a hb).bound (c := 1 / (|c| + 1)) (by positivity)
  filter_upwards [hlo, eventually_gt_atTop 1] with x hx hx1
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hLa : 0 ≤ Real.log x ^ a := Real.rpow_nonneg hL.le a
  have hxb : 0 ≤ x ^ b := Real.rpow_nonneg (by linarith) b
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hLa, abs_of_nonneg hxb] at hx
  have h1 : (|c| + 1) * Real.log x ^ a ≤ x ^ b := by
    have := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ |c| + 1)
    rwa [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
  have h2 : c * Real.log x ^ a ≤ (|c| + 1) * Real.log x ^ a :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) hLa
  exact h2.trans h1

/-- A power saving beats every power of the logarithm. -/
theorem ev_small_power (c a b D : ℝ) (hb : b < 1) :
    ∀ᶠ x : ℝ in atTop, c * L x ^ a * x ^ b ≤ x * L x ^ (-D) := by
  filter_upwards [ev_log_rpow_le_rpow (a + D) (1 - b) c (by linarith),
    eventually_gt_atTop 1] with x h hx1
  have hL : 0 < L x := Real.log_pos hx1
  have hx0 : 0 < x := by linarith
  have e1 : c * L x ^ a * x ^ b = (c * L x ^ (a + D)) * (L x ^ (-D) * x ^ b) := by
    rw [Real.rpow_add hL, Real.rpow_neg hL.le]
    have : L x ^ D ≠ 0 := (Real.rpow_pos_of_pos hL D).ne'
    field_simp
  have e2 : x * L x ^ (-D) = x ^ (1 - b) * (L x ^ (-D) * x ^ b) := by
    have : x ^ (1 - b) * x ^ b = x := by
      rw [← Real.rpow_add hx0, sub_add_cancel, Real.rpow_one]
    calc x * L x ^ (-D) = (x ^ (1 - b) * x ^ b) * L x ^ (-D) := by rw [this]
      _ = _ := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- A larger logarithmic saving beats any constant. -/
theorem ev_small_log (c a D : ℝ) (ha : a < -D) :
    ∀ᶠ x : ℝ in atTop, c * x * L x ^ a ≤ x * L x ^ (-D) := by
  have hpos : 0 < -(a + D) := by linarith
  filter_upwards [((tendsto_rpow_atTop hpos).comp tendsto_L').eventually
    (eventually_ge_atTop |c|), eventually_gt_atTop 1] with x h hx1
  have hL : 0 < L x := Real.log_pos hx1
  have hx0 : 0 < x := by linarith
  simp only [Function.comp] at h
  have h1 : c * L x ^ (a + D) ≤ 1 := by
    have hp : 0 < L x ^ (a + D) := Real.rpow_pos_of_pos hL _
    calc c * L x ^ (a + D) ≤ |c| * L x ^ (a + D) :=
          mul_le_mul_of_nonneg_right (le_abs_self c) hp.le
      _ ≤ L x ^ (-(a + D)) * L x ^ (a + D) := mul_le_mul_of_nonneg_right h hp.le
      _ = 1 := by rw [← Real.rpow_add hL]; simp
  have e1 : c * x * L x ^ a = (c * L x ^ (a + D)) * (x * L x ^ (-D)) := by
    rw [Real.rpow_add hL, Real.rpow_neg hL.le]
    have : L x ^ D ≠ 0 := (Real.rpow_pos_of_pos hL D).ne'
    field_simp
  rw [e1]
  have : 0 ≤ x * L x ^ (-D) := by positivity
  nlinarith

/-- Dyadic counts are logarithmic. -/
theorem natLog_add_one_le (x : ℝ) (hx : 1 < x) (hL : 1 ≤ L x) (n : ℕ) (hn : (n : ℝ) ≤ x) :
    ((Nat.log 2 n : ℕ) : ℝ) + 1 ≤ 3 * L x := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0]; simp; linarith
  · have hpow : ((2 : ℝ) ^ (Nat.log 2 n)) ≤ x := by
      have : 2 ^ (Nat.log 2 n) ≤ n := Nat.pow_log_le_self 2 hpos.ne'
      calc ((2 : ℝ) ^ (Nat.log 2 n)) = ((2 ^ (Nat.log 2 n) : ℕ) : ℝ) := by push_cast; rfl
        _ ≤ n := by exact_mod_cast this
        _ ≤ x := hn
    have hlog : ((Nat.log 2 n : ℕ) : ℝ) * Real.log 2 ≤ L x := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) hpow
    have h2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have : ((Nat.log 2 n : ℕ) : ℝ) ≤ 2 * L x := by
      have h0 : (0 : ℝ) ≤ ((Nat.log 2 n : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    linarith

/-- Divisor moments, in the uniform form `≤ L^c` for moduli up to `4x`. -/
theorem divisor_moment_L (hdiv : DivisorMoments) (k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ x : ℝ in atTop, ∀ N : ℕ, (N : ℝ) ≤ 4 * x →
      (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k / n) ≤ L x ^ c := by
  obtain ⟨C, K, hK, hY⟩ := hdiv k
  refine ⟨|C| + 1, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop 1,
    tendsto_L'.eventually (eventually_ge_atTop (K * 2 ^ |C|)),
    tendsto_L'.eventually (eventually_ge_atTop (Real.log 8)),
    tendsto_L'.eventually (eventually_ge_atTop 1)] with x hx1 hLK hL8 hL1
  intro N hN
  have hx0 : 0 < x := by linarith
  have hY1 : (1 : ℝ) ≤ 4 * x := by linarith
  have hsub : (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k / n) ≤
      ∑ n ∈ Finset.Icc 1 ⌊4 * x⌋₊, (n.divisors.card : ℝ) ^ k / n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
      exact Finset.mem_Icc.2 ⟨h1, h2.trans (Nat.le_floor hN)⟩
    · intro _ _ _
      positivity
  refine hsub.trans ((hY (4 * x) hY1).1.trans ?_)
  have hlog8 : Real.log (2 * (4 * x)) = Real.log 8 + L x := by
    rw [show 2 * (4 * x) = 8 * x by ring, Real.log_mul (by norm_num) hx0.ne']
    rfl
  have hl1 : 1 ≤ Real.log (2 * (4 * x)) := by
    rw [hlog8]
    have : (1 : ℝ) < Real.log 8 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    linarith
  have hl2 : Real.log (2 * (4 * x)) ≤ 2 * L x := by rw [hlog8]; linarith
  have hA : Real.log (2 * (4 * x)) ^ C ≤ Real.log (2 * (4 * x)) ^ |C| :=
    Real.rpow_le_rpow_of_exponent_le hl1 (le_abs_self C)
  have hB : Real.log (2 * (4 * x)) ^ |C| ≤ (2 * L x) ^ |C| :=
    Real.rpow_le_rpow (by linarith) hl2 (abs_nonneg C)
  have hL0 : 0 < L x := by linarith
  calc K * Real.log (2 * (4 * x)) ^ C ≤ K * (2 * L x) ^ |C| :=
        mul_le_mul_of_nonneg_left (hA.trans hB) hK.le
    _ = (K * 2 ^ |C|) * L x ^ |C| := by
        rw [Real.mul_rpow (by norm_num) hL0.le]; ring
    _ ≤ L x * L x ^ |C| := mul_le_mul_of_nonneg_right hLK (by positivity)
    _ = L x ^ (|C| + 1) := by
        rw [Real.rpow_add hL0, Real.rpow_one]; ring

end Erdos821.P7Char
