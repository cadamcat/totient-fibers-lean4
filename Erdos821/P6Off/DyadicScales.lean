import Erdos821.P6Off.Dyadic

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic

def dyadicCount (x C : ℝ) : ℕ := ⌈(2 * C + 1) * T x / Real.log 2⌉₊
def dyadicBase (x C : ℝ) : ℝ := x * L x ^ (-C)
def dyadicScale (x C : ℝ) (j : ℕ) : ℝ := dyadicBase x C * 2 ^ j

/-- The ceil precision costs a factor at most two in the last dyadic scale. -/
theorem dyadicCount_power_bounds (x C : ℝ) (hL : 2 ≤ L x) (hC : 0 < C) :
    L x ^ (2 * C + 1) ≤ (2 : ℝ) ^ dyadicCount x C ∧
      (2 : ℝ) ^ dyadicCount x C ≤ 2 * L x ^ (2 * C + 1) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 < L x := by linarith
  have hTnonneg : 0 ≤ T x := Real.log_nonneg (by linarith : 1 ≤ L x)
  have htpos : 0 ≤ (2 * C + 1) * T x / Real.log 2 := by
    positivity
  have hceilLo : (2 * C + 1) * T x / Real.log 2 ≤ (dyadicCount x C : ℝ) := Nat.le_ceil _
  have hceilHi : (dyadicCount x C : ℝ) ≤ (2 * C + 1) * T x / Real.log 2 + 1 :=
    (Nat.ceil_lt_add_one htpos).le
  have heq : (2 : ℝ) ^ ((2 * C + 1) * T x / Real.log 2) = L x ^ (2 * C + 1) := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hLpos]
    congr 1
    unfold T
    field_simp
  constructor
  · rw [← heq, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hceilLo
  · calc
      _ = (2 : ℝ) ^ (dyadicCount x C : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ ((2 * C + 1) * T x / Real.log 2 + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hceilHi
      _ = _ := by rw [Real.rpow_add (by norm_num), heq]; norm_num; ring

/-- All dyadic scales lie in a fixed logarithmic window and their number is
bounded by L². These parameters are chosen before the discrepancy precision. -/
theorem eventually_dyadic_scales (C : ℝ) (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop,
      0 < dyadicBase x C ∧ (dyadicCount x C : ℝ) ≤ L x ^ (2 : ℕ) ∧
      (∀ j ∈ Finset.range (dyadicCount x C),
        x * L x ^ (-(C + 2)) ≤ dyadicScale x C j ∧
          dyadicScale x C j ≤ x * L x ^ (C + 2)) ∧
      (∀ z : ℝ, x * L x ^ (-C) ≤ z → z ≤ x * L x ^ C →
        (∑ j ∈ Finset.range (dyadicCount x C), dyadicCutoff (z / dyadicScale x C j)) = 1) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (0 : ℝ), hL.eventually (eventually_ge_atTop 2),
    hL.eventually (eventually_ge_atTop ((2 * C + 1) / Real.log 2 + 1))] with x hx hL2 hLK
  have hLpos : 0 < L x := by linarith
  have hTnonneg : 0 ≤ T x := Real.log_nonneg (by linarith : 1 ≤ L x)
  have hbase : 0 < dyadicBase x C := mul_pos hx (Real.rpow_pos_of_pos hLpos _)
  obtain ⟨hpowLo, hpowHi⟩ := dyadicCount_power_bounds x C hL2 hC
  have htpos : 0 ≤ (2 * C + 1) * T x / Real.log 2 := by
    positivity
  have hceilHi : (dyadicCount x C : ℝ) ≤ (2 * C + 1) * T x / Real.log 2 + 1 :=
    (Nat.ceil_lt_add_one htpos).le
  refine ⟨hbase, ?_, ?_, ?_⟩
  · have hT : T x ≤ L x := (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)
    have hcoef : 0 ≤ (2 * C + 1) / Real.log 2 := by positivity
    have hcount : (dyadicCount x C : ℝ) ≤ ((2 * C + 1) / Real.log 2 + 1) * L x := by
      calc
        _ ≤ (2 * C + 1) / Real.log 2 * T x + 1 := by convert hceilHi using 1 <;> ring
        _ ≤ (2 * C + 1) / Real.log 2 * L x + L x :=
          add_le_add (mul_le_mul_of_nonneg_left hT hcoef) (by linarith)
        _ = _ := by ring
    exact hcount.trans (by nlinarith)
  · intro j hj
    have hjle : j ≤ dyadicCount x C := (Finset.mem_range.mp hj).le
    have hpowj : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ dyadicCount x C := pow_le_pow_right₀ (by norm_num) hjle
    constructor
    · calc
        _ ≤ dyadicBase x C := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L x) (by linarith)) hx.le
        _ ≤ _ := by
          unfold dyadicScale
          exact le_mul_of_one_le_right hbase.le (one_le_pow₀ (by norm_num))
    · calc
        _ ≤ dyadicBase x C * (2 * L x ^ (2 * C + 1)) :=
          mul_le_mul_of_nonneg_left (hpowj.trans hpowHi) hbase.le
        _ = 2 * x * L x ^ (C + 1) := by
          unfold dyadicBase
          have heq : L x ^ (-C) * L x ^ (2 * C + 1) = L x ^ (C + 1) := by
            rw [← Real.rpow_add hLpos]
            congr 1
            ring
          calc
            _ = 2 * x * (L x ^ (-C) * L x ^ (2 * C + 1)) := by ring
            _ = _ := by rw [heq]
        _ ≤ x * L x ^ (C + 2) := by
          rw [show C + 2 = (C + 1) + 1 by ring,
            Real.rpow_add hLpos (C + 1) 1, Real.rpow_one]
          have h := mul_le_mul_of_nonneg_left hL2
            (mul_nonneg hx.le (Real.rpow_nonneg hLpos.le (C + 1)))
          nlinarith
  · intro z hlo hhi
    apply dyadicCutoff_sum_one z (dyadicBase x C) hbase (dyadicCount x C) hlo
    have hmul : x * L x ^ C ≤ dyadicBase x C * (2 : ℝ) ^ dyadicCount x C / 2 := by
      have hLpow : 2 * L x ^ (2 * C) ≤ L x ^ (2 * C + 1) := by
        rw [Real.rpow_add hLpos, Real.rpow_one]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hL2 (Real.rpow_nonneg hLpos.le (2 * C))
      calc
        _ = dyadicBase x C * (2 * L x ^ (2 * C)) / 2 := by
          unfold dyadicBase
          have heq : L x ^ (-C) * L x ^ (2 * C) = L x ^ C := by
            rw [← Real.rpow_add hLpos]
            congr 1
            ring
          calc
            _ = x * (L x ^ (-C) * L x ^ (2 * C)) := by rw [heq]
            _ = _ := by ring
        _ ≤ _ := by gcongr; exact hLpow.trans hpowLo
    exact hhi.trans hmul


end Erdos821.P6Off
