import Erdos821.P6Off.Growth

noncomputable section
open Filter
open scoped BigOperators

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic

def determinantTruncation (U V : ℝ) : ℕ := ⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊

theorem determinantTruncation_lower (x U V : ℝ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUV : x / 8 ≤ U * V) : U * x ≤ (determinantTruncation U V : ℝ) := by
  have hUpos : 0 < U := by linarith
  have hVpos : 0 < V := by linarith
  have hceil : 2 * U ≤ (⌈2 * U⌉₊ : ℝ) := Nat.le_ceil _
  have hfloor : 2 * V ≤ (⌊4 * V⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one (4 * V)
    push_cast at h
    linarith
  have hpow : (2 * U) ^ (2 : ℕ) ≤ (⌈2 * U⌉₊ : ℝ) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hceil _
  calc
    U * x ≤ (2 * U) ^ (2 : ℕ) * (2 * V) := by
      have h := mul_le_mul_of_nonneg_left hUV hUpos.le
      nlinarith
    _ ≤ (⌈2 * U⌉₊ : ℝ) ^ (2 : ℕ) * (⌊4 * V⌋₊ : ℝ) :=
      mul_le_mul hpow hfloor (by positivity) (by positivity)
    _ = _ := by simp [determinantTruncation]

/-- A logarithmic z window lies above every relevant shift and below x²/3,
once the fixed power precision is chosen. -/
theorem log_window_aux (x C Z : ℝ) (hx : 0 < x) (hL : 3 ≤ L x) (hC : 0 < C)
    (hgrowth : L x ^ (2 * C + 2) ≤ x)
    (hlo : x * L x ^ (-C) ≤ Z) (hhi : Z ≤ x * L x ^ C) :
    1 ≤ Z ∧ L x ^ C ≤ Z ∧ 3 * Z ≤ x ^ (2 : ℕ) := by
  have hLpos : 0 < L x := by linarith
  have hL1 : 1 ≤ L x := by linarith
  have hlow : L x ^ (C + 2) ≤ x * L x ^ (-C) := by
    have h := mul_le_mul_of_nonneg_right hgrowth (Real.rpow_nonneg hLpos.le (-C))
    have heq : L x ^ (2 * C + 2) * L x ^ (-C) = L x ^ (C + 2) := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    rwa [heq] at h
  have hpow1 : 1 ≤ L x ^ C := Real.one_le_rpow hL1 hC.le
  have hpowlo : L x ^ C ≤ L x ^ (C + 2) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hXZ : L x ^ C ≤ Z := hpowlo.trans (hlow.trans hlo)
  refine ⟨hpow1.trans hXZ, hXZ, ?_⟩
  have hpower : 3 * L x ^ C ≤ x := by
    calc
      _ ≤ L x ^ (C + 1) := by
        rw [Real.rpow_add hLpos C 1, Real.rpow_one]
        have h := mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hLpos.le C)
        nlinarith
      _ ≤ L x ^ (2 * C + 2) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ ≤ x := hgrowth
  have hmul := mul_le_mul_of_nonneg_left hpower hx.le
  nlinarith

theorem log_window_truncation (x U V C b Z : ℝ) (hx : 0 < x) (hL : 2 ≤ L x)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUV : x / 8 ≤ U * V)
    (hgrowth : L x ^ (C + 1) ≤ x ^ b) (hUb : x ^ b ≤ U) (hZ : Z ≤ x * L x ^ C) :
    2 * Z ≤ (determinantTruncation U V : ℝ) := by
  have hLpos : 0 < L x := by linarith
  have hpower : 2 * L x ^ C ≤ U := by
    calc
      _ ≤ L x ^ (C + 1) := by
        rw [Real.rpow_add hLpos C 1, Real.rpow_one]
        have h := mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hLpos.le C)
        nlinarith
      _ ≤ x ^ b := hgrowth
      _ ≤ U := hUb
  have hmul := mul_le_mul_of_nonneg_left hpower hx.le
  apply le_trans _ (determinantTruncation_lower x U V hU hV hUV)
  nlinarith


end Erdos821.P6Off
