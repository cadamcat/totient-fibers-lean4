import Erdos821.P6Off.Rough

noncomputable section
open Filter

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic

/-- Algebraic z range from the enlarged smooth e,n ranges. -/
theorem cross_product_bounds (x U V E e n m m' h : ℝ)
    (hx : 32 ≤ x) (hU : 0 < U) (hV : 0 < V) (hE : 0 < E)
    (he : 0 < e) (hh : 0 < h)
    (hUVlo : x / 8 ≤ U * V) (hUVhi : U * V ≤ 8 * x)
    (hmlo : U ≤ m) (hmhi : m ≤ 2 * U)
    (hm'lo : U ≤ m') (hm'hi : m' ≤ 2 * U)
    (hnlo : V / 2 ≤ n) (hnhi : n ≤ 4 * V)
    (hehi : e ≤ 2 * E) (heq : m * n = 2 * e * h + 1) :
    U * x / (128 * E) ≤ m' * h ∧
      m' * h ≤ 64 * U * x / e := by
  have hxpos : 0 < x := by linarith
  have hmpos : 0 < m := hU.trans_le hmlo
  have hm'pos : 0 < m' := hU.trans_le hm'lo
  have hnpos : 0 < n := (half_pos hV).trans_le hnlo
  have hprodlo : x / 16 ≤ m * n := by
    have h := mul_le_mul hmlo hnlo (half_pos hV).le hmpos.le
    nlinarith [hUVlo]
  have hprodhi : m * n ≤ 64 * x := by
    have h := mul_le_mul hmhi hnhi hnpos.le (by positivity : 0 ≤ 2 * U)
    nlinarith [hUVhi]
  have hlow : x / 32 ≤ m * n - 1 := by nlinarith
  have hhigh : m * n - 1 ≤ 64 * x := by linarith
  have hcross : 2 * e * (m' * h) = m' * (m * n - 1) := by nlinarith [heq]
  have hzpos : 0 < m' * h := mul_pos hm'pos hh
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 128 * E)).mpr
    have hright := mul_le_mul hm'lo hlow (by positivity : 0 ≤ x / 32) hm'pos.le
    have hez := mul_le_mul_of_nonneg_right hehi hzpos.le
    nlinarith [hcross]
  · apply (le_div_iff₀ he).mpr
    have hright := mul_le_mul hm'hi hhigh (by nlinarith : 0 ≤ m * n - 1)
      (by positivity : 0 ≤ 2 * U)
    nlinarith [hcross]

/-- The logarithmic e scale converts the cross-product bounds to powers of L. -/
theorem cross_product_log_bounds (x U V e n m m' h K0 Cs : ℝ)
    (hx : 32 ≤ x) (hL : 0 < L x) (hU : 0 < U) (hV : 0 < V)
    (he : 0 < e) (hh : 0 < h)
    (hUVlo : x / 8 ≤ U * V) (hUVhi : U * V ≤ 8 * x)
    (hmlo : U ≤ m) (hmhi : m ≤ 2 * U)
    (hm'lo : U ≤ m') (hm'hi : m' ≤ 2 * U)
    (hnlo : V / 2 ≤ n) (hnhi : n ≤ 4 * V)
    (helo : U * L x ^ (-K0) * L x ^ (-Cs) / 2 ≤ e)
    (hehi : e ≤ 2 * (U * L x ^ (-K0))) (heq : m * n = 2 * e * h + 1) :
    x * L x ^ K0 / 128 ≤ m' * h ∧
      m' * h ≤ 128 * x * L x ^ (K0 + Cs) := by
  have hE : 0 < U * L x ^ (-K0) := mul_pos hU (Real.rpow_pos_of_pos hL _)
  obtain ⟨hlo, hhi⟩ := cross_product_bounds x U V (U * L x ^ (-K0)) e n m m' h
    hx hU hV hE he hh hUVlo hUVhi hmlo hmhi hm'lo hm'hi hnlo hnhi hehi heq
  constructor
  · convert hlo using 1
    rw [Real.rpow_neg hL.le]
    field_simp [hU.ne', (Real.rpow_pos_of_pos hL K0).ne']
  · have hmin : 0 < U * L x ^ (-K0) * L x ^ (-Cs) / 2 := by positivity
    have hzpos : 0 < m' * h := mul_pos (hU.trans_le hm'lo) hh
    apply hhi.trans
    calc
      _ ≤ 64 * U * x / (U * L x ^ (-K0) * L x ^ (-Cs) / 2) := by
        gcongr
      _ = _ := by
        rw [Real.rpow_neg hL.le K0, Real.rpow_neg hL.le Cs, Real.rpow_add hL]
        field_simp [hU.ne', (Real.rpow_pos_of_pos hL K0).ne',
          (Real.rpow_pos_of_pos hL Cs).ne']
        ring


end Erdos821.P6Off
