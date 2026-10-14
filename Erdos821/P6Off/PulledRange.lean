import Erdos821.P6Off.Range
import Erdos821.P6Off.Discrepancy

noncomputable section

namespace Erdos821.P6Off
open Erdos821.Blueprint.Analytic Erdos821.S56Core

def pulledE (k : ℤ) (m m' : ℝ) : ℝ := (m' - m) / (2 * k)
def pulledN (k : ℤ) (m m' z : ℝ) : ℝ := (m' - m) * z / (k * m * m') + 1 / m

theorem pulled_cutoff_arguments (k : ℤ) (m m' z E V : ℝ) :
    (m' - m) / (2 * k * E) = pulledE k m m' / E ∧
      (m' - m) * z / (k * m * m' * V) + 1 / (m * V) = pulledN k m m' z / V := by
  unfold pulledE pulledN
  constructor <;> field_simp <;> ring

theorem pulled_factor_equation (k : ℤ) (m m' z : ℝ)
    (hk : k ≠ 0) (hm : m ≠ 0) (hm' : m' ≠ 0) :
    m * pulledN k m m' z = 2 * pulledE k m m' * (z / m') + 1 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  unfold pulledE pulledN
  field_simp [hk', hm, hm'] <;> ring

theorem absorb_cross_product_window (x K0 Cs z : ℝ)
    (hx : 0 < x) (hL : 128 ≤ L x) (hK : 0 < K0) (hCs : 0 < Cs)
    (hlo : x * L x ^ K0 / 128 ≤ z) (hhi : z ≤ 128 * x * L x ^ (K0 + Cs)) :
    x * L x ^ (-(K0 + Cs + 1)) ≤ z ∧ z ≤ x * L x ^ (K0 + Cs + 1) := by
  have hLpos : 0 < L x := by linarith
  constructor
  · have hinv : L x ^ (-(K0 + Cs + 1)) ≤ (128 : ℝ)⁻¹ := by
      calc
        _ ≤ L x ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
          (by linarith : 1 ≤ L x) (by linarith)
        _ = (L x)⁻¹ := Real.rpow_neg_one _
        _ ≤ (128 : ℝ)⁻¹ := by gcongr
    have hone : 1 ≤ L x ^ K0 := Real.one_le_rpow (by linarith) hK.le
    apply (mul_le_mul_of_nonneg_left hinv hx.le).trans
    have h := mul_le_mul_of_nonneg_left hone hx.le
    nlinarith
  · apply hhi.trans
    rw [Real.rpow_add hLpos (K0 + Cs) 1, Real.rpow_one]
    have h := mul_le_mul_of_nonneg_left hL
      (mul_nonneg hx.le (Real.rpow_nonneg hLpos.le (K0 + Cs)))
    nlinarith

/-- The pulled-back smooth cutoffs themselves impose the same z window;
this bound does not use or discard any integer divisibility condition. -/
theorem pulled_cutoff_z_range (x U V K0 Cs : ℝ) (etae etan : ℝ → ℝ)
    (hx : 32 ≤ x) (hL : 128 ≤ L x) (hU : 0 < U) (hV : 0 < V)
    (hK : 0 < K0) (hCs : 0 < Cs)
    (hUVlo : x / 8 ≤ U * V) (hUVhi : U * V ≤ 8 * x)
    (hse : Function.support etae ⊆ Set.Icc (L x ^ (-Cs) / 2) 2)
    (hsn : Function.support etan ⊆ Set.Icc (1 / 2) 4)
    (k : ℤ) (hk : k ≠ 0) (m m' z : ℝ) (hz : 0 < z)
    (hm : U ≤ m ∧ m ≤ 2 * U) (hm' : U ≤ m' ∧ m' ≤ 2 * U)
    (hweight : etae ((m' - m) / (2 * k * (U * L x ^ (-K0)))) *
      etan ((m' - m) * z / (k * m * m' * V) + 1 / (m * V)) ≠ 0) :
    x * L x ^ (-(K0 + Cs + 1)) ≤ z ∧ z ≤ x * L x ^ (K0 + Cs + 1) := by
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L x := by linarith
  have hE : 0 < U * L x ^ (-K0) := by positivity
  have hmpos : 0 < m := hU.trans_le hm.1
  have hm'pos : 0 < m' := hU.trans_le hm'.1
  obtain ⟨hearg, hnarg⟩ := pulled_cutoff_arguments k m m' z (U * L x ^ (-K0)) V
  rw [hearg, hnarg] at hweight
  have heRange := hse (mul_ne_zero_iff.mp hweight).1
  have hnRange := hsn (mul_ne_zero_iff.mp hweight).2
  have helo : U * L x ^ (-K0) * L x ^ (-Cs) / 2 ≤ pulledE k m m' := by
    have h := (le_div_iff₀ hE).mp heRange.1
    nlinarith
  have hehi : pulledE k m m' ≤ 2 * (U * L x ^ (-K0)) := (div_le_iff₀ hE).mp heRange.2
  have hepos : 0 < pulledE k m m' := lt_of_lt_of_le (by positivity) helo
  have hnlo : V / 2 ≤ pulledN k m m' z := by
    have h := (le_div_iff₀ hV).mp hnRange.1
    nlinarith
  have hnhi : pulledN k m m' z ≤ 4 * V := (div_le_iff₀ hV).mp hnRange.2
  obtain ⟨hlo, hhi⟩ := cross_product_log_bounds x U V (pulledE k m m')
    (pulledN k m m' z) m m' (z / m') K0 Cs hx hLpos hU hV hepos (div_pos hz hm'pos)
    hUVlo hUVhi hm.1 hm.2 hm'.1 hm'.2 hnlo hnhi helo hehi
    (pulled_factor_equation k m m' z hk hmpos.ne' hm'pos.ne')
  have hcancel : m' * (z / m') = z := by field_simp
  rw [hcancel] at hlo hhi
  exact absorb_cross_product_window x K0 Cs z hxpos hL hK hCs hlo hhi


end Erdos821.P6Off
