import Mathlib

/-! Exact integer determinant identities for §5's Type II parametrization. -/

namespace Erdos821.S56

/-- The forward identities, with the architect's increment hypothesis. -/
theorem determinant_forward_of_increment (m m' n e h h' k : ℤ)
    (hm : m * n = 2 * e * h + 1) (hm' : m' * n = 2 * e * h' + 1)
    (he : e ≠ 0) (hk : m' - m = 2 * e * k) :
    h' - h = k * n ∧ m * h' - m' * h = k := by
  have hc : (2 * e) * (h' - h - k * n) = 0 := by
    linear_combination hm - hm' + n * hk
  have he₂ : 2 * e ≠ 0 := mul_ne_zero (by norm_num) he
  have hd : h' - h = k * n := by
    have hz := (mul_eq_zero.mp hc).resolve_left he₂
    linarith
  refine ⟨hd, ?_⟩
  linear_combination m * hd - h * hk + k * hm


end Erdos821.S56
