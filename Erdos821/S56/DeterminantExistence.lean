import Erdos821.S56.Determinant

namespace Erdos821.S56

/-- The common factor equations produce the nonzero signed shift used in §5. -/
theorem determinant_shift_exists (m m' n e h h' : ℤ)
    (he : 0 < e) (hm : m * n = 2 * e * h + 1)
    (hm' : m' * n = 2 * e * h' + 1) (hne : m ≠ m') :
    ∃ k : ℤ, k ≠ 0 ∧ m' - m = 2 * e * k ∧ h' - h = k * n ∧ m * h' - m' * h = k := by
  have hcop : IsCoprime (2 * e) n := by
    refine ⟨-h, m, ?_⟩
    linear_combination hm
  have hdiv : 2 * e ∣ (m' - m) * n := by
    refine ⟨h' - h, ?_⟩
    linear_combination hm' - hm
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_right hdiv
  have hk0 : k ≠ 0 := by
    intro hz
    have heq : m' - m = 0 := by simpa [hz] using hk
    exact hne (sub_eq_zero.mp heq).symm
  exact ⟨k, hk0, hk, determinant_forward_of_increment m m' n e h h' k hm hm' he.ne' hk⟩


end Erdos821.S56
