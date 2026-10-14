import Mathlib

/-! Converse reconstruction for §5. Coprimality retains exact divisibility. -/

namespace Erdos821.S56

/-- A determinant representation reconstructs exactly one positive common factor.
The shift may be zero; the algebraic reconstruction does not need that restriction. -/
theorem determinant_converse_unique (m m' e h h' k : ℤ)
    (hm : 0 < m) (he : 0 < e) (hh : 0 < h)
    (hdelta : m' - m = 2 * e * k) (hcross : m * h' - m' * h = k)
    (hcop : IsCoprime m k) :
    ∃! n : ℤ, 0 < n ∧ m * n = 2 * e * h + 1 ∧ m' * n = 2 * e * h' + 1 := by
  have hidentity : m * (h' - h) = k * (2 * e * h + 1) := by
    linear_combination hcross + h * hdelta
  have hdiv : m ∣ 2 * e * h + 1 :=
    hcop.dvd_of_dvd_mul_left ⟨h' - h, hidentity.symm⟩
  obtain ⟨n, hn⟩ := hdiv
  have hfirst : m * n = 2 * e * h + 1 := hn.symm
  have hnpos : 0 < n := by
    by_contra hn0
    have hnonpos : m * n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm.le (le_of_not_gt hn0)
    have hprod : 0 < 2 * e * h + 1 := by positivity
    linarith
  have hincrement : h' - h = k * n := by
    apply mul_left_cancel₀ hm.ne'
    rw [hidentity, hn]
    ring
  have hsecond : m' * n = 2 * e * h' + 1 := by
    linear_combination n * hdelta - (2 * e) * hincrement + hfirst
  refine ⟨n, ⟨hnpos, hfirst, hsecond⟩, ?_⟩
  intro n' hn'
  apply mul_left_cancel₀ hm.ne'
  exact hn'.2.1.trans hfirst.symm


end Erdos821.S56
