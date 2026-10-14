import Erdos821.S56.Diagonal

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem inner_square_expansion (U : ℝ) (ah alpha : ℕ → ℂ) (e n : ℕ) (he : 0 < e) :
    ‖innerSum U ah alpha e n‖ ^ 2 =
      (∑ m ∈ dyad U, if 1 < m * n ∧ 2 * e ∣ m * n - 1 then
        ‖alpha m * ah ((m * n - 1) / (2 * e))‖ ^ 2 else 0) +
      (∑ m ∈ dyad U, ∑ m' ∈ dyad U,
        if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
            2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
          alpha m * ah ((m * n - 1) / (2 * e)) *
            star (alpha m' * ah ((m' * n - 1) / (2 * e))) else 0).re := by
  let f : ℕ → ℂ := fun m => if 1 < m * n ∧ 2 * e ∣ m * n - 1 then
    alpha m * ah ((m * n - 1) / (2 * e)) else 0
  have hinner : innerSum U ah alpha e n = ∑ m ∈ dyad U, f m := by
    apply Finset.sum_congr rfl
    intro m _
    simp only [f, he, true_and]
  have hdiag : (∑ m ∈ dyad U, ‖f m‖ ^ 2) =
      ∑ m ∈ dyad U, if 1 < m * n ∧ 2 * e ∣ m * n - 1 then
        ‖alpha m * ah ((m * n - 1) / (2 * e))‖ ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro m _
    by_cases hm : 1 < m * n ∧ 2 * e ∣ m * n - 1 <;> simp [f, hm]
  rw [hinner]
  have hsq := square_sum_diagonal (dyad U) f
  rw [hdiag] at hsq
  apply hsq.trans
  apply congrArg (fun w : ℂ =>
    (∑ m ∈ dyad U, if 1 < m * n ∧ 2 * e ∣ m * n - 1 then
      ‖alpha m * ah ((m * n - 1) / (2 * e))‖ ^ 2 else 0) + w.re)
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro m' _
  by_cases hne : m ≠ m' <;> by_cases hm : 1 < m * n <;> by_cases hm' : 1 < m' * n <;>
    by_cases hd : 2 * e ∣ m * n - 1 <;> by_cases hd' : 2 * e ∣ m' * n - 1 <;>
      simp [f, hne, hm, hm', hd, hd']

def smoothedSquare (E U V : ℝ) (etae etan : ℝ → ℝ) (ah alpha : ℕ → ℂ) : ℝ :=
  ∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
    etae (e / E) * etan (n / V) * ‖innerSum U ah alpha e n‖ ^ 2

/-- The exact square has the literal diagonal plus the real part of the
signed off-diagonal correlation; no absolute value is inserted in this identity. -/
theorem smoothed_square_eq (E U V : ℝ) (etae etan : ℝ → ℝ) (ah alpha : ℕ → ℂ) :
    smoothedSquare E U V etae etan ah alpha =
      diagonalSum E U V etae etan ah alpha + (offDiagonalSum E U V etae etan ah alpha).re := by
  have hre : (offDiagonalSum E U V etae etan ah alpha).re =
      ∑ e ∈ Finset.Icc 1 ⌊2 * E⌋₊, ∑ n ∈ Finset.Icc 1 ⌊4 * V⌋₊,
        etae (e / E) * etan (n / V) *
          (∑ m ∈ dyad U, ∑ m' ∈ dyad U,
            if m ≠ m' ∧ 1 < m * n ∧ 1 < m' * n ∧
                2 * e ∣ m * n - 1 ∧ 2 * e ∣ m' * n - 1 then
              alpha m * ah ((m * n - 1) / (2 * e)) *
                star (alpha m' * ah ((m' * n - 1) / (2 * e))) else 0).re := by
    simp [offDiagonalSum, Complex.mul_re]
  rw [hre]
  unfold smoothedSquare diagonalSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [inner_square_expansion U ah alpha e n (Finset.mem_Icc.mp he).1, mul_add]


end Erdos821.S56Core
