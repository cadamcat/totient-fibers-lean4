import Erdos821.S56.Separated
import Erdos821.S56.ElementaryLeaves

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def innerSum (U : ℝ) (ah alpha : ℕ → ℂ) (e n : ℕ) : ℂ :=
  ∑ m ∈ dyad U,
    if 0 < e ∧ 1 < m * n ∧ 2 * e ∣ m * n - 1 then
      alpha m * ah ((m * n - 1) / (2 * e)) else 0

/-- The outside Cauchy factor counts (e,n), rather than (m,n). -/
theorem separated_cauchy (emin E U V M : ℝ) (ae ah alpha beta : ℕ → ℂ)
    (hM : 0 ≤ M) (hae : ∀ e, ‖ae e‖ ≤ M) (hbeta : ∀ n, ‖beta n‖ ≤ M) :
    ‖separatedSum emin E U V ae ah alpha beta‖ ^ 2 ≤
      ((Finset.Icc ⌈emin⌉₊ ⌊E⌋₊).card : ℝ) * (dyad V).card * M ^ 4 *
        ∑ e ∈ Finset.Icc ⌈emin⌉₊ ⌊E⌋₊, ∑ n ∈ dyad V,
          ‖innerSum U ah alpha e n‖ ^ 2 := by
  let s := (Finset.Icc ⌈emin⌉₊ ⌊E⌋₊) ×ˢ dyad V
  have hc := Erdos821.S56.weighted_cauchy_proved s
    (fun p => ae p.1 * beta p.2) (fun p => innerSum U ah alpha p.1 p.2)
  have hcoeff : (∑ p ∈ s, ‖ae p.1 * beta p.2‖ ^ 2) ≤
      ((Finset.Icc ⌈emin⌉₊ ⌊E⌋₊).card : ℝ) * (dyad V).card * M ^ 4 := by
    calc
      _ ≤ ∑ _p ∈ s, M ^ 4 := by
        apply Finset.sum_le_sum
        intro p _
        rw [norm_mul]
        have hprod : ‖ae p.1‖ * ‖beta p.2‖ ≤ M * M :=
          mul_le_mul (hae p.1) (hbeta p.2) (norm_nonneg _) hM
        calc
          _ ≤ (M * M) ^ 2 := pow_le_pow_left₀ (by positivity) hprod 2
          _ = M ^ 4 := by ring
      _ = _ := by simp [s, mul_assoc]
  have hnonneg : 0 ≤ ∑ p ∈ s, ‖innerSum U ah alpha p.1 p.2‖ ^ 2 := by positivity
  have hbound := hc.trans (mul_le_mul_of_nonneg_right hcoeff hnonneg)
  simpa only [s, Finset.sum_product, separatedSum, innerSum, mul_assoc] using hbound

/-- Exact finite square expansion: the diagonal is nonnegative and the
off-diagonal retains its complex signed coefficients. -/
theorem square_sum_diagonal {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 =
      (∑ i ∈ s, ‖f i‖ ^ 2) +
        (∑ i ∈ s, ∑ j ∈ s, if i ≠ j then f i * star (f j) else 0).re := by
  have hsplit : (∑ i ∈ s, ∑ j ∈ s, f i * star (f j)) =
      (∑ i ∈ s, f i * star (f i)) +
        ∑ i ∈ s, ∑ j ∈ s, if i ≠ j then f i * star (f j) else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hdiag : (∑ j ∈ s, if i = j then f i * star (f j) else 0) =
        f i * star (f i) := by simp [hi]
    rw [← hdiag, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j <;> simp [hij, eq_comm]
  have hsq : ((∑ i ∈ s, f i) * star (∑ i ∈ s, f i)).re =
      ‖∑ i ∈ s, f i‖ ^ 2 := by
    simpa only [Complex.star_def, ← Complex.ofReal_pow, Complex.ofReal_re] using
      congrArg Complex.re (Complex.mul_conj' (∑ i ∈ s, f i))
  rw [← hsq, star_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [hsplit]
  simp [Complex.mul_conj', ← Complex.ofReal_pow]


end Erdos821.S56Core
