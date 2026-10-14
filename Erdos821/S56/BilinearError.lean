import Erdos821.S56.AbsoluteMass

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def weightedBilinear (D : BandData) (x : ℝ) (jstar : ℕ) (U V : ℝ)
    (F a b : ℕ → ℂ) : ℂ :=
  ∑ m ∈ dyad U, ∑ n ∈ dyad V,
    if Odd (m*n) ∧ 1 < m*n then
      (D.weight x jstar ((m*n-1)/2) : ℂ)*F ((m*n-1)/2)*a m*b n else 0

theorem typeII_as_weighted_bilinear (D : BandData) (x : ℝ) (jstar : ℕ) (U V : ℝ)
    (psi : ℝ → ℝ) (a b : ℕ → ℂ) :
    typeIISum D x jstar U V psi a b =
      weightedBilinear D x jstar U V (fun u => (psi ((u:ℝ)/x) : ℂ)) a b := by
  simp only [typeIISum, weightedBilinear, dyad, Complex.ofReal_mul]

/-- Pointwise Fourier errors are summed before Cauchy. The total loss is
exactly the absolute weighted pair mass times the two coefficient bounds. -/
theorem weighted_bilinear_stability (D : BandData) (x : ℝ) (jstar : ℕ) (U V eps M : ℝ)
    (F H a b : ℕ → ℂ) (heps : 0 ≤ eps) (hM : 0 ≤ M)
    (hFH : ∀ u, ‖F u-H u‖ ≤ eps) (ha : ∀ m, ‖a m‖ ≤ M) (hb : ∀ n, ‖b n‖ ≤ M) :
    ‖weightedBilinear D x jstar U V F a b - weightedBilinear D x jstar U V H a b‖ ≤
      eps*M^2*weightedPairMass D x jstar U V := by
  have heq : weightedBilinear D x jstar U V F a b - weightedBilinear D x jstar U V H a b =
      ∑ m ∈ dyad U, ∑ n ∈ dyad V,
        if Odd (m*n) ∧ 1 < m*n then
          (D.weight x jstar ((m*n-1)/2) : ℂ)*(F ((m*n-1)/2)-H ((m*n-1)/2))*a m*b n else 0 := by
    simp only [weightedBilinear, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> ring
  rw [heq]
  calc
    _ ≤ ∑ m ∈ dyad U, ∑ n ∈ dyad V,
        ‖if Odd (m*n) ∧ 1 < m*n then
          (D.weight x jstar ((m*n-1)/2) : ℂ)*(F ((m*n-1)/2)-H ((m*n-1)/2))*a m*b n else 0‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ m ∈ dyad U, ∑ n ∈ dyad V,
        eps*M^2*(if Odd (m*n) ∧ 1 < m*n then D.weight x jstar ((m*n-1)/2) else 0) := by
      apply Finset.sum_le_sum
      intro m _
      apply Finset.sum_le_sum
      intro n _
      split_ifs
      · have hw := band_weight_nonneg D x jstar ((m*n-1)/2)
        have h1 := mul_le_mul (hFH ((m*n-1)/2)) (ha m) (norm_nonneg _) heps
        have h2 := mul_le_mul h1 (hb n) (norm_nonneg _) (mul_nonneg heps hM)
        have h3 := mul_le_mul_of_nonneg_left h2 hw
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw,
          pow_two, mul_assoc, mul_comm, mul_left_comm] using h3
      · simp
    _ = _ := by simp only [weightedPairMass, Finset.mul_sum]


end Erdos821.S56Core
