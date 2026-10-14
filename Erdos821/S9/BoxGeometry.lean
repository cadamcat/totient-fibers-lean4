import Erdos821.Blueprint.Balanced

noncomputable section
open scoped BigOperators
namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem odd_product_index (m n : ℕ) (hodd : Odd (m * n)) :
    m * n = 2 * ((m * n - 1) / 2) + 1 := by
  rcases hodd with ⟨k, hk⟩
  omega

theorem balancedRoughSum_eq_zero_of_large_box
    (C : CandidateData) (x M N : ℝ) (jstar : ℕ)
    (hx : 1 ≤ x) (hM : 0 ≤ M) (hN : 0 ≤ N) (hbox : 5 * x < M * N)
    (hsupport : ∀ u : ℕ, C.weighted x jstar u ≠ 0 → (u : ℝ) ≤ 2 * x) :
    balancedRoughSum C x M N jstar = 0 := by
  classical
  unfold balancedRoughSum
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hp : Odd (m * n) ∧ 1 < m * n
  · rw [if_pos hp]
    by_contra hne
    have hu := hsupport _ hne
    have hmul := odd_product_index m n hp.1
    have hmulR : (m : ℝ) * n = 2 * (((m * n - 1) / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hmul
    have hmlo : M ≤ (m : ℝ) := (Nat.le_ceil M).trans (by
      exact_mod_cast (Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1).1)
    have hnlo : N ≤ (n : ℝ) := (Nat.le_ceil N).trans (by
      exact_mod_cast (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1)
    have hprod : M * N ≤ (m : ℝ) * n :=
      mul_le_mul hmlo hnlo hN (Nat.cast_nonneg m)
    nlinarith
  · simp only [if_neg hp]

theorem dyadic_nat_width_le (M : ℝ) (hM : 0 ≤ M) :
    ((⌈2 * M⌉₊ - ⌈M⌉₊ : ℕ) : ℝ) ≤ M + 1 := by
  have hceil : ⌈M⌉₊ ≤ ⌈2 * M⌉₊ := Nat.ceil_mono (by linarith)
  rw [Nat.cast_sub hceil]
  have hlo := Nat.le_ceil M
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 2 * M by linarith)
  linarith

theorem dyadic_area_le (x M N : ℝ) (hx : 1 ≤ x) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hprod : M * N ≤ 5 * x) :
    ((⌈2 * M⌉₊ - ⌈M⌉₊ : ℕ) : ℝ) * ((⌈2 * N⌉₊ - ⌈N⌉₊ : ℕ) : ℝ) ≤ 20 * x := by
  have hwidthM := dyadic_nat_width_le M (by linarith)
  have hwidthN := dyadic_nat_width_le N (by linarith)
  calc
    _ ≤ (M + 1) * (N + 1) := mul_le_mul hwidthM hwidthN
      (Nat.cast_nonneg _) (by linarith)
    _ ≤ (2 * M) * (2 * N) := mul_le_mul (by linarith) (by linarith)
      (by linarith) (by linarith)
    _ ≤ 20 * x := by nlinarith

end Erdos821.S56Core

