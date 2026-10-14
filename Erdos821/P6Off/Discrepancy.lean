import Erdos821.P6Off.Task

noncomputable section
open scoped BigOperators

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

theorem discrepancy_mono (x B B' : ℝ) (hx : 1 ≤ L x) (hB : B ≤ B')
    (a : ℕ → ℂ) (ha : discrepancy x B' a) : discrepancy x B a := by
  intro lo hi u r χ hlo hI hhi hr hrbound hu
  have hp : L x ^ B ≤ L x ^ B' := Real.rpow_le_rpow_of_exponent_le hx hB
  exact (ha lo hi u r χ hlo hI hhi hr (hrbound.trans hp) (hu.trans hp)).trans
    (Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hB))

theorem restricted_bound (U M : ℝ) (a : ℕ → ℂ) (hM : 0 ≤ M)
    (ha : ∀ n, ‖a n‖ ≤ M) : ∀ n, ‖restricted U a n‖ ≤ M := by
  intro n
  unfold restricted
  split_ifs
  · exact ha n
  · simpa using hM

theorem restricted_rough (U y : ℝ) (a : ℕ → ℂ)
    (ha : ∀ n, a n ≠ 0 → rough y n) :
    ∀ n, restricted U a n ≠ 0 → rough y n := by
  intro n hn
  unfold restricted at hn
  split_ifs at hn with h
  · exact ha n hn
  · exact False.elim (hn rfl)

theorem mem_dyad_iff (U : ℝ) (m : ℕ) :
    m ∈ dyad U ↔ U ≤ (m : ℝ) ∧ (m : ℝ) < 2 * U := by
  simp [dyad, Nat.ceil_le, Nat.lt_ceil]

theorem restricted_eq_on_dyad (U : ℝ) (a : ℕ → ℂ) (m : ℕ) (hm : m ∈ dyad U) :
    restricted U a m = a m := by
  exact if_pos ((mem_dyad_iff U m).mp hm)


end Erdos821.P6Off
