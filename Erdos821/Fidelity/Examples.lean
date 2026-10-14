import Mathlib
import Erdos821.Challenge
import Erdos821.Supply
import Erdos821.Fidelity.FormalConjectures

/-!
# Non-vacuity probes for the target and the supply interface

Kernel-checked evaluations of `Erdos821.g` on small values, instances of the predicate inside
`Erdos821.Statement` that hold and that fail, and concrete members and a non-member of
`Erdos821.smoothShiftedPrimes`.
-/

namespace Erdos821.Fidelity.Examples

open Erdos821

/-- For `n ≥ 1` and `B` at least the bound of `Source.fiber_bound`, the fiber of `n` is a filter of
`[1, B]`. -/
theorem fiber_eq_filter {n B : ℕ} (hn : 1 ≤ n) (hB : n * ∏ p ∈ Finset.Icc 1 (n + 1), p ≤ B) :
    {m : ℕ | Nat.totient m = n} = ↑((Finset.Icc 1 B).filter fun m => Nat.totient m = n) := by
  ext m
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_Icc]
  constructor
  · intro h
    have hb := Source.fiber_bound hn h
    exact ⟨⟨hb.1, hb.2.trans hB⟩, h⟩
  · exact fun h => h.2

/-- So `g n` is the size of that filter, which the kernel can evaluate. -/
theorem g_eq_card_filter {n B : ℕ} (hn : 1 ≤ n) (hB : n * ∏ p ∈ Finset.Icc 1 (n + 1), p ≤ B) :
    g n = ((Finset.Icc 1 B).filter fun m => Nat.totient m = n).card := by
  rw [g, fiber_eq_filter hn hB, Set.ncard_coe_finset]

/-! ## `g` on small values -/

/-- `φ m = 0` only for `m = 0`: the project's `g 0` is `1` (the source does not use `n = 0`). -/
example : g 0 = 1 := Source.project_g_zero

/-- `φ m = 1` for `m ∈ {1, 2}`. -/
example : g 1 = 2 := by
  rw [g_eq_card_filter (B := 2) le_rfl (by decide)]
  decide +kernel

/-- `φ m = 2` for `m ∈ {3, 4, 6}`. -/
example : g 2 = 3 := by
  rw [g_eq_card_filter (B := 12) (by norm_num) (by decide)]
  decide +kernel

/-- `3` is not a value of `φ`. -/
example : g 3 = 0 := by
  rw [g_eq_card_filter (B := 72) (by norm_num) (by decide)]
  decide +kernel

/-- `φ m = 4` for `m ∈ {5, 8, 10, 12}`. -/
theorem g_four : g 4 = 4 := by
  rw [g_eq_card_filter (B := 480) (by norm_num) (by decide)]
  decide +kernel

/-- The fiber itself, not only its size. -/
example : {m : ℕ | Nat.totient m = 4} = {5, 8, 10, 12} := by
  rw [fiber_eq_filter (B := 480) (by norm_num) (by decide)]
  have h : ((Finset.Icc 1 480).filter fun m => Nat.totient m = 4) = {5, 8, 10, 12} := by
    decide +kernel
  rw [h]
  simp

/-! ## The predicate of `Statement` on concrete `n` -/

/-- With `ε = 1/2`, `n = 4` satisfies `g n > n ^ (1 - ε)`: `4 > 4 ^ (1/2) = 2`. -/
example : (4 : ℕ) ∈ {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - (1 / 2 : ℝ))} := by
  show ((g 4 : ℕ) : ℝ) > ((4 : ℕ) : ℝ) ^ (1 - (1 / 2 : ℝ))
  rw [g_four]
  have h : ((4 : ℕ) : ℝ) ^ (1 - (1 / 2 : ℝ)) = 2 := by
    rw [show (1 : ℝ) - 1 / 2 = ((2 : ℕ) : ℝ)⁻¹ by norm_num, show ((4 : ℕ) : ℝ) = (2 : ℝ) ^ (2 : ℕ) by
      norm_num, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
  rw [h]; norm_num

/-- For every `ε`, `n = 3` fails the predicate: `g 3 = 0 < 3 ^ (1 - ε)`. -/
example (ε : ℝ) : (3 : ℕ) ∉ {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)} := by
  have h3 : g 3 = 0 := by
    rw [g_eq_card_filter (B := 72) (by norm_num) (by decide)]
    decide +kernel
  simp only [Set.mem_ofPred_eq, h3, Nat.cast_zero, gt_iff_lt, not_lt]
  positivity

/-! ## The supply interface -/

/-- The floors in `smoothShiftedPrimes` encode exactly `2x < p ≤ 5x` for `x ≥ 0`. -/
theorem mem_smoothShiftedPrimes_iff {δ x : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ smoothShiftedPrimes δ x ↔
      p.Prime ∧ 2 * x < p ∧ (p : ℝ) ≤ 5 * x ∧
        ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ x ^ δ := by
  simp only [smoothShiftedPrimes, Finset.mem_filter, Finset.mem_Ioc]
  rw [Nat.floor_lt (by positivity), Nat.le_floor_iff (by positivity)]
  tauto

/-- Every prime factor of `2 ^ a * 3 ^ b` is `2` or `3`. -/
private theorem prime_dvd_two_three {q a b : ℕ} (hq : q.Prime) (h : q ∣ 2 ^ a * 3 ^ b) :
    q ≤ 3 := by
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h) ▸ by norm_num
  · exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h) ▸ le_rfl

/-- `257 = 2 ^ 8 + 1` is in the supply set for `δ = 1/6`, `x = 64`: `128 < 257 ≤ 320`, and the only
prime factor of `256` is `2 = 64 ^ (1/6)`. -/
example : 257 ∈ smoothShiftedPrimes (1 / 6) 64 := by
  rw [mem_smoothShiftedPrimes_iff (by norm_num)]
  have hx : (64 : ℝ) ^ (1 / 6 : ℝ) = 2 := by
    rw [show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num, show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num,
      Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
  refine ⟨by norm_num, by norm_num, by norm_num, fun q hq hdvd => ?_⟩
  rw [hx]
  have : q ≤ 3 := prime_dvd_two_three (a := 8) (b := 0) hq (by simpa using hdvd)
  have h2 : q = 2 := by
    interval_cases q
    · exact absurd hq Nat.not_prime_zero
    · exact absurd hq Nat.not_prime_one
    · rfl
    · exact absurd hdvd (by decide)
  subst h2; norm_num

/-- `487 = 2 * 3 ^ 5 + 1` is in the supply set for `δ = 1/5`, `x = 243`: `486 < 487 ≤ 1215`, and the
prime factors `2, 3` of `486` are at most `243 ^ (1/5) = 3`. -/
example : 487 ∈ smoothShiftedPrimes (1 / 5) 243 := by
  rw [mem_smoothShiftedPrimes_iff (by norm_num)]
  have hx : (243 : ℝ) ^ (1 / 5 : ℝ) = 3 := by
    rw [show (1 / 5 : ℝ) = ((5 : ℕ) : ℝ)⁻¹ by norm_num, show (243 : ℝ) = 3 ^ (5 : ℕ) by norm_num,
      Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
  refine ⟨by norm_num, by norm_num, by norm_num, fun q hq hdvd => ?_⟩
  rw [hx]
  exact_mod_cast prime_dvd_two_three (a := 1) (b := 5) hq (by simpa using hdvd)

/-- The smoothness condition bites: `131` is prime and in `(128, 320]`, but `5 ∣ 130` and
`5 > 2 = 64 ^ (1/6)`. -/
example : 131 ∉ smoothShiftedPrimes (1 / 6) 64 := by
  rw [mem_smoothShiftedPrimes_iff (by norm_num)]
  have hx : (64 : ℝ) ^ (1 / 6 : ℝ) = 2 := by
    rw [show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num, show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num,
      Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
  rintro ⟨-, -, -, h⟩
  have := h 5 (by norm_num) (by norm_num)
  rw [hx] at this
  norm_num at this

end Erdos821.Fidelity.Examples
