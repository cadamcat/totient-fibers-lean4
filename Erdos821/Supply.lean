import Mathlib

/-!
# The smooth shifted-prime supply

Theorem 1.2 of the source paper: for every fixed `0 < δ < 1/4`, at least `x ^ (1 - o(1))` primes
`p` with `2x < p ≤ 5x` have no prime factor of `p - 1` above `x ^ δ`.
-/

namespace Erdos821

open Filter

open scoped Classical in
/-- The primes `p` with `2x < p ≤ 5x` all of whose prime factors of `p - 1` are at most `x ^ δ`. -/
noncomputable def smoothShiftedPrimes (δ x : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊2 * x⌋₊ ⌊5 * x⌋₊).filter fun p =>
    p.Prime ∧ ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ x ^ δ

/-- Theorem 1.2 of the source, with `x ^ (1 - o(1))` written as: for every `σ > 0`, eventually at
least `x ^ (1 - σ)`. -/
def SmoothShiftedPrimeSupply : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 4 → ∀ σ : ℝ, 0 < σ →
    ∀ᶠ x : ℝ in atTop, x ^ (1 - σ) ≤ ((smoothShiftedPrimes δ x).card : ℝ)

end Erdos821
