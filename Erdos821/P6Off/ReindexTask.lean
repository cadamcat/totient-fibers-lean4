import Erdos821.P6Off.Determinant

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

/-- Literal finite determinant reindexing before character orthogonality.
The generous z bound is algebraic; the cutoffs later give z = x L^{O(1)}. -/
def determinantSum (M N : ℕ) (E U V : ℝ) (etae etan : ℝ → ℝ)
    (ah alpha : ℕ → ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(M : ℤ)) M, ∑ z ∈ Finset.Icc 1 N,
    ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
      if k ≠ 0 ∧ 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat ∧
          Nat.ModEq (2 * k.natAbs) m m' then
        (etae (((m' : ℝ) - m) / (2 * k * E)) *
          etan (((m' : ℝ) - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ) *
          (alpha m * ah (z / m')) * star (alpha m' * ah (((z : ℤ) + k).toNat / m))
      else 0

/-- Only finite arithmetic is required. Nonzero alpha forces the rough
coprimality needed by the converse; support removes nonpositive e and n. -/
def OffDiagonalReindexTask : Prop :=
  ∀ (M : ℕ) (E U V emin y : ℝ) (etae etan : ℝ → ℝ) (ah alpha : ℕ → ℂ),
    0 < E → 1 ≤ U → 1 ≤ V → 0 < emin → U ≤ 2 * emin * M →
    (2 * M : ℝ) ≤ y → (∀ n, alpha n ≠ 0 → rough y n) →
    Function.support etae ⊆ Set.Icc (emin / E) 2 →
    Function.support etan ⊆ Set.Icc (1 / 2) 4 →
    offDiagonalSum E U V etae etan ah alpha =
      determinantSum M (⌈2 * U⌉₊ ^ 2 * ⌊4 * V⌋₊) E U V etae etan ah alpha

end Erdos821.P6Off
