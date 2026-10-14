import Erdos821.Blueprint.Classical

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint

/-- The free Q₀ prime must hit a fixed multiplicative window. This is the
PNT input to the upper and lower local candidate mass comparisons.

Proof outline: specialize `PrimeProgressions` to `A=3`, `C=1`, modulus
`r=1`, residue `0`. For the lower count use primes in `(a*y,b*y]`, a
subset of the displayed closed interval. The difference of the two
logarithmic integrals is at least `(b-a)*y/log(b*y)` once `a*y >= 2`;
the logarithmic errors are eventually less than half this main term.
Divide that count by `b*y` for a lower reciprocal mass. For the upper
mass divide the total prime count up to `b*y` by `a*y`, using PNT and
an upper bound for `li`. Fixed endpoint logarithms are comparable to
`log y`. No prime groups, candidate weights, or smooth cutoffs enter
this task. Its constants and threshold may depend on `a,b`. -/
def PrimeWindowHarmonicTask : Prop :=
  ClassicalInputs → ∀ a b : ℝ, 0 < a → a < b →
    ∃ cmin cmax : ℝ, 0 < cmin ∧ 0 < cmax ∧ ∀ᶠ y : ℝ in atTop,
      cmin / Real.log y ≤
        (∑ p ∈ (Finset.Icc ⌈a * y⌉₊ ⌊b * y⌋₊).filter Nat.Prime, (p : ℝ)⁻¹) ∧
      (∑ p ∈ (Finset.Icc ⌈a * y⌉₊ ⌊b * y⌋₊).filter Nat.Prime, (p : ℝ)⁻¹) ≤
        cmax / Real.log y

end Erdos821.P7Core
