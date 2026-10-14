import Erdos821.P7.PlacementTask

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- The fixed prefix event retains a fixed fraction of the Q harmonic
measure, independently of the rough slot in the tail. No proof is assumed.

Proof outline: each prefix coordinate other than the chosen free slot has
its value restricted to the prime interval with log endpoints
`((c₁+c₂)/2 ± epsilon)*scale`. The epsilon assumptions put these endpoints
strictly inside its band. A sharp Mertens interval estimate gives a fixed
positive reciprocal mass for this smaller interval. The accepted uniform
band harmonic upper bound gives a fixed upper mass for the full prime slot.
Their ratio is a fixed positive constant. Every such coordinate is a pure
prime slot because `jstar ≥ j₀ > prefixLen`.

Use finite product-sum factorization to express the event sum as a product
of the restricted slot masses and all remaining unrestricted masses. Bound
the number of restricted coordinates by `r₀*(prefixLen+1)`, a fixed number;
replace each ratio by its minimum with one. The factorial normalization is
absent from both sides and cancels in the consuming probability inequality.
The free coordinate is unrestricted, as are all tail coordinates.

Reuse a sharp Mertens interval lemma from the P7Band or Q-lower helper when
available. This task concerns neither product placement nor P mass nor the
PNT free-slot window estimate. -/
def PrefixHarmonicTask : Prop :=
  ClassicalInputs → ∀ (δ : ℝ) (C : CandidateData), C.Geometry δ →
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < (C.bands.c₂ - C.bands.c₁) / 4 →
      ∃ c : ℝ, 0 < c ∧ ∀ jstar : ℕ, C.j₀ ≤ jstar → ∀ᶠ x : ℝ in atTop,
        ∀ s : C.bands.Slot x, s.1.val = 0 → s.2.val = 0 →
          c * (∑ z : C.bands.Lists x jstar, (C.bands.listProduct z : ℝ)⁻¹) ≤
            ∑ z : C.bands.Lists x jstar,
              if prefixMidpointEvent C epsilon s z then (C.bands.listProduct z : ℝ)⁻¹
              else 0

end Erdos821.P7Core
