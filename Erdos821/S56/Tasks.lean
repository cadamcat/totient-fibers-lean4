import Erdos821.Blueprint.TypeII

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- The exceptional slot is fixed first as a divisor. Pure-prime slots in
each disjoint band have at most r₀! orderings, cancelled by the normalization.
This is §5, equation typeii-weight-bounds, first assertion. -/
def SlotMultiplicityTask : Prop :=
  ∀ D : BandData, D.Valid → ∀ jstar : ℕ, ∀ᶠ x : ℝ in atTop,
    ∀ v : ℕ, D.aQ x jstar v ≤ (v.divisors.card : ℝ)

/-- Finite tilted marked harmonic mass, uniform in the truncation N. The
one-group Euler expansion uses aₚ=(p^(1-θ)-1)⁻¹, θ=L^(-d), aₚ≤2e/p;
the product over O(T) groups is a fixed power of L. This avoids a summability
obligation in the consuming Type II tail argument. -/
def TiltedGroupMassTask : Prop :=
  ∀ P : Geometry, ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
    ∀ G : PrimeGroups, Admissible P x G → ∀ N : ℕ,
      (∑ v ∈ Finset.Icc 1 N,
        if groupFreePart G v = 1 then
          markWeight G P.q (fun _ => P.ell) v /
            (v : ℝ) ^ (1 - L x ^ (-P.d))
        else 0) ≤ L x ^ C

end Erdos821.S56Core
