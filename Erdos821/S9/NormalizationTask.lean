import Erdos821.Blueprint.Balanced

noncomputable section
open Filter
namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- Convert the aggregated sieve main term and power-saving error to the
frozen candidate mass. The comparison constant precedes jstar. -/
def BalancedNormalizationTask : Prop :=
  ∀ (hc : ClassicalInputs) (δ : ℝ) (C : CandidateData),
    C.Geometry δ → C.Bounds δ → ∀ A K : ℝ, 0 < K →
    ∃ K' : ℝ, 0 < K' ∧ ∀ jstar : ℕ, C.j₀ ≤ jstar →
      ∀ᶠ x : ℝ in atTop,
        K * (x * sieveProduct (W x) ^ 2 * sieveProduct (x ^ C.theta) *
                C.bands.harmonicQ x jstar * C.bands.harmonicP x +
            x ^ (0.64 : ℝ) * L x ^ A * C.bands.harmonicQ x jstar) ≤
          K' * C.mass x jstar * sieveProduct (W x) ^ 2

end Erdos821.S56Core
