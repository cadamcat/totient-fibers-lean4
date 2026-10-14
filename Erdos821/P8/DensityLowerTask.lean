import Erdos821.Blueprint.Proxy

noncomputable section
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

/-- The lower-count limit used to compare the simplex density with the block sieve. -/
def RoughDyadicDensityLowerTask : Prop :=
  ClassicalInputs → ∀ b : ℝ, 0 < b → b < 1 →
    ∀ eps : ℝ, 0 < eps → ∀ᶠ x : ℝ in atTop,
      roughDensity b 1 - eps ≤ L x / x *
        (((Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter (rough (x ^ b))).card : ℝ)

end Erdos821.P8Core
