import Erdos821.Blueprint.Proxy

noncomputable section
open scoped BigOperators
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

/-- Task: moving-boundary dominated convergence, including integer thresholds. -/
def DensityContinuityTask : Prop :=
  ContinuousOn (fun v : ℝ × ℝ => roughDensity v.1 v.2)
    {v | 0 < v.1 ∧ v.1 < v.2}

/-- Task: simplex partition by the minimum coordinate, with null ties. -/
def DensityIntegralTask : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 →
    (∫ a : ℝ in b..(1 / 2 : ℝ), roughDensity a (1 - a) / a) =
      roughDensity b 1 - 1

/-- Task: uniform prime-list counting limit on a compact parameter region.
The full real-endpoint cell convention is (Y, exp(delta) Y]. -/
def RoughCellDensityTask : Prop :=
  ClassicalInputs → ∀ b wMax gap S : ℝ,
    0 < b → 0 < wMax → 0 < gap → 0 < S →
    ∀ eps : ℝ, 0 < eps → ∀ᶠ x : ℝ in atTop, ∀ gamma w : ℝ,
      b ≤ gamma → gamma + gap ≤ w → w ≤ wMax →
      (((Finset.Ioc ⌊x ^ w⌋₊ ⌊Real.exp (L x ^ (-S)) * x ^ w⌋₊).filter
        (rough (x ^ gamma))).card : ℝ) ≤
        (roughDensity gamma w + eps) * L x ^ (-S) * x ^ w / L x

end Erdos821.P8Core
