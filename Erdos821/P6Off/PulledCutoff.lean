import Erdos821.P6Off.Task

noncomputable section
open scoped BigOperators ContDiff
open Filter MeasureTheory

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- The exact smooth weights in logarithmic variables after determinant
reconstruction. The compact localization is fixed before all precisions. -/
def pulledCutoff (U V Z E : ℝ) (k : ℤ) (etae etan : ℝ → ℝ)
    (localizer : (Fin 3 → ℝ) → ℝ) (t : Fin 3 → ℝ) : ℂ :=
  let m := U * Real.exp (t 0)
  let m' := U * Real.exp (t 1)
  let z := Z * Real.exp (t 2)
  (localizer t * etae ((m' - m) / (2 * k * E)) *
    etan ((m' - m) * z / (k * m * m' * V) + 1 / (m * V)) : ℝ)

/-- Quantitative three-variable Fourier separation. All exponents and
constants are fixed before the tail saving A and before discrepancy B. -/
def PulledCutoffSeparationTask : Prop :=
  ClassicalInputs →
  ∀ (C K0 CZ R : ℝ) (bounds localBounds : ℕ → ℝ)
    (localizer : (Fin 3 → ℝ) → ℝ),
    0 < C → 0 < K0 → 0 < CZ → 0 < R →
    (∀ j, 0 ≤ bounds j ∧ 0 ≤ localBounds j) →
    ContDiff ℝ ∞ localizer →
    Function.support localizer ⊆ Metric.closedBall 0 R →
    (∀ j y, ‖iteratedFDeriv ℝ j localizer y‖ ≤ localBounds j) →
    ∃ Cf K : ℝ, 0 < Cf ∧ 0 < K ∧
      ∀ A : ℝ, 0 < A → ∃ KA : ℝ, 0 < KA ∧ ∀ᶠ x : ℝ in atTop,
        ∀ (U V Z : ℝ) (k : ℤ) (etae etan : ℝ → ℝ),
          1 ≤ U → 1 ≤ V → x / 8 ≤ U * V → U * V ≤ 8 * x →
          0 < Z → Z ≤ x * L x ^ CZ → k ≠ 0 →
          ContDiff ℝ ∞ etae → ContDiff ℝ ∞ etan →
          (∀ j y, ‖iteratedDeriv j etae y‖ ≤ bounds j * L x ^ (C * (j + 1)) ∧
            ‖iteratedDeriv j etan y‖ ≤ bounds j * L x ^ (C * (j + 1))) →
          ∃ a : (Fin 3 → ℝ) → ℂ,
            Integrable a ∧ (∫ ξ, ‖a ξ‖) ≤ L x ^ K ∧
            (∀ t, pulledCutoff U V Z (U * L x ^ (-K0)) k etae etan localizer t =
              ∫ ξ, a ξ * e (∑ i, ξ i * t i)) ∧
            (∫ ξ in {ξ : Fin 3 → ℝ | L x ^ Cf < ‖ξ‖}, ‖a ξ‖) ≤
              KA * L x ^ (-A)

end Erdos821.P6Off
