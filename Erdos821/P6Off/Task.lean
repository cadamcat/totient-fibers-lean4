import Erdos821.S56.Separated

noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

/-- The post-Cauchy half of §5. K₀ is fixed data here. Exact signed determinant
reconstruction, character congruence, and Fourier separation in log m, log m',
log z turn this literal off-diagonal sum into ShiftEstimate correlations.
All cutoff derivative constants and powers are fixed before B. -/
def OffDiagonalShiftTask : Prop :=
  ClassicalInputs → ShiftEstimate →
  ∀ (P : Geometry) (A b C Cs K0 tau eta : ℝ) (bounds : ℕ → ℝ),
    0 < A → 0 < b → 0 < C → 0 < Cs → 0 < K0 →
    0 < tau → tau < eta → eta < 1 / 4 → eta < b / 4 →
    (∀ j, 0 ≤ bounds j) →
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (U V lo hi rho sigma : ℝ)
        (c alpha : ℕ → ℂ) (etae etan : ℝ → ℝ),
        Admissible P x G → x / 8 ≤ U * V → U * V ≤ 8 * x →
        x ^ b ≤ U → U ≤ x ^ (1 - b) → x ^ b ≤ V → V ≤ x ^ (1 - b) →
        x ^ tau ≤ lo → lo ≤ hi → hi ≤ x ^ eta →
        |rho| ≤ L x ^ C → |sigma| ≤ L x ^ C →
        (∀ n, ‖alpha n‖ ≤ L x ^ C ∧ ‖c n‖ ≤ L x ^ C) →
        (∀ n, alpha n ≠ 0 → rough (W x) n) →
        discrepancy x B (restricted U alpha) →
        ContDiff ℝ ∞ etae → ContDiff ℝ ∞ etan →
        Function.support etae ⊆ Set.Icc (L x ^ (-Cs) / 2) 2 →
        Function.support etan ⊆ Set.Icc (1 / 2) 4 →
        (∀ j y, ‖iteratedDeriv j etae y‖ ≤ bounds j * L x ^ (C * (j + 1)) ∧
          ‖iteratedDeriv j etan y‖ ≤ bounds j * L x ^ (C * (j + 1))) →
        ‖offDiagonalSum (U * L x ^ (-K0)) U V etae etan
          (hCoefficient P G x lo hi rho sigma c) alpha‖ ≤ K * x * L x ^ (-A)


example : OffDiagonalShiftTask = Erdos821.S56Core.OffDiagonalShiftTask := rfl

end Erdos821.P6Off
