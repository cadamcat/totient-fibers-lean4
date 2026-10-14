import Erdos821.P6Off.Task

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- Absolute control for Fourier tails; the twists and slot interval need
no size bounds because their modulus and indicator are at most one. -/
def EndpointSquareTask : Prop :=
  ClassicalInputs → ∀ (P : Geometry) (C : ℝ), 0 < C →
    ∃ C' K : ℝ, 0 < C' ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (F : Endpoint) (N : ℕ),
        Admissible P x G → (N : ℝ) ≤ x ^ (2 : ℕ) →
        (∀ n, ‖F.alpha n‖ ≤ L x ^ C ∧ ‖F.residual n‖ ≤ L x ^ C) →
        (∑ n ∈ Finset.Icc 1 N,
          ‖endpoint G x F n * (markWeight G P.q (fun _ => P.ell) n : ℂ)‖ ^ 2) ≤
            K * N * L x ^ C'

end Erdos821.P6Off
