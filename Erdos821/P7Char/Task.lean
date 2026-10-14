import Erdos821.P7TypeI.TypeI

noncomputable section
open scoped BigOperators
open Filter Erdos821.Blueprint.Analytic

namespace Erdos821.P7Char

open Erdos821.Blueprint

/-- The progression sum `∑_{u ≤ 2x, d ∣ 2u+1} w(u)`. -/
def progressionSum (C : CandidateData) (x : ℝ) (jstar d : ℕ) : ℝ :=
  ∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u + 1), C.weighted x jstar u

def NonprincipalTypeITask : Prop :=
  ∀ (_hc : ClassicalInputs) (δ : ℝ) (C : CandidateData), C.Geometry δ → C.Bounds δ →
    ∀ θ D : ℝ, θ < 1 / 2 → 0 < D →
      ∀ jstar : ℕ, C.j₀ ≤ jstar → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
        (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
          |progressionSum C x jstar d -
            Erdos821.P7B.coprimeMass C x jstar d / (Nat.totient d : ℝ)|) ≤
          K * (x * L x ^ (-D))

end Erdos821.P7Char
