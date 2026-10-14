import Erdos821.P7.Pointwise
import Erdos821.P7.Support

noncomputable section
open Filter

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- The remaining mass estimates, without repeating the already proved
pointwise and prime-factor support controls. No proof is assumed here. -/
def CandidateMassTask : Prop :=
  ClassicalInputs → ∀ (δ : ℝ) (C : CandidateData), C.Geometry δ →
    ∃ CA cmin cmax : ℝ, 0 < cmin ∧ 0 < cmax ∧
      ∀ jstar : ℕ, C.j₀ ≤ jstar → ∀ᶠ x : ℝ in atTop,
        x * L x ^ (-CA) ≤ C.mass x jstar ∧
        cmin * (x / L x) * C.bands.harmonicQ x jstar * C.bands.harmonicP x ≤ C.mass x jstar ∧
        C.mass x jstar ≤ cmax * (x / L x) * C.bands.harmonicQ x jstar * C.bands.harmonicP x

theorem candidate_bounds_of_massTask (hmass : CandidateMassTask) :
    Erdos821.Blueprint.candidate_bounds_statement := by
  intro hc δ C hC
  obtain ⟨CA, cmin, cmax, hmin, hmax, hm⟩ := hmass hc δ C hC
  obtain ⟨K, hK, hp⟩ := candidate_pointwise_bound δ C hC
  refine ⟨K, CA, cmin, cmax, hK, hmin, hmax, ?_⟩
  intro jstar hj
  filter_upwards [hm jstar hj, hp jstar, candidate_support_bounds δ C hC]
    with x hm hp hs
  exact ⟨hm.1, hm.2.1, hm.2.2, geometry_weighted_nonneg C δ hC x jstar,
    hp, hs jstar⟩

example (hmass : CandidateMassTask) : Erdos821.Blueprint.candidate_bounds_statement :=
  candidate_bounds_of_massTask hmass

end Erdos821.P7Core

