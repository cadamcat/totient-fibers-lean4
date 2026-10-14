import Erdos821.Blueprint.Candidate

noncomputable section
open Filter

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def HarmonicQLowerTask : Prop :=
  ClassicalInputs → ∀ (D : BandData), D.Valid →
    ∃ C : ℝ, 0 < C ∧ ∀ jstar : ℕ, ∀ᶠ x : ℝ in atTop,
      L x ^ (-C) ≤ D.harmonicQ x jstar

end Erdos821.P7Core
