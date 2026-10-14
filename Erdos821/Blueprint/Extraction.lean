import Erdos821.Blueprint.TypeII
import Erdos821.Blueprint.Balanced
import Erdos821.Supply

/-! P10: subtract unbalanced and balanced composites, then remove the weights. -/
noncomputable section
open scoped BigOperators
open Filter
namespace Erdos821.Blueprint
open Analytic

def PrimeExtraction (C : CandidateData) : Prop :=
  ∃ jstar : ℕ, C.j₀ ≤ jstar ∧ ∃ c : ℝ, 0 < c ∧
    ∀ᶠ x : ℝ in atTop, c * C.mass x jstar / L x ≤ C.primeMass x jstar

/-- P10 analytic boundary. Choose κ using P9, b₁ and jstar next, B next, S last. -/
abbrev prime_extraction_statement : Prop :=
  ∀ (_hc : ClassicalInputs) (_hs : SieveInputs)
    (_hii : TypeIIEstimate) (_hp : ProxyInputs) (δ : ℝ) (C : CandidateData)
    (_hC : C.Geometry δ) (_hb : C.Bounds δ) (_htI : C.TypeI)
    (_hbal : BalancedRoughBound C),
    PrimeExtraction C
-- `count_from_weighted_mass` is proved in `Erdos821/Count/Count.lean`.

end Erdos821.Blueprint
