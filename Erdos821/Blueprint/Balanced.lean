import Erdos821.Blueprint.Proxy

/-! P9: a positive two-variable sieve bound whose constant precedes the gap. -/
noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable
namespace Erdos821.Blueprint
open Analytic

def balancedRoughSum (C : CandidateData) (x M N : ℝ) (jstar : ℕ) : ℝ :=
  ∑ m ∈ (Finset.Ico ⌈M⌉₊ ⌈2 * M⌉₊).filter (rough (W x)),
    ∑ n ∈ (Finset.Ico ⌈N⌉₊ ⌈2 * N⌉₊).filter (rough (W x)),
      if Odd (m * n) ∧ 1 < m * n then C.weighted x jstar ((m * n - 1) / 2) else 0

def BalancedRoughBound (C : CandidateData) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ jstar : ℕ, C.j₀ ≤ jstar →
    ∀ᶠ x : ℝ in atTop, ∀ M N : ℝ,
      x ^ (0.46 : ℝ) ≤ M → M ≤ x ^ (0.54 : ℝ) →
      x ^ (0.46 : ℝ) ≤ N → N ≤ x ^ (0.54 : ℝ) →
      balancedRoughSum C x M N jstar ≤ K * C.mass x jstar * sieveProduct (W x) ^ 2

/-- P9 boundary. K does not depend on κ,b₁,jstar,S or later analytic accuracies. -/
abbrev balanced_rough_bound_statement : Prop :=
  ∀ (_hc : ClassicalInputs) (_hs : SieveInputs)
    (δ : ℝ) (C : CandidateData) (_hC : C.Geometry δ) (_hb : C.Bounds δ),
    BalancedRoughBound C
end Erdos821.Blueprint
