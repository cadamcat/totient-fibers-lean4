import Erdos821.Blueprint.Proxy

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

/-- The actual-test branch of proxy discrepancy. Enumerate rough integers by
nondecreasing prime lists and use Siegel--Walfisz on the last prime interval,
then partial summation for the Mellin weight. This statement includes all
characters modulo a logarithmically bounded modulus, including imprimitive
ones, and the saving exponent A is independent of the twist/modulus bound B. -/
def ActualTestNonprincipalTask : Prop :=
  ClassicalInputs → ∀ b kappa B A : ℝ,
    0 < b → 0 < kappa → kappa < 1 / 50 → 0 < B → 0 < A →
    ∀ᶠ x : ℝ in atTop, ∀ (I : FactorTest) (lo hi u : ℝ) (r : ℕ)
      (chi : DirichletCharacter ℂ r),
      TestAllowed b kappa I → x ^ (b / 4) ≤ lo → lo ≤ hi → hi ≤ x ^ (2 : ℕ) →
      1 ≤ r → (r : ℝ) ≤ L x ^ B → chi ≠ 1 → |u| ≤ L x ^ B →
      ‖∑ n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊,
        (test I x n : ℂ) * chi (n : ZMod r) * mellin n u / (n : ℂ)‖ ≤ L x ^ (-A)

end Erdos821.P8Core
