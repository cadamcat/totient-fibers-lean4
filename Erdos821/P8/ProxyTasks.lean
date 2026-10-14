import Erdos821.Blueprint.Proxy

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core
open Blueprint Blueprint.Analytic

/-- Absolute-error residue-class sieve estimate, valid even on tiny subintervals.
Taking r = 1 also supplies the ordinary full-cell denominator estimate. -/
def RoughResidueIntervalTask : Prop :=
  ClassicalInputs → SieveInputs → ∀ b C B A eta : ℝ,
    0 < b → 0 < C → 0 < B → 0 < A → 0 < eta →
    ∀ᶠ x : ℝ in atTop, ∀ lo hi : ℝ, ∀ r a : ℕ,
      x ^ b ≤ lo → lo ≤ hi → hi ≤ x ^ C →
      1 ≤ r → (r : ℝ) ≤ L x ^ B → Nat.Coprime a r →
      |(((Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter
          (fun n => rough (W x) n ∧ n % r = a % r)).card : ℝ) -
        (hi - lo) * sieveProduct (W x) / (Nat.totient r : ℝ)| ≤
        (hi - lo) * sieveProduct (W x) / (Nat.totient r : ℝ) * L x ^ (-A) + x ^ eta

end Erdos821.P8Core
