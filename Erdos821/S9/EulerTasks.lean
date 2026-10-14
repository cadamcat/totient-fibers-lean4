import Erdos821.P9.GlobalMarks
import Erdos821.P9.PermissionMask
import Erdos821.P9.PairEulerProduct

noncomputable section
open scoped BigOperators
open Filter
namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P9Core

def permissionAllowed (P : Finset ℕ) (allow : PermissionIndex P → Bool) : Finset ℕ :=
  (P.attach.filter fun p => allow p = true).image Subtype.val

/-- Uniform compensation for the prime divisors of a small assignment modulus. -/
def DivisorCompensationTask : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, ∀ (D : ℕ) (z : ℝ),
    0 < D → (D : ℝ) ≤ x ^ (1 / 20 : ℝ) →
    (∀ p : ℕ, p.Prime → p ∣ D → L x ^ (20 : ℕ) ≤ (p : ℝ)) →
    (∏ p ∈ primesUpTo z, pairDComp p D) ≤ K

/-- Average the actual Boolean permission masks used by the pair sieve.
The set R may omit marked primes; D may remove further local factors. -/
def MaskHarmonicPTask : Prop :=
  ∀ (δ : ℝ) (C : CandidateData), C.Geometry δ →
    ∀ᶠ x : ℝ in atTop, ∀ (R : Finset ℕ) (D : ℕ) (z : ℝ),
      R ⊆ groupPrimeSet (C.bands.groups x) →
      (∑ allow : PermissionIndex R → Bool,
        permissionMaskProbability R C.bands.geometry.q allow *
          ∏ p ∈ primesUpTo z, pairAComp p D (permissionAllowed R allow)) ≤
        C.bands.harmonicP x

end Erdos821.S56Core
