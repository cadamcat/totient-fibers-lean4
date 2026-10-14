import Erdos821.S9.EulerTasks
import Erdos821.P9.PairSieveData

noncomputable section
open scoped BigOperators
open Filter
namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P9Core
attribute [local instance] Classical.propDecidable

def pairBudgetPrimes (C : CandidateData) (x : ℝ) (D : ℕ) : Finset ℕ :=
  (primesUpTo (x ^ C.theta)).filter fun p => 3 ≤ p ∧ ¬ p ∣ D

def pairBudgetData (C : CandidateData) (x M N : ℝ) (D : ℕ)
    (R : Finset ℕ) (hD : 0 < D) (allow : PermissionIndex R → Bool) :
    SieveData (ℕ × ℕ) :=
  pairSieveData ⌈M⌉₊ ⌈2 * M⌉₊ ⌈N⌉₊ ⌈2 * N⌉₊ D (W x)
    (groupPrimeSet (C.bands.groups x)) (permissionAllowed R allow)
    (pairBudgetPrimes C x D) hD (by
      intro p hp
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2)

/-- A single assignment's Boolean-mask sieve bound, with constants chosen
uniformly before the box, modulus, mask set and later rough-slot index. -/
def PairSieveBudgetTask : Prop :=
  ∀ (hc : ClassicalInputs) (hs : SieveInputs),
    DivisorCompensationTask → MaskHarmonicPTask →
    ∀ (δ : ℝ) (C : CandidateData), C.Geometry δ →
    ∃ A K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (M N : ℝ) (D : ℕ) (R : Finset ℕ) (hD : 0 < D),
        0 ≤ M → 0 ≤ N → M ≤ x ^ (0.54 : ℝ) → N ≤ x ^ (0.54 : ℝ) →
        (D : ℝ) ≤ x ^ (1 / 20 : ℝ) →
        (∀ p : ℕ, p.Prime → p ∣ D → L x ^ (20 : ℕ) ≤ (p : ℝ)) →
        R ⊆ groupPrimeSet (C.bands.groups x) →
        (∑ allow : PermissionIndex R → Bool,
          permissionMaskProbability R C.bands.geometry.q allow *
            (pairBudgetData C x M N D R hD allow).sifted) ≤
          K * (((((⌈2 * M⌉₊ - ⌈M⌉₊ : ℕ) : ℝ) *
                ((⌈2 * N⌉₊ - ⌈N⌉₊ : ℕ) : ℝ)) / D) *
              sieveProduct (W x) ^ 2 * sieveProduct (x ^ C.theta) *
                C.bands.harmonicP x +
            ((D : ℝ) * x ^ (0.1 : ℝ) + x ^ (0.59 : ℝ)) * L x ^ A)

end Erdos821.S56Core
