import Erdos821.P6Off.AbsoluteTask
import Erdos821.S56.Separated

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P6Off
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.S56Core

/-- Absolute Fourier-error mass on one dyad, after dropping congruence. -/
def absoluteDeterminantDyad (P : Geometry) (G : PrimeGroups) (x U Z lo hi rho sigma : ℝ)
    (N : ℕ) (k : ℤ) (psi : ℝ → ℝ) (c alpha : ℕ → ℂ) : ℝ :=
  ∑ z ∈ Finset.Icc 1 N, ∑ m ∈ dyad U, ∑ m' ∈ dyad U,
    if 0 < (z : ℤ) + k ∧ m' ∣ z ∧ m ∣ ((z : ℤ) + k).toNat then
      ‖(psi (z / Z) : ℂ) *
        (alpha m * hCoefficient P G x lo hi rho sigma c (z / m')) *
          star (alpha m' * hCoefficient P G x lo hi rho sigma c (((z : ℤ) + k).toNat / m))‖
    else 0

/-- Endpoint square sums control every Fourier tail on a fixed dyad. The
absolute endpoints use norm(alpha), norm(c), trivial character and zero twists.
Both z and z+k lie below floor(3Z), even if the original truncation N is larger. -/
def AbsoluteDeterminantDyadTask : Prop :=
  ClassicalInputs → EndpointSquareTask → ∀ (P : Geometry) (C : ℝ), 0 < C →
    ∃ C' K : ℝ, 0 < C' ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (U Z lo hi rho sigma : ℝ)
        (N : ℕ) (k : ℤ) (psi : ℝ → ℝ) (c alpha : ℕ → ℂ),
        Admissible P x G → 0 < U → 1 ≤ Z → 3 * Z ≤ x ^ (2 : ℕ) →
        |(k : ℝ)| ≤ Z →
        Function.support psi ⊆ Set.Icc (1 / 2) 2 → (∀ t, |psi t| ≤ 1) →
        (∀ n, ‖alpha n‖ ≤ L x ^ C ∧ ‖c n‖ ≤ L x ^ C) →
        (∀ n, alpha n ≠ 0 → rough (W x) n) →
        absoluteDeterminantDyad P G x U Z lo hi rho sigma N k psi c alpha ≤
          K * Z * L x ^ C'

end Erdos821.P6Off
