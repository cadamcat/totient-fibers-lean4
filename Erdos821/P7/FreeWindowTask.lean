import Erdos821.P7.FreeSlotMass
import Erdos821.P7.PrimeWindowTask
import Erdos821.P7.Pointwise

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

/-- The ordinary product tested against psi, averaged harmonically over
only the distinguished free slot. The complementary product remains literal. -/
def freeWindowKernel (C : CandidateData) (x : ℝ) (jstar : ℕ) (s : C.bands.Slot x)
    (v r : ℕ) : ℝ :=
  ∑ p : C.bands.SlotValue x jstar s,
    (p.val : ℝ)⁻¹ * ((p.val : ℝ) * v * r) * C.psi (((p.val : ℝ) * v * r) / x)

theorem freeWindowKernel_nonneg (C : CandidateData) (hpsi : ∀ y, 0 ≤ C.psi y)
    (x : ℝ) (jstar : ℕ) (s : C.bands.Slot x) (v r : ℕ) :
    0 ≤ freeWindowKernel C x jstar s v r := by
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)))
    (hpsi _)

/-- Bounded analytic conversion of a multiplicative prime-window estimate
and deterministic product placement into the candidate's free-slot kernel
bounds. This is a proof obligation; no proof is assumed.

Upper outline: take `B ≥ 1` from `P7Core.cutoff_bound`. A supported summand
has U in [x,2x], hence U*psi(U/x) ≤ 2*B*x, and its prime lies in [y,2y],
where y=x/(r*restProduct). If a supported summand exists, its membership
in Q0 gives y ≥ exp(c₁*s'*L)/2; this tends to infinity uniformly and gives
log y ≥ c₁*s'*L/2 eventually. Apply PrimeWindowHarmonicTask at a=1,b=2.
If no supported summand exists, the kernel is zero.

Lower outline: obtain epsilon,sigma from CandidatePlacementTask and a,b,c
from the geometry's positivity interval for psi. By free_slot_harmonic_bounds,
Q0 has a value, so restore any such value to a RestLists choice and transport
its prefix event using prefixMidpointEvent_restoreList. Placement and
outsideSlotProduct_restoreList put [a*y,b*y] inside Q0 when r≤x^sigma.
The lower endpoint gives y→∞ uniformly; the upper gives
log y ≤ c₂*s'*L (b>1). Every window prime contributes U*psi(U/x) ≥ c*x.
Apply PrimeWindowHarmonicTask at a,b and use the literal prime-set inclusion.

All constants and epsilon,sigma precede jstar. This task has no P harmonic
averaging, prefix-probability bound, HQ lower bound or candidate mass identity.
The two pending input tasks are explicit hypotheses of the statement. -/
def FreeWindowBoundsTask : Prop :=
  PrimeWindowHarmonicTask → CandidatePlacementTask → ClassicalInputs →
    ∀ (δ : ℝ) (C : CandidateData), C.Geometry δ →
      ∃ epsilon sigma kmin kmax : ℝ, 0 < epsilon ∧
        epsilon < (C.bands.c₂ - C.bands.c₁) / 4 ∧
        0 < sigma ∧ 0 < kmin ∧ 0 < kmax ∧
        ∀ jstar : ℕ, C.j₀ ≤ jstar → ∀ᶠ x : ℝ in atTop,
          ∀ s : C.bands.Slot x, s.1.val = 0 → s.2.val = 0 →
            ∀ z : RestLists C.bands x jstar s, ∀ r : ℕ, 0 < r →
              freeWindowKernel C x jstar s (restProduct C.bands z) r ≤ kmax * (x / L x) ∧
              (restPrefixEvent C epsilon s z → (r : ℝ) ≤ x ^ sigma →
                kmin * (x / L x) ≤ freeWindowKernel C x jstar s (restProduct C.bands z) r)

end Erdos821.P7Core

