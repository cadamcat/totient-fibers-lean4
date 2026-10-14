import Erdos821.S56.PureCoefficients
import Erdos821.S56.AllocatedFactors

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

abbrev ProcessedValue (D : BandData) (x : ℝ) (jstar : ℕ)
    (i : ProcessedIndex D x jstar) :=
  {p : ℕ // p ∈ D.band x (processedSlot D x jstar i).1.val}

def processedCoefficient (D : BandData) (x : ℝ) (jstar : ℕ)
    (delta : ProcessedIndex D x jstar → Bool) (take : Bool)
    (nu : ProcessedIndex D x jstar → ℝ) (v : ℕ) : ℂ :=
  productCoefficient (fun i : {i // delta i = take} => ProcessedValue D x jstar i.val)
    (fun _ p => p.val) (fun i p => Erdos821.Blueprint.Analytic.mellin p.val (nu i.val)) v

/-- Transport each selected processed-coordinate family to the subset of
literal slots in its image; PureSlotMultiplicityTask then supplies its bound. -/
def ProcessedCoefficientBoundTask : Prop :=
  PureSlotMultiplicityTask → ∀ D : BandData, D.Valid →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ jstar : ℕ,
      ∀ (delta : ProcessedIndex D x jstar → Bool) (take : Bool)
        (nu : ProcessedIndex D x jstar → ℝ) (v : ℕ),
        ‖processedCoefficient D x jstar delta take nu v‖ ≤ L x ^ C

/-- The finite, exact pre-Cauchy weight split. Coordinate restriction splits
the full slot list into the exceptional integer and two partial prime lists.
The product equation recovers the residual outside part, and the group-free
e factor preserves markWeight. No Fourier or asymptotic estimate is requested. -/
def SlotCoefficientSplitTask : Prop :=
  ∀ (D : BandData) (x : ℝ) (jstar : ℕ),
    jstar ≤ D.last x → 1 ≤ D.r₀ →
    (∀ j ≤ D.last x, ∀ g, Disjoint (D.band x j) ((D.groups x).primes g)) →
    (∀ p : ℕ, rough (W x) p → GroupFree (D.groups x) p) →
    ∀ (delta : ProcessedIndex D x jstar → Bool) (nu : ProcessedIndex D x jstar → ℝ)
      (u e : ℕ), 0 < u → 0 < e →
      (∑ z : D.Lists x jstar,
        if D.listProduct z = groupFreePart (D.groups x) u ∧ processedFactor D z delta = e then
          (markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u : ℂ) *
            ∏ i, Erdos821.Blueprint.Analytic.mellin (z (processedSlot D x jstar i)).val (nu i)
        else 0) =
      if e ∣ u then
        processedCoefficient D x jstar delta true nu e *
          (markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) (u / e) : ℂ) *
            roughCore x (Real.exp (D.c₁ * D.scale x jstar))
              (Real.exp (D.c₂ * D.scale x jstar)) 0
              (processedCoefficient D x jstar delta false nu)
              (groupFreePart (D.groups x) (u / e))
      else 0

end Erdos821.S56Core
