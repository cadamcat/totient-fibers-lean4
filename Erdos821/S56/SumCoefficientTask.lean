import Erdos821.S56.CoefficientSplit

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core

/-- The coordinate family over a disjoint sum is finite in each fiber. -/
abbrev sumCoordinateFintype {ι κ : Type} (A : ι → Type) (B : κ → Type)
    [∀ i, Fintype (A i)] [∀ j, Fintype (B j)] (s : ι ⊕ κ) :
    Fintype (Sum.elim A B s) := by
  cases s with
  | inl i =>
      change Fintype (A i)
      infer_instance
  | inr j =>
      change Fintype (B j)
      infer_instance

attribute [local instance] sumCoordinateFintype

/-- Direct convolution for a sum of coordinate types. This avoids transporting
the positive and negative subtype fibers in `product_coefficient_split`. -/
def SumCoefficientTask : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : ι → Type) (B : κ → Type) [∀ i, Fintype (A i)] [∀ j, Fintype (B j)]
    (valA : ∀ i, A i → ℕ) (valB : ∀ j, B j → ℕ)
    (weightA : ∀ i, A i → ℂ) (weightB : ∀ j, B j → ℂ),
    (∀ i a, 0 < valA i a) → (∀ j b, 0 < valB j b) → ∀ t : ℕ,
      productCoefficient (Sum.elim A B)
        (fun i => match i with
          | Sum.inl a => valA a
          | Sum.inr b => valB b)
        (fun i => match i with
          | Sum.inl a => weightA a
          | Sum.inr b => weightB b) t =
      ∑ pr ∈ t.divisorsAntidiagonal,
        productCoefficient A valA weightA pr.1 * productCoefficient B valB weightB pr.2

end Erdos821.S56Core
