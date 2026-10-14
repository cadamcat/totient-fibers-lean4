import Erdos821.S56.Separated

noncomputable section
open Filter
open scoped ContDiff

namespace Erdos821.S56Core
open Erdos821.Blueprint.Analytic

/-- The §5 Cauchy majorants. Only the lower e edge moves, by L^(-Cs),
so every derivative costs a fixed power of L per order. Cs and all these
costs are fixed before K₀. A scaled smoothTransition construction suffices. -/
def DyadicMajorantsTask : Prop :=
  ∀ Cs : ℝ, 0 < Cs → ∃ C : ℝ, 0 < C ∧ ∃ bounds : ℕ → ℝ,
    (∀ j, 0 ≤ bounds j) ∧ ∀ᶠ x : ℝ in atTop,
      ∃ etae etan : ℝ → ℝ,
        ContDiff ℝ ∞ etae ∧ ContDiff ℝ ∞ etan ∧
        Function.support etae ⊆ Set.Icc (L x ^ (-Cs) / 2) 2 ∧
        Function.support etan ⊆ Set.Icc (1 / 2) 4 ∧
        (∀ y, 0 ≤ etae y ∧ etae y ≤ 1 ∧ 0 ≤ etan y ∧ etan y ≤ 1) ∧
        (∀ y ∈ Set.Icc (L x ^ (-Cs)) 1, etae y = 1) ∧
        (∀ y ∈ Set.Icc 1 2, etan y = 1) ∧
        ∀ j y, ‖iteratedDeriv j etae y‖ ≤ bounds j * L x ^ (C * (j + 1)) ∧
          ‖iteratedDeriv j etan y‖ ≤ bounds j * L x ^ (C * (j + 1))

end Erdos821.S56Core
