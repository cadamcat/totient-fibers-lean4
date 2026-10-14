import Erdos821.P8.ProxyTasks

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P8Core

/-- A tail with an available final factor in a bounded interval uses only bounded labels.
This exact identity permits arbitrary positive label sets in the finite-grid argument. -/
def TailRestrictionTask : Prop :=
  ∀ I P : Finset ℕ, ∀ M k : ℕ,
    (∀ p ∈ P, 1 ≤ p) → (∀ n ∈ I, n ≤ M) → ∀ F : ℕ → ℝ,
    let Q := P.filter (fun p => p ≤ M)
    (∑ f : Fin k → {p : ℕ // p ∈ P},
      if (∃ q ∈ P, q * (∏ i, (f i).val) ∈ I)
      then F (∏ i, (f i).val) else 0) =
    (∑ f : Fin k → {p : ℕ // p ∈ Q},
      if (∃ q ∈ Q, q * (∏ i, (f i).val) ∈ I)
      then F (∏ i, (f i).val) else 0)

end Erdos821.P8Core
