import Erdos821.S56.Tasks

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint

abbrev PureLists (D : BandData) (x : ℝ) (S : Finset (D.Slot x)) :=
  (s : S) → {p : ℕ // p ∈ D.band x s.val.1.val}

def pureListProduct (D : BandData) (x : ℝ) (S : Finset (D.Slot x))
    (z : PureLists D x S) : ℕ := ∏ s : S, (z s).val

/-- The same prime multiplicity/permutation argument needed for aQ also
bounds every partial pure-prime coefficient after a fixed allocation pattern.
The subset S carries labelled slots and may omit any number from each band.
This is §5, typeii-separated-coefficients, a_e and c_r. -/
def PureSlotMultiplicityTask : Prop :=
  ∀ D : BandData, D.Valid → ∀ᶠ x : ℝ in atTop,
    ∀ (S : Finset (D.Slot x)) (v : ℕ),
      ((Finset.univ.filter (fun z : PureLists D x S => pureListProduct D x S z = v)).card : ℝ) ≤
        (D.r₀.factorial : ℝ) ^ (D.last x + 1)

end Erdos821.S56Core
