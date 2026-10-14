import Erdos821.S56.TypeIIAssembly
import Erdos821.P6Off.PreCauchyProof

namespace Erdos821.S56Core
open Erdos821.Blueprint

/-- The pre-Cauchy reconstruction is now discharged. The only remaining
input is the exact finite slot coefficient split. -/
theorem typeII_of_slot_split (hc : ClassicalInputs) (hshift : ShiftEstimate)
    (hSplit : SlotCoefficientSplitTask) : TypeIIEstimate :=
  typeII_of_two_tasks hc hshift hSplit PreCauchyApproximationTask_proof

example (hSplit : SlotCoefficientSplitTask) : Erdos821.Blueprint.typeII_estimate_statement :=
  fun hc hshift => typeII_of_slot_split hc hshift hSplit

end Erdos821.S56Core
