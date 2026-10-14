import Erdos821.S56.TypeIISplitAssembly
import Erdos821.S56.BlueprintDeterminant
import Erdos821.P6Split.Basic

namespace Erdos821.S56Core

theorem slot_coefficient_split : SlotCoefficientSplitTask := by
  change Erdos821.P6Split.SlotCoefficientSplitTask
  exact Erdos821.P6Split.SlotCoefficientSplitTask_proof

end Erdos821.S56Core

namespace Erdos821.Blueprint

/-- Section 5 Type II estimate, with shifted cancellation as its input. -/
theorem typeII_estimate_proof (hc : ClassicalInputs) (hshift : ShiftEstimate) :
    TypeIIEstimate :=
  S56Core.typeII_of_slot_split hc hshift S56Core.slot_coefficient_split

example : Erdos821.Blueprint.typeII_estimate_statement := @typeII_estimate_proof

end Erdos821.Blueprint
