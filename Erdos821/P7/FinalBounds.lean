import Erdos821.P7.Bounds
import Erdos821.P7.Geometry
import Erdos821.P7Free.Proof

namespace Erdos821.Blueprint

/-- Exact closure of the frozen candidate bounds statement. -/
theorem candidate_bounds_proof : Erdos821.Blueprint.candidate_bounds_statement :=
  Erdos821.P7Core.candidate_bounds_of_final_helpers
    Erdos821.P7Free.FreeWindowBoundsTask_proof

example : Erdos821.Blueprint.candidate_bounds_statement := @candidate_bounds_proof

end Erdos821.Blueprint

