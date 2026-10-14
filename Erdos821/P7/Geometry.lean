import Erdos821.P7.BandGeometryTask
import Erdos821.P7Band.Proof

namespace Erdos821.Blueprint

/-- Exact closure of the frozen P7 geometry statement using the explicit
prime-group construction and the early candidate parameters. -/
theorem candidate_geometry_proof : Erdos821.Blueprint.candidate_geometry_statement :=
  Erdos821.P7Core.candidateGeometryTask_closes Erdos821.P7Core.BandGeometryTask_proof

example : Erdos821.Blueprint.candidate_geometry_statement := @candidate_geometry_proof

end Erdos821.Blueprint

