import Erdos821.S10.BalancedAssembly
import Erdos821.S10.ConditionalAssembly
import Erdos821.S10Sharp.TaskProof
import Erdos821.S10Bfac.Proof
import Erdos821.S10Cover.CompositeCoverage
import Erdos821.S10Brough.BalancedWindowRough
import Erdos821.S10Prime.Proof
import Erdos821.P10.UnbalancedMesh

noncomputable section
namespace Erdos821.P7Core
open Erdos821.Blueprint

/-- All but the unbalanced mesh task are supplied by concrete proofs. -/
theorem prime_extraction_of_remaining_tasks
    (hMesh : UnbalancedMeshTask) : Erdos821.Blueprint.prime_extraction_statement :=
  prime_extraction_of_tasks S10Sharp.SharpPresieveTask_proof hMesh
    S10Cover.CompositeCoverageTask_proof
    (balanced_composite_of_window_tasks S10Bfac.BalancedFactorCoverageTask_proof
      S10Brough.BalancedWindowRoughTask_proof BalancedWindowPrimeTask_proof)

example (hMesh : UnbalancedMeshTask) : Erdos821.Blueprint.prime_extraction_statement :=
  prime_extraction_of_remaining_tasks hMesh

end Erdos821.P7Core

namespace Erdos821.Blueprint

/-- Prime extraction with all six helper tasks supplied by concrete proofs. -/
theorem prime_extraction_proof : Erdos821.Blueprint.prime_extraction_statement :=
  P7Core.prime_extraction_of_remaining_tasks P7Core.UnbalancedMeshTask_proof

example : Erdos821.Blueprint.prime_extraction_statement := @prime_extraction_proof

end Erdos821.Blueprint
