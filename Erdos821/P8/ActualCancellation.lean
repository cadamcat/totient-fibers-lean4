import Erdos821.P8Np.ActualTestNonprincipal
import Erdos821.P8.DiscrepancyAssembly

noncomputable section

namespace Erdos821.P8Core
open Blueprint

example : ActualTestNonprincipalTask = P8Np.ActualTestNonprincipalTask := rfl

/-- Bridge the delivered cancellation task to the lead's fixed task definition. -/
theorem actualTestNonprincipalTask_proof : ActualTestNonprincipalTask :=
  P8Np.ActualTestNonprincipalTask_proof

/-- Actual-test cancellation is discharged; only the residue sieve task remains. -/
theorem proxyDiscrepancy_from_residue (hc : ClassicalInputs) (hs : SieveInputs)
    (hresidue : RoughResidueIntervalTask) : ProxyDiscrepancy :=
  proxyDiscrepancy_from_tasks hc hs hresidue actualTestNonprincipalTask_proof

end Erdos821.P8Core

