import Erdos821.P8Res.RoughResidueInterval
import Erdos821.P8.ProxyAssembly

noncomputable section

namespace Erdos821.P8Core
open Blueprint

example : RoughResidueIntervalTask = P8Res.RoughResidueIntervalTask := rfl

/-- The delivered residue sieve proof has exactly the fixed lead-side task type. -/
theorem roughResidueIntervalTask_proof : RoughResidueIntervalTask :=
  P8Res.RoughResidueIntervalTask_proof

/-- All discrepancy tasks are discharged from the given classical and sieve inputs. -/
theorem proxyDiscrepancy_proof (hc : ClassicalInputs) (hs : SieveInputs) :
    ProxyDiscrepancy :=
  proxyDiscrepancy_from_residue hc hs roughResidueIntervalTask_proof

/-- Only the assigned rough-cell density task remains in the density estimates. -/
theorem proxyDensities_from_cell (hc : ClassicalInputs) (hs : SieveInputs)
    (hcell : RoughCellDensityTask) : ProxyDensities :=
  proxyDensities_from_tasks hc hs roughResidueIntervalTask_proof hcell

/-- The full boundary now needs only the three assigned density tasks. -/
theorem proxyInputs_from_density_tasks (hc : ClassicalInputs) (hs : SieveInputs)
    (hcell : RoughCellDensityTask) (hintegral : DensityIntegralTask)
    (hlower : RoughDyadicDensityLowerTask) : ProxyInputs :=
  proxyInputs_from_tasks hc hs roughResidueIntervalTask_proof hcell hintegral hlower

end Erdos821.P8Core

