import Erdos821.P8.ActualCancellation
import Erdos821.P8.RoughProxyDensity
import Erdos821.P8.IdentityAssembly

noncomputable section

namespace Erdos821.P8Core
open Blueprint

/-- The exact proxy-input constructor reduced to the four independently assigned analytic tasks. -/
theorem proxyInputs_from_tasks (hc : ClassicalInputs) (hs : SieveInputs)
    (hresidue : RoughResidueIntervalTask) (hcell : RoughCellDensityTask)
    (hintegral : DensityIntegralTask) (hlower : RoughDyadicDensityLowerTask) : ProxyInputs :=
  { discrepancy := proxyDiscrepancy_from_residue hc hs hresidue
    densities := proxyDensities_from_tasks hc hs hresidue hcell
    identities := densityIdentities_from_tasks hc hs hintegral hlower
    products := sieveProducts_proof }

end Erdos821.P8Core

