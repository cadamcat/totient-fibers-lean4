import Erdos821.P8.IntegralTask
import Erdos821.P8Low.Proof
import Erdos821.P8.ResidueAssembly

noncomputable section

namespace Erdos821.P8Core
open Blueprint

example : DensityIntegralTask = P8Low.DensityIntegralIdentity := rfl
example : RoughDyadicDensityLowerTask = P8Low.RoughDyadicDensityLowerTask := rfl

/-- Least-prime-factor induction uses the same density integral identity as the package. -/
theorem roughDyadicDensityLowerTask_proof : RoughDyadicDensityLowerTask :=
  P8Low.roughDyadicDensityLowerTask_of_densityIntegralIdentity densityIntegralTask_proof

/-- Continuity, the integral identity and the density sieve upper bound are discharged. -/
theorem densityIdentities_proof (hc : ClassicalInputs) (hs : SieveInputs) :
    DensityIdentities :=
  densityIdentities_from_tasks hc hs densityIntegralTask_proof roughDyadicDensityLowerTask_proof

/-- The sole remaining analytic task in the full proxy boundary is rough-cell density. -/
theorem proxyInputs_from_cell (hc : ClassicalInputs) (hs : SieveInputs)
    (hcell : RoughCellDensityTask) : ProxyInputs :=
  proxyInputs_from_density_tasks hc hs hcell densityIntegralTask_proof
    roughDyadicDensityLowerTask_proof

end Erdos821.P8Core

