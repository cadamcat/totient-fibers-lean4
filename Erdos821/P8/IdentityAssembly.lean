import Erdos821.P8.DensityBounds
import Erdos821.P8.DensitySieve

noncomputable section

namespace Erdos821.P8Core
open Blueprint

/-- Continuity is proved; the integral and ordinary lower-count tasks are the remaining leaves. -/
theorem densityIdentities_from_tasks (hc : ClassicalInputs) (hs : SieveInputs)
    (hintegral : DensityIntegralTask) (hlower : RoughDyadicDensityLowerTask) : DensityIdentities :=
  ⟨densityContinuityTask_proof, hintegral, density_sieve_upper_from_lower hc hs hlower⟩

end Erdos821.P8Core

