import Erdos821.P8Int.Integral
import Erdos821.P8.DensityTasks

noncomputable section

namespace Erdos821.P8Core

example : DensityIntegralTask = P8Int.DensityIntegralTask := rfl

/-- The accepted minimum-coordinate integral proves the exact fixed density task. -/
theorem densityIntegralTask_proof : DensityIntegralTask :=
  P8Int.DensityIntegralTask_proof

end Erdos821.P8Core

