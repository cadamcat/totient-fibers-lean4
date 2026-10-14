import Erdos821.P6Off.Driver
import Erdos821.P6Off.ReindexBridge
import Erdos821.P6Off.SeparationBridge
import Erdos821.P6Off.TailBridge
import Erdos821.P6Off.AbsoluteBridge

namespace Erdos821.P6Off

/-- The literal off-diagonal estimate, with all derivative data and K₀ fixed
before the discrepancy exponent. -/
theorem offDiagonalShiftTask_proof : OffDiagonalShiftTask :=
  offDiagonalShiftTask_of_tasks offDiagonalReindexTask_proof pulledCutoffSeparationTask_proof
    absoluteDeterminantDyadTask_proof endpointSquareTask_proof

example : Erdos821.S56Core.OffDiagonalShiftTask := offDiagonalShiftTask_proof


end Erdos821.P6Off
