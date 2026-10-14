import Erdos821.P8Grid.Cell
import Erdos821.P8.IntegralAssembly

noncomputable section

namespace Erdos821.P8Core
open Blueprint

/-- Both proxy density estimates follow from the given classical and sieve inputs. -/
theorem proxyDensities_proof (hc : ClassicalInputs) (hs : SieveInputs) :
    ProxyDensities :=
  proxyDensities_from_cell hc hs roughCellDensityTask_proof

end Erdos821.P8Core

namespace Erdos821.Blueprint

/-- The full proxy package is independent of Type II. -/
theorem proxy_inputs_proof (hc : ClassicalInputs) (hs : SieveInputs) : ProxyInputs :=
  P8Core.proxyInputs_from_cell hc hs P8Core.roughCellDensityTask_proof

example : Erdos821.Blueprint.proxy_inputs_statement := @proxy_inputs_proof

end Erdos821.Blueprint

