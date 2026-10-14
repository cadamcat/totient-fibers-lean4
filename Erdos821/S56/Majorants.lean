import Erdos821.S56.MajorantsTask
import Erdos821.P6Maj.Basic

namespace Erdos821.S56Core

theorem dyadic_majorants : DyadicMajorantsTask :=
  Erdos821.P6Maj.DyadicMajorantsTask_proof

example : DyadicMajorantsTask = Erdos821.P6Maj.DyadicMajorantsTask := rfl


end Erdos821.S56Core
