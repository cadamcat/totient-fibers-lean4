import Erdos821.P7.ConditionalBounds
import Erdos821.P7Prefix.PrefixHarmonicTask
import Erdos821.P7HQ.HarmonicQLower
import Erdos821.P7Place.CandidatePlacement

noncomputable section

namespace Erdos821.P7Core

/-- The prefix, Q lower and placement inputs are proved. The final local
free-window estimate remains an explicit input. -/
theorem candidate_bounds_of_final_helpers
    (hwindow : FreeWindowBoundsTask) :
    Erdos821.Blueprint.candidate_bounds_statement :=
  candidate_bounds_of_pending_helpers hwindow
    Erdos821.P7Place.CandidatePlacementTask_proof
    Erdos821.P7Prefix.PrefixHarmonicTask_proof
    Erdos821.P7Hq.harmonicQLowerTask_proof

example (hwindow : FreeWindowBoundsTask) :
    Erdos821.Blueprint.candidate_bounds_statement :=
  candidate_bounds_of_final_helpers hwindow

end Erdos821.P7Core

