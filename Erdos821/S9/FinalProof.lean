import Erdos821.S9.ConditionalAssembly
import Erdos821.S9Div.DivisorCompensation
import Erdos821.S9Mask.MaskHarmonicP
import Erdos821.S9Norm.Normalization
import Erdos821.S9Budget.Proof
import Erdos821.P9.AssignmentSiftedBridge

namespace Erdos821.Blueprint

theorem balanced_rough_bound_proof
    (hc : ClassicalInputs) (hs : SieveInputs) (δ : ℝ) (C : CandidateData)
    (hC : C.Geometry δ) (hb : C.Bounds δ) : BalancedRoughBound C :=
  Erdos821.S56Core.balanced_rough_bound_of_tasks
    Erdos821.S9Div.divisorCompensationTask_proof
    Erdos821.S56Core.MaskHarmonicPTask_proof
    Erdos821.S9Budget.pairSieveBudgetTask_proof
    Erdos821.S56Core.AssignmentSiftedBridgeTask_proof
    Erdos821.S9Norm.BalancedNormalizationTask_proof
    hc hs δ C hC hb

example : Erdos821.Blueprint.balanced_rough_bound_statement := @balanced_rough_bound_proof

end Erdos821.Blueprint

