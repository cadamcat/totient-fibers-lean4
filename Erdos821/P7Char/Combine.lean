import Erdos821.P7Char.Main

noncomputable section

namespace Erdos821.P7Char

open Erdos821.Blueprint

theorem candidate_typeI_via_nonprincipal (hc : ClassicalInputs) (δ : ℝ) (C : CandidateData)
    (hC : C.Geometry δ) (hb : C.Bounds δ) : C.TypeI :=
  Erdos821.P7B.candidate_typeI_of_nonprincipal_bounds hc C δ hb
    (nonprincipalTypeITask_proof hc δ C hC hb)

example : Erdos821.Blueprint.candidate_typeI_statement := @candidate_typeI_via_nonprincipal

end Erdos821.P7Char
