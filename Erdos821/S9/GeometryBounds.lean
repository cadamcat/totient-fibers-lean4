import Erdos821.S9.AssignmentMoments

noncomputable section
open Filter
namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic Erdos821.P9Core

theorem geometry_assignment_bounds_eventually
    (C : CandidateData) (δ : ℝ) (hC : C.Geometry δ) :
    ∀ᶠ x : ℝ in atTop,
      (∀ g, 0 < mass (C.bands.groups x) g) ∧
      ∀ (jstar : ℕ) (m : MicroAssignments C x jstar)
        (marks : GlobalMarkChoices (C.bands.groups x)),
        (assignmentModulus C x jstar m marks : ℝ) ≤ x ^ (1 / 20 : ℝ) := by
  rcases hC.1 with ⟨_, _, _, _, _, _, _, _, cmin, cmax, _, _, hvalid⟩
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  have hpow : Tendsto (fun x : ℝ => L x ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hL
  filter_upwards [hvalid, eventually_gt_atTop (1 : ℝ),
    hL.eventually (eventually_ge_atTop (1 : ℝ)),
    hpow.eventually (eventually_ge_atTop (2000 * C.bands.geometry.C₀))]
    with x hv hx hxL hxpow
  refine ⟨?_, ?_⟩
  · intro g
    exact C.bands.geometry.positive.2.2.1.trans_le (hv.1.2.2.1 g).1
  · intro jstar m marks
    exact assignmentModulus_le_x_one_twentieth C δ x jstar hC hv.1 hx hxL hxpow m marks

end Erdos821.S56Core

