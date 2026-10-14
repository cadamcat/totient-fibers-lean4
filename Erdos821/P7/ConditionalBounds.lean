import Erdos821.P7.MassComparison
import Erdos821.P7.HarmonicQLowerTask
import Erdos821.P7.BoundsAssembly
import Erdos821.P7Win.Proof

noncomputable section
open Filter

namespace Erdos821.P7Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

theorem polynomial_lower_of_comparison (x ell Q P m c CQ : ℝ)
    (hx : 0 < x) (hell : 0 < ell) (hc : 0 < c)
    (hconstant : 1 / ell ≤ c) (hQ : ell ^ (-CQ) ≤ Q) (hP : 1 ≤ P)
    (hm : c * (x / ell) * Q * P ≤ m) :
    x * ell ^ (-(CQ + 2)) ≤ m := by
  have hX : 0 ≤ x / ell := by positivity
  have hQ0 : 0 ≤ Q := (Real.rpow_pos_of_pos hell _).le.trans hQ
  have heq : x * ell ^ (-(CQ + 2)) = (1 / ell) * (x / ell) * ell ^ (-CQ) := by
    rw [show -(CQ + 2) = -CQ + (-1) + (-1) by ring,
      Real.rpow_add hell, Real.rpow_add hell, Real.rpow_neg_one]
    ring
  rw [heq]
  calc
    _ ≤ c * (x / ell) * ell ^ (-CQ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconstant hX) (by positivity)
    _ ≤ c * (x / ell) * Q :=
      mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = (c * (x / ell) * Q) * 1 := by ring
    _ ≤ c * (x / ell) * Q * P :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    _ ≤ m := hm

theorem candidateMassTask_of_helpers
    (hwindow : FreeWindowBoundsTask) (hprime : PrimeWindowHarmonicTask)
    (hplace : CandidatePlacementTask) (hprefix : PrefixHarmonicTask)
    (hqlower : HarmonicQLowerTask) : CandidateMassTask := by
  intro hc δ C hC
  obtain ⟨cmin, cmax, hmin, hmax, hcomp⟩ :=
    candidate_mass_comparison_of_tasks hwindow hprime hplace hprefix hc δ C hC
  obtain ⟨CQ, _, hQ⟩ := hqlower hc C.bands hC.1
  refine ⟨CQ + 2, cmin, cmax, hmin, hmax, ?_⟩
  intro jstar hj
  filter_upwards [hcomp jstar hj, hQ jstar, geometry_harmonicP_ge_one C δ hC,
    eventually_gt_atTop 0,
    Erdos821.S56Core.tendsto_L.eventually (eventually_ge_atTop (max 1 (1 / cmin)))]
    with x hm hQx hPx hx hL
  have hLpos : 0 < L x := zero_lt_one.trans_le ((le_max_left _ _).trans hL)
  have hcL : 1 / L x ≤ cmin := by
    apply (div_le_iff₀ hLpos).mpr
    have h := (div_le_iff₀ hmin).mp ((le_max_right _ _).trans hL)
    simpa only [mul_comm] using h
  exact ⟨polynomial_lower_of_comparison x (L x) (C.bands.harmonicQ x jstar)
    (C.bands.harmonicP x) (C.mass x jstar) cmin CQ hx hLpos hmin hcL hQx hPx hm.1,
    hm.1, hm.2⟩

theorem candidate_bounds_of_helpers
    (hwindow : FreeWindowBoundsTask) (hprime : PrimeWindowHarmonicTask)
    (hplace : CandidatePlacementTask) (hprefix : PrefixHarmonicTask)
    (hqlower : HarmonicQLowerTask) :
    Erdos821.Blueprint.candidate_bounds_statement :=
  candidate_bounds_of_massTask
    (candidateMassTask_of_helpers hwindow hprime hplace hprefix hqlower)

example (hwindow : FreeWindowBoundsTask) (hprime : PrimeWindowHarmonicTask)
    (hplace : CandidatePlacementTask) (hprefix : PrefixHarmonicTask)
    (hqlower : HarmonicQLowerTask) : Erdos821.Blueprint.candidate_bounds_statement :=
  candidate_bounds_of_helpers hwindow hprime hplace hprefix hqlower

theorem candidate_bounds_of_pending_helpers
    (hwindow : FreeWindowBoundsTask) (hplace : CandidatePlacementTask)
    (hprefix : PrefixHarmonicTask) (hqlower : HarmonicQLowerTask) :
    Erdos821.Blueprint.candidate_bounds_statement :=
  candidate_bounds_of_helpers hwindow PrimeWindowHarmonicTask_proof hplace hprefix hqlower

end Erdos821.P7Core

